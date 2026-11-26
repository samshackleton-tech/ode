#!/usr/bin/env pypy3
"""Push-button automated pre-registered cold-room experiment harness for Ode.

Runs a declarative bank of tasks across frontier models and target architectures
(x86-64 and AArch64), automatically:
  1. Verifying a clean git tree and pinging every model API schema (1-token preflight).
  2. Writing and (optionally) committing `paper/EXPERIMENTS/prereg-<run-id>.md`
     with full 64-hex BLAKE3 hashes BEFORE any task API call begins.
  3. Executing all `(task x model x target)` cells concurrently in isolated sandboxes
     with a cumulative USD cost circuit breaker.
  4. On every passing cell, running `ode audit`, independent dual verification with
     `proof-core/verify2.py`, and real-silicon native hardware tests.
  5. Emitting `paper/EXPERIMENTS/results-<run-id>.json` and `.md` with an automatic
     before/after delta table against an optional `--baseline` results JSON.

No hostnames, IP addresses, or private paths are ever written into published reports.
"""
import argparse
import concurrent.futures
import datetime
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import urllib.error
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
EXP_DIR = ROOT / "paper" / "EXPERIMENTS"
TASKS_DIR = EXP_DIR / "tasks"
QUICKSTART_PATH = ROOT / "docs" / "QUICKSTART.md"
ODE_TOOL = ROOT / "lang" / "ode_tool.py"
VERIFY2 = ROOT / "proof-core" / "verify2.py"
ODEVERIFY = ROOT / "proof-core" / ".lake" / "build" / "bin" / "odeverify"

sys.path[:0] = [str(ROOT / "lang"), str(ROOT / "proof-core"), str(ROOT / "kcheck")]


SYSTEM_PROMPT = """\
You are a systems programmer writing verified native machine code in Ode.
You have NEVER seen an implementation of this task before. You are given:
1. The complete Ode Quickstart (`docs/QUICKSTART.md`).
2. The complete target instruction table (`core/x86.tab` or `arm64/arm64.tab`).
3. The complete specification file, which already sits in the working directory
   alongside your `.ode` file.

Your goal is to write ONE complete, self-contained `.ode` file that imports the
specification file and implements the requested entry function for the requested
target architecture so that `ode pack` and `ode audit` return `shown` against the
exact canonical contract header in the task prompt.

Rules:
- Keep the exact exported function signature and contract clauses given in the task
  prompt (so its canonical contract ID matches the expected 52-character BLAKE3 ID).
- You may define private helper functions in the same file (callees before callers)
  using Ode's newline-separated custom-calling syntax (one clause per line, no
  semicolons), e.g.:
    for x86_64 calling {
        in a = r10, b = r11
        out = r9
        preserves rdi, rsi, rbx, rbp, r12, r13, r14, r15
    } { ... }
- Output the complete `.ode` source file inside a single fenced code block
  (` ```ode ... ``` `).
- Do NOT modify the specification file; reference its definitions through the
  `use` alias shown in the task prompt.
- If the compiler, prover, or verifier reports an error, diagnose it and return a
  complete updated `.ode` file in a single ` ```ode ... ``` ` block.\
"""


def utc_now() -> str:
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def blake3_hex(path: Path) -> str:
    r = subprocess.run(["b3sum", "--no-names", str(path)], capture_output=True, text=True, check=True)
    return r.stdout.strip().split()[0]


def git_head() -> str:
    return subprocess.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"],
                          capture_output=True, text=True, check=True).stdout.strip()


def git_dirty() -> str:
    return subprocess.run(["git", "-C", str(ROOT), "status", "--porcelain"],
                          capture_output=True, text=True, check=True).stdout.strip()


def load_openrouter_key() -> str:
    key = os.environ.get("OPENROUTER_API_KEY")
    if key:
        return key.strip()
    auth_path = Path.home() / ".pi" / "agent" / "auth.json"
    if auth_path.exists():
        with auth_path.open("r", encoding="utf-8") as f:
            data = json.load(f)
        ent = data.get("openrouter")
        if isinstance(ent, dict) and ent.get("key"):
            return str(ent["key"]).strip()
        if isinstance(ent, str) and ent:
            return ent.strip()
    raise RuntimeError("No OpenRouter API key found in OPENROUTER_API_KEY or ~/.pi/agent/auth.json")


def call_openrouter(model: str, messages: list[dict], api_key: str,
                    temperature: float = 0.2, max_tokens: int = 16000,
                    effort: str = "medium", timeout: int = 240,
                    run_title: str = "Ode Pre-Registered Suite") -> tuple[str, dict, float]:
    payload = {
        "model": model,
        "temperature": temperature,
        "max_tokens": max_tokens,
        "reasoning": {"effort": effort},
        "messages": messages,
    }
    last_err = None
    for attempt in range(3):
        req = urllib.request.Request(
            "https://openrouter.ai/api/v1/chat/completions",
            data=json.dumps(payload).encode("utf-8"),
            headers={
                "Authorization": f"Bearer {api_key}",
                "Content-Type": "application/json",
                "HTTP-Referer": "https://github.com/samshackleton-tech/ode",
                "X-Title": run_title,
            },
            method="POST",
        )
        t0 = time.monotonic()
        try:
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                data = json.loads(resp.read().decode("utf-8"))
            dt = time.monotonic() - t0
            ch = data["choices"][0]
            content = (ch["message"].get("content") or "").strip()
            usage = data.get("usage", {})
            usage["finish_reason"] = ch.get("finish_reason")
            return content, usage, dt
        except (urllib.error.HTTPError, urllib.error.URLError, TimeoutError, OSError) as exc:
            last_err = exc
            if isinstance(exc, urllib.error.HTTPError) and exc.code < 500 and exc.code != 429:
                body = exc.read().decode("utf-8", "replace")[:400]
                raise RuntimeError(f"HTTP {exc.code}: {body}") from exc
            time.sleep(2.0 * (attempt + 1))
    raise RuntimeError(f"OpenRouter request failed after 3 attempts: {last_err}") from last_err


def preflight_ping(models: list[str], api_key: str, effort: str) -> dict[str, dict]:
    """Send a tiny 1-word ping to every model in parallel to verify ID & schema before spending."""
    def _ping(m: str) -> tuple[str, dict]:
        content, usage, dt = call_openrouter(
            m, [{"role": "user", "content": "Reply with the single word OK."}],
            api_key, temperature=0.0, max_tokens=64, effort="low", timeout=60,
            run_title="Ode Suite Preflight",
        )
        return m, {"ok": True, "reply": content[:32], "cost_usd": float(usage.get("cost") or 0.0), "s": round(dt, 2)}

    out = {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=len(models)) as ex:
        futs = [ex.submit(_ping, m) for m in models]
        for fut in concurrent.futures.as_completed(futs):
            m, info = fut.result()
            out[m] = info
    return out


def extract_ode_source(reply: str, entry_fn: str) -> str:
    blocks = re.findall(r"```(?:ode)?[ \t]*\n(.*?)```", reply, flags=re.DOTALL)
    if blocks:
        for b in reversed(blocks):
            if f"fn {entry_fn}" in b:
                return b.strip() + "\n"
        return blocks[-1].strip() + "\n"
    return reply.strip() + "\n"


def classify_failure(stage: str, out: str, rc: int) -> str:
    low = out.lower()
    if rc == 124 or "timeout after" in low:
        return "prover_timeout"
    if "cannot decide: is " in low:
        return "arith_need_compare"
    if ("ode does not use semicolons" in low or "calling {" in low or "calling `" in low
            or "in `calling`" in low or "expected `=`" in low or "expected '='" in low
            or "unexpected `;`" in low or "unexpected ';'" in low or "calling" in low and "unexpected" in low):
        return "calling_syntax_error"
    if "no row in" in low and ".tab matches" in low:
        return "isa_table_error"
    if "return address (x30)" in low or "stack pointer (sp)" in low or "values kept out of the trace" in low:
        return "trace_refusal"
    if "a register a callee keeps" in low:
        return "kept_reg_refusal"
    if "contract_id_mismatch" in low or "expected contract" in low:
        return "contract_id_mismatch"
    if "need entail" in low or "need compare" in low or "need below" in low or "need know" in low:
        return "arith_need_entail"
    if "need spec" in low or "need held" in low:
        return "spec_need_open"
    if "place`" in low or "place {" in low or "at the place" in low or "does not drop" in low:
        return "place_error"
    if stage == "pack" and ("line " in low and (":" in low)):
        return "compile_or_parse_error"
    return "other"


def run_tool(cmd: list[str], cwd: Path, timeout: int = 120) -> tuple[int, str, float]:
    t0 = time.monotonic()
    try:
        r = subprocess.run(cmd, cwd=str(cwd), capture_output=True, text=True, timeout=timeout)
        return r.returncode, (r.stdout + "\n" + r.stderr).strip(), time.monotonic() - t0
    except subprocess.TimeoutExpired as e:
        out = e.stdout.decode("utf-8", "replace") if isinstance(e.stdout, bytes) else (e.stdout or "")
        err = e.stderr.decode("utf-8", "replace") if isinstance(e.stderr, bytes) else (e.stderr or "")
        return 124, f"TIMEOUT after {timeout}s\n{out}\n{err}".strip(), time.monotonic() - t0


def run_verify2_on_bundle(out_o: Path, out_p: Path, target: str) -> tuple[bool, str, float]:
    """Run independent second verifier `proof-core/verify2.py` on a packed `.o` + `.proof`."""
    import ode_audit
    import verify2
    t0 = time.monotonic()
    try:
        with tempfile.TemporaryDirectory(prefix="ode_v2_") as td:
            td_p = Path(td)
            st_p = td_p / "stmt.txt"
            pf_p = td_p / "proof.txt"
            dump = td_p / "dump.sh"
            with dump.open("w", encoding="utf-8") as f:
                f.write(f"#!/bin/sh\ncp \"$2\" {st_p}\ncp \"$3\" {pf_p}\necho shown\n")
            os.chmod(dump, 0o755)
            ode_audit.audit_binary(str(out_o), str(out_p), verify_bin=str(dump))
            tab = str(ROOT / ("arm64/arm64.tab" if target == "arm64" else "core/x86.tab"))
            n = verify2.verify_files(tab, str(st_p), str(pf_p))
            return True, f"shown ({n} functions, verify2)", time.monotonic() - t0
    except Exception as exc:
        return False, f"refused: {exc}", time.monotonic() - t0


def run_native_test(out_o: Path, task: dict, target: str, x86_exec_script: str | None) -> tuple[str, str]:
    """Execute the verified binary on real silicon matching `target`."""
    harness = ROOT / task["native_harness"]
    if not harness.exists():
        return "skipped", "no native harness configured"
    if target == "arm64":
        if platform.system() == "Darwin" and platform.machine() == "arm64":
            import struct
            import ode_audit
            raw = out_o.read_bytes()
            elf = ode_audit.parse_elf64(raw)
            text_bytes = bytearray(elf["by_name"][".text"][0]["body"])
            syms_by_idx = {s["index"]: s for s in elf["symbols"]}
            # Apply internal AArch64 branch/call relocations (R_AARCH64_JUMP26=282, R_AARCH64_CALL26=283)
            for rsec in elf["by_name"].get(".rela.text", []):
                rbody = rsec["body"]
                for off in range(0, len(rbody), 24):
                    r_offset, r_info, r_addend = struct.unpack_from("<QQq", rbody, off)
                    r_sym = r_info >> 32
                    r_type = r_info & 0xFFFFFFFF
                    if r_type in (282, 283):
                        target_off = syms_by_idx[r_sym]["value"] + r_addend
                        disp = (target_off - r_offset) >> 2
                        word = struct.unpack_from("<I", text_bytes, r_offset)[0]
                        word = (word & 0xFC000000) | (disp & 0x03FFFFFF)
                        struct.pack_into("<I", text_bytes, r_offset, word)
            sym_name = f"ode_{task['expected_contract_id']}"
            entry_off = None
            for s in elf["symbols"]:
                if s["name"] == sym_name:
                    entry_off = s["value"]
                    break
            if entry_off is None:
                return "fail", f"symbol {sym_name} not found in .o"
            with tempfile.TemporaryDirectory(prefix="ode_nat_arm64_") as td:
                td_p = Path(td)
                bin_p = td_p / "text.bin"
                exe_p = td_p / "run_arm64"
                bin_p.write_bytes(text_bytes)
                rc_c, out_c, _ = run_tool(["cc", "-O2", "-DNATIVE_JIT_BIN", str(harness), "-o", str(exe_p)], td_p, 30)
                if rc_c != 0:
                    return "fail", f"cc failed: {out_c[:200]}"
                rc_r, out_r, _ = run_tool([str(exe_p), str(bin_p), str(entry_off)], td_p, 30)
                if rc_r == 0 and "NATIVE_PASS" in out_r:
                    return "pass", out_r.splitlines()[-1].strip()
                return "fail", out_r[:200]
        return "skipped", f"local host is {platform.system()}/{platform.machine()}"
    if target == "x86_64":
        if platform.system() == "Linux" and platform.machine() == "x86_64":
            with tempfile.TemporaryDirectory(prefix="ode_nat_x86_") as td:
                td_p = Path(td)
                exe_p = td_p / "run_x86"
                rc_c, out_c, _ = run_tool(["cc", "-O2", str(harness), str(out_o), "-o", str(exe_p)], td_p, 30)
                if rc_c != 0:
                    return "fail", f"cc failed: {out_c[:200]}"
                rc_r, out_r, _ = run_tool([str(exe_p)], td_p, 30)
                if rc_r == 0 and "NATIVE_PASS" in out_r:
                    return "pass", out_r.splitlines()[-1].strip()
                return "fail", out_r[:200]
        if x86_exec_script:
            rc_r, out_r, _ = run_tool([x86_exec_script, str(out_o), str(harness)], out_o.parent, 60)
            if rc_r == 0 and "NATIVE_PASS" in out_r:
                return "pass", [l for l in out_r.splitlines() if "NATIVE_PASS" in l][-1].strip()
            return "fail", out_r[:200]
        return "skipped", "no x86_64 native runner configured"
    return "skipped", f"unknown target {target}"


def parse_audit_metrics(audit_out: str) -> dict:
    m = {}
    cov = re.search(r"COVERAGE:\s+.*?\((\d+) functions?.*?, (\d+) instructions?, (\d+) B", audit_out)
    if cov:
        m["functions"] = int(cov.group(1))
        m["instructions"] = int(cov.group(2))
        m["code_bytes"] = int(cov.group(3))
    cid = re.search(r"BLAKE3\(contract\):\s+([a-z2-7]{52})", audit_out)
    if cid:
        m["contract_id"] = cid.group(1)
    ver = re.search(r"VERDICT:\s+(\S+)", audit_out)
    if ver:
        m["verdict"] = ver.group(1)
    return m


def build_initial_user_prompt(task: dict, target: str) -> str:
    quickstart = QUICKSTART_PATH.read_text(encoding="utf-8")
    tab_rel = "arm64/arm64.tab" if target == "arm64" else "core/x86.tab"
    tab_text = (ROOT / tab_rel).read_text(encoding="utf-8")
    spec_text = (ROOT / task["spec_file"]).read_text(encoding="utf-8")
    return (
        f"## Task\n\n"
        f"{task['task_summary']} Target architecture: `{target}`.\n\n"
        f"Use this EXACT import and exported contract header for `{task['entry_fn']}` "
        f"(expected canonical contract ID: `{task['expected_contract_id']}`):\n\n"
        f"```ode\n{task['contract_header']}```\n\n"
        f"Return a single complete `.ode` file implementing `for {target} {{ ... }}` "
        f"(and any optional private `for {target} calling {{ ... }} {{ ... }}` helpers you choose to define).\n\n"
        f"---\n\n"
        f"## Complete Ode Quickstart (`docs/QUICKSTART.md`)\n\n{quickstart}\n\n"
        f"---\n\n"
        f"## Complete Target Instruction Table (`{tab_rel}`)\n\n```\n{tab_text}\n```\n\n"
        f"---\n\n"
        f"## Complete Specification (`{task['spec_basename']}`)\n\n```ode\n{spec_text}\n```\n"
    )


class BudgetGuard:
    def __init__(self, max_usd: float):
        self.max_usd = max_usd
        self.spent = 0.0
        self.lock = threading.Lock()

    def exceeded(self) -> bool:
        with self.lock:
            return self.spent >= self.max_usd

    def add(self, usd: float) -> float:
        with self.lock:
            self.spent += usd
            return self.spent


def slug(s: str) -> str:
    return re.sub(r"[^a-zA-Z0-9._-]+", "_", s).strip("_")


def parse_advise_metrics(advise_txt: str, target: str) -> dict:
    """Extract hot-loop static `cyc/B`, `cyc/iter`, `load_bytes`, and cross-CPU `cyc/B` from `ode advise --all-archs`."""
    default_arch = "apple_m" if target == "arm64" else "zen5"
    loops = []
    cur = None
    for line in advise_txt.splitlines():
        m_lp = re.search(
            r"loop\s+(\d+):.*pipeline sim ~([0-9.]+) cyc/iter \(([^,]+),\s*(\d+) fused(?:,\s*([0-9.]+) cyc/B across (\d+) load\(s\)/(\d+) B)?\)",
            line,
        )
        if m_lp:
            cur = {
                "loop_idx": int(m_lp.group(1)),
                "cycles_per_iter": float(m_lp.group(2)),
                "bottleneck": m_lp.group(3).strip(),
                "fused_pairs": int(m_lp.group(4)),
                "cyc_per_b": float(m_lp.group(5)) if m_lp.group(5) else None,
                "load_count": int(m_lp.group(6)) if m_lp.group(6) else 0,
                "load_bytes": int(m_lp.group(7)) if m_lp.group(7) else 0,
                "all_archs_cyc_per_b": {},
                "all_archs_cyc_per_iter": {},
                "lints": 0,
            }
            loops.append(cur)
            continue
        if cur is not None:
            if "hint [" in line:
                cur["lints"] += 1
            m_aa = re.match(r"^\s+(\w+)\s*:\s*~\s*([0-9.]+) cyc/iter(?:,\s*([0-9.]+) cyc/B)?", line)
            if m_aa:
                cur["all_archs_cyc_per_iter"][m_aa.group(1)] = float(m_aa.group(2))
                if m_aa.group(3):
                    cur["all_archs_cyc_per_b"][m_aa.group(1)] = float(m_aa.group(3))
    load_loops = [lp for lp in loops if lp["load_bytes"] > 0 and lp["cyc_per_b"] is not None]
    if not load_loops:
        return {"hot_loop": None, "primary_arch": default_arch, "cyc_per_b": None, "load_bytes": 0, "loops": loops}
    # Main hot loop for large buffers is the one loading the most bytes per iteration (tie-break: lowest cyc/B)
    hot = min(load_loops, key=lambda lp: (-lp["load_bytes"], lp["cyc_per_b"]))
    return {
        "hot_loop": hot["loop_idx"],
        "primary_arch": default_arch,
        "cyc_per_b": round(hot["cyc_per_b"], 4),
        "cycles_per_iter": round(hot["cycles_per_iter"], 3),
        "load_bytes": hot["load_bytes"],
        "load_count": hot["load_count"],
        "bottleneck": hot["bottleneck"],
        "lints": hot["lints"],
        "all_archs_cyc_per_b": hot["all_archs_cyc_per_b"],
        "loop_count": len(loops),
    }


def run_static_advise(cand: Path, entry_fn: str, target: str, work: Path) -> tuple[str, dict]:
    cmd = [sys.executable, str(ODE_TOOL), "advise", str(cand), "--fn", entry_fn, "--target", target, "--all-archs"]
    rc, out, _ = run_tool(cmd, work, timeout=30)
    if rc != 0:
        return f"(ode advise exited {rc}: {out[:300]})", {"cyc_per_b": None}
    return out, parse_advise_metrics(out, target)


def run_cell(task: dict, model: str, target: str, args, api_key: str,
             budget: BudgetGuard, out_dir: Path, prover_sem: threading.BoundedSemaphore,
             arm: str | None = None) -> dict:
    arm_tag = f"__{arm}" if arm else ""
    cell_id = f"{task['id']}__{slug(model.split('/')[-1])}__{target}{arm_tag}"
    print(f"[start] {cell_id}", flush=True)
    t_cell_start = time.monotonic()
    consec_trunc = 0
    messages = [
        {"role": "system", "content": SYSTEM_PROMPT},
        {"role": "user", "content": build_initial_user_prompt(task, target)},
    ]
    cell = {
        "cell_id": cell_id,
        "task": task["id"],
        "model": model,
        "target": target,
        "arm": arm,
        "expected_contract_id": task["expected_contract_id"],
        "started_utc": utc_now(),
        "strict_pass": False,
        "rounds_to_pass": None,
        "passing_rounds": 0,
        "total_cost_usd": 0.0,
        "total_api_s": 0.0,
        "total_tool_s": 0.0,
        "verify2_pass": None,
        "verify2_detail": None,
        "verify2_s": None,
        "native_status": "not_run",
        "native_detail": None,
        "initial_perf": None,
        "best_perf": None,
        "best_round": None,
        "final_metrics": {},
        "rounds": [],
    }
    opt_rounds_left = args.opt_rounds if arm else 0
    best_cyc_per_b = None

    spec_src = ROOT / task["spec_file"]
    last_ode = ""
    with tempfile.TemporaryDirectory(prefix=f"ode_cell_{cell_id}_") as td:
        work = Path(td)
        shutil.copy2(spec_src, work / task["spec_basename"])
        cand = work / f"{task['id']}.ode"
        out_o = work / "out.o"
        out_p = work / "out.proof"

        for rnum in range(1, args.max_rounds + 1):
            if budget.exceeded():
                cell["stopped_reason"] = f"budget_cap_{args.max_usd}"
                print(f"[stop]  {cell_id}: cumulative budget cap ${args.max_usd:.2f} reached", flush=True)
                break
            if args.cell_timeout > 0 and (time.monotonic() - t_cell_start) >= args.cell_timeout:
                cell["stopped_reason"] = f"cell_timeout_{args.cell_timeout}s"
                print(f"[stop]  {cell_id}: cell wall-clock cap {args.cell_timeout}s reached before R{rnum}", flush=True)
                break
            try:
                reply, usage, api_s = call_openrouter(
                    model, messages, api_key,
                    temperature=args.temperature, max_tokens=args.max_tokens,
                    effort=args.effort, timeout=args.api_timeout,
                    run_title=f"Ode Suite {args.run_id}",
                )
            except Exception as exc:
                cell["rounds"].append({"round": rnum, "stage": "api_error", "category": "api_error",
                                       "error": str(exc)[:400]})
                print(f"[err]   {cell_id} R{rnum}: API error: {exc}", flush=True)
                break

            cost = float(usage.get("cost") or 0.0)
            cell["total_cost_usd"] += cost
            cell["total_api_s"] += api_s
            total_spent = budget.add(cost)

            # A reply cut off by the token limit before it holds the function is no candidate: say so to
            # the model and count it apart from compile errors (no tool is run on it).
            if usage.get("finish_reason") == "length" and f"fn {task['entry_fn']}" not in reply:
                consec_trunc += 1
                cell["rounds"].append({
                    "round": rnum, "api_s": round(api_s, 2), "tool_s": 0.0, "cost_usd": round(cost, 4),
                    "prompt_tokens": usage.get("prompt_tokens"),
                    "completion_tokens": usage.get("completion_tokens"),
                    "finish_reason": "length", "source_lines": 0,
                    "stage": "no_candidate", "category": "output_token_limit",
                })
                print(f"[fail]  {cell_id} R{rnum} (output_token_limit #{consec_trunc}, ${cost:.2f}, suite=${total_spent:.2f})", flush=True)
                if args.max_truncations > 0 and consec_trunc >= args.max_truncations:
                    cell["stopped_reason"] = f"consecutive_truncations_{consec_trunc}"
                    print(f"[stop]  {cell_id}: {consec_trunc} consecutive output_token_limit replies", flush=True)
                    break
                messages.append({"role": "assistant", "content": reply or "(no visible output)"})
                messages.append({"role": "user", "content": (
                    f"Round {rnum}: your reply reached the output limit of {args.max_tokens} tokens before it "
                    f"contained the `.ode` file, so nothing was compiled. Reason more briefly and return the "
                    f"complete `.ode` file in a single ```ode ... ``` block.")})
                continue

            consec_trunc = 0
            ode_src = extract_ode_source(reply, task["entry_fn"])
            last_ode = ode_src
            cand.write_text(ode_src, encoding="utf-8")
            for p in (out_o, out_p):
                if p.exists():
                    p.unlink()

            # Step A: `ode pack` (bounded local prover concurrency so parallel API cells do not starve each other)
            pack_cmd = [
                sys.executable, str(ODE_TOOL), "pack", str(cand),
                "--fn", task["entry_fn"], "--target", target,
                "--out", str(out_o), "--proof", str(out_p),
            ]
            with prover_sem:
                rc_p, out_p_txt, dt_p = run_tool(pack_cmd, work, timeout=args.tool_timeout)
            cell["total_tool_s"] += dt_p

            rec = {
                "round": rnum,
                "api_s": round(api_s, 2),
                "tool_s": round(dt_p, 2),
                "cost_usd": round(cost, 4),
                "prompt_tokens": usage.get("prompt_tokens"),
                "completion_tokens": usage.get("completion_tokens"),
                "finish_reason": usage.get("finish_reason"),
                "source_lines": len(ode_src.splitlines()),
                "pack_rc": rc_p,
            }

            if rc_p == 0 and out_o.exists() and out_p.exists():
                # Step B: independent `ode audit --expect-contract`
                audit_cmd = [
                    sys.executable, str(ODE_TOOL), "audit", str(out_o),
                    "--proof", str(out_p),
                    "--expect-contract", task["expected_contract_id"],
                ]
                with prover_sem:
                    rc_a, out_a_txt, dt_a = run_tool(audit_cmd, work, timeout=args.tool_timeout)
                cell["total_tool_s"] += dt_a
                rec["audit_rc"] = rc_a
                rec["audit_s"] = round(dt_a, 3)
                if rc_a == 0 and "VERDICT:           shown" in out_a_txt:
                    metrics = parse_audit_metrics(out_a_txt)
                    metrics["audit_s"] = round(dt_a, 3)
                    metrics["pack_s"] = round(dt_p, 3)
                    metrics["proof_bytes"] = out_p.stat().st_size
                    rec["stage"] = "passed"
                    rec["category"] = "passed"

                    # Step C: independent pure-Python second verifier (`verify2.py`)
                    v2_ok, v2_msg, v2_s = run_verify2_on_bundle(out_o, out_p, target)
                    # Step D: real-silicon native tests + optional static `ode advise --all-archs`
                    nat_st, nat_det = run_native_test(out_o, task, target, args.x86_exec_script)
                    adv_txt, perf = ("", None)
                    if arm is not None:
                        adv_txt, perf = run_static_advise(cand, task["entry_fn"], target, work)
                        rec["perf"] = perf

                    cpb = perf.get("cyc_per_b") if perf else None
                    first_pass = not cell["strict_pass"]
                    improved = first_pass or (
                        cpb is not None and (best_cyc_per_b is None or cpb < best_cyc_per_b - 1e-6)
                    )
                    if first_pass:
                        cell["strict_pass"] = True
                        cell["rounds_to_pass"] = rnum
                        cell["initial_perf"] = perf
                        if arm is not None:
                            shutil.copy2(cand, out_dir / f"{cell_id}.r{rnum}.ode")
                            shutil.copy2(out_o, out_dir / f"{cell_id}.r{rnum}.o")
                    cell["passing_rounds"] += 1
                    if improved:
                        best_cyc_per_b = cpb
                        cell["best_perf"] = perf
                        cell["best_round"] = rnum
                        cell["final_metrics"] = metrics
                        cell["verify2_pass"] = v2_ok
                        cell["verify2_detail"] = v2_msg
                        cell["verify2_s"] = round(v2_s, 3)
                        cell["native_status"] = nat_st
                        cell["native_detail"] = nat_det
                        shutil.copy2(cand, out_dir / f"{cell_id}.ode")
                        shutil.copy2(out_o, out_dir / f"{cell_id}.o")
                        shutil.copy2(out_p, out_dir / f"{cell_id}.proof")

                    cell["rounds"].append(rec)
                    perf_tag = f" hot={cpb:.2f}cyc/B({perf.get('load_bytes')}B/it)" if cpb is not None else ""
                    print(
                        f"[PASS]  {cell_id} R{rnum} (${cell['total_cost_usd']:.2f}, suite=${total_spent:.2f}) "
                        f"{metrics.get('functions')}fns {metrics.get('instructions')}insns "
                        f"{metrics.get('code_bytes')}B verify2={v2_ok} native={nat_st}{perf_tag}",
                        flush=True,
                    )
                    if arm is None or opt_rounds_left <= 0 or rnum >= args.max_rounds:
                        break
                    opt_rounds_left -= 1
                    messages.append({"role": "assistant", "content": reply})
                    if arm == "advised":
                        messages.append({
                            "role": "user",
                            "content": (
                                f"Round {rnum} PASSED verification (`shown`, {metrics.get('functions')} fn(s), "
                                f"{metrics.get('instructions')} instructions, {metrics.get('code_bytes')} B, "
                                f"verify2={v2_ok}, native={nat_st}).\n\n"
                                f"Here is the static `ode advise --all-archs` report on your verified code (no execution):\n"
                                f"```\n{adv_txt}\n```\n\n"
                                f"You have {opt_rounds_left + 1} optimization attempt(s) left (until round {args.max_rounds}). "
                                f"Use this static pipeline report (cycles/iter, `cyc/B`, bottlenecks, critical path, "
                                f"i-cache alignment, and lints) to reduce loop cycles per byte (`cyc/B`) further for large `n` "
                                f"while keeping `ode pack`, `ode audit`, and native tests passing. "
                                f"Return a complete updated `.ode` file in a single ```ode ... ``` block."
                            ),
                        })
                    else:
                        messages.append({
                            "role": "user",
                            "content": (
                                f"Round {rnum} PASSED verification (`shown`, {metrics.get('functions')} fn(s), "
                                f"{metrics.get('instructions')} instructions, {metrics.get('code_bytes')} B, "
                                f"verify2={v2_ok}, native={nat_st}).\n\n"
                                f"You have {opt_rounds_left + 1} optimization attempt(s) left (until round {args.max_rounds}). "
                                f"Try to make the hot loop significantly faster (lower cycles per byte for large `n`, e.g. `n = 4096`) "
                                f"while keeping `ode pack`, `ode audit`, and native tests passing. "
                                f"Return a complete updated `.ode` file in a single ```ode ... ``` block."
                            ),
                        })
                    continue
                else:
                    fb = out_a_txt
                    cat = classify_failure("audit", fb, rc_a)
                    rec["stage"] = "audit_failed"
                    rec["category"] = cat
                    rec["diagnostic_head"] = fb[:600]
            else:
                fb = out_p_txt
                cat = classify_failure("pack", fb, rc_p)
                rec["stage"] = "pack_failed"
                rec["category"] = cat
                rec["diagnostic_head"] = fb[:600]

            cell["rounds"].append(rec)
            print(f"[fail]  {cell_id} R{rnum} ({cat}, {dt_p:.1f}s, ${cost:.2f}, suite=${total_spent:.2f})", flush=True)

            # Truncate huge feedback cleanly while keeping start + end
            fb_send = fb if len(fb) <= 6000 else (fb[:4200] + "\n... [truncated] ...\n" + fb[-1500:])
            messages.append({"role": "assistant", "content": reply})
            messages.append({
                "role": "user",
                "content": (
                    f"Round {rnum} failed ({rec['stage']}, exit {rc_p if rec['stage']=='pack_failed' else rec.get('audit_rc')}).\n\n"
                    f"Tool output:\n```\n{fb_send}\n```\n\n"
                    f"Diagnose the root cause and return the complete updated `.ode` file in a single ```ode ... ``` block."
                ),
            })

        if not cell["strict_pass"] and last_ode:
            (out_dir / f"{cell_id}.last.ode").write_text(last_ode, encoding="utf-8")

    cell["finished_utc"] = utc_now()
    cell["total_cost_usd"] = round(cell["total_cost_usd"], 4)
    cell["total_api_s"] = round(cell["total_api_s"], 2)
    cell["total_tool_s"] = round(cell["total_tool_s"], 2)

    # Save verbatim per-cell log privately in out_dir
    with (out_dir / f"{cell_id}.json").open("w", encoding="utf-8") as f:
        json.dump(cell, f, indent=2)
    return cell


def write_prereg(run_id: str, tasks: list[dict], models: list[str], targets: list[str],
                 args, hashes: dict[str, str], commit_sha: str, started_utc: str,
                 arms: list[str | None] | None = None) -> Path:
    arms = arms or [None]
    path = EXP_DIR / f"prereg-{run_id}.md"
    lines = [
        f"# Pre-Registration: Cold-Room Suite `{run_id}`",
        "",
        f"Committed before any task API call begins.",
        "",
        "## Frozen Configuration",
        "",
        f"- **Run ID:** `{run_id}`",
        f"- **UTC timestamp:** `{started_utc}`",
        f"- **Repository commit (HEAD before pre-registration):** `{commit_sha}`",
        f"- **Tasks:** {', '.join('`' + t['id'] + '`' for t in tasks)}",
        f"- **Models ({len(models)}):** {', '.join(f'`{m}`' for m in models)}",
        f"- **Targets ({len(targets)}):** {', '.join(f'`{t}`' for t in targets)}",
        f"- **Experimental arms:** {', '.join('`' + (a or 'default') + '`' for a in arms)}" + (f" (`--opt-rounds {args.opt_rounds}` after first pass)" if any(arms) else ""),
        f"- **Total cells:** {len(tasks) * len(models) * len(targets) * len(arms)}",
        f"- **Budget cap:** max `{args.max_rounds}` rounds per cell, `{args.tool_timeout}s` tool timeout, "
        f"`{args.cell_timeout}s` wall-clock cap per cell, early stop after `{args.max_truncations}` consecutive "
        f"`output_token_limit` replies, `{args.prover_slots}` concurrent local prover slots, "
        f"temperature `{args.temperature}`, reasoning effort `{args.effort}`, max_tokens `{args.max_tokens}`, "
        f"cumulative suite cap `${args.max_usd:.2f}`.",
        "",
        "## Frozen Input BLAKE3-256 Hashes",
        "",
        "The table below lists the full 64-hex BLAKE3-256 hash of every frozen prompt input and verifier artifact.",
        "",
        "| Artifact | BLAKE3-256 (64 hex) |",
        "| --- | --- |",
    ]
    for k, h in sorted(hashes.items()):
        lines.append(f"| `{k}` | `{h}` |")
    lines += [
        "",
        "## Expected Canonical Contract IDs",
        "",
        "The table below lists each task's required 52-character base-32 contract identifier.",
        "",
        "| Task | Entry function | Expected contract ID |",
        "| --- | --- | --- |",
    ]
    for t in tasks:
        lines.append(f"| `{t['id']}` | `{t['entry_fn']}` | `{t['expected_contract_id']}` |")
    lines += [
        "",
        "## Strict Pass Criteria",
        "",
        "A cell counts as a **strict pass** if and only if, within the round limit and with no manual intervention:",
        "1. `ode pack` produces an ELF64 object file and `.proof` file matching the task's exact expected contract ID.",
        "2. `ode audit --expect-contract <ID>` returns `VERDICT: shown` with 100% executable coverage and 0 hooks.",
        "3. Secondary automated checks recorded on every passing cell: independent pure-Python second verifier (`proof-core/verify2.py`) and real-silicon native execution against the task harness.",
        "",
    ]
    path.write_text("\n".join(lines), encoding="utf-8")
    return path


def summarize_categories(cells: list[dict]) -> dict[str, int]:
    counts: dict[str, int] = {}
    for c in cells:
        for r in c["rounds"]:
            cat = r.get("category", "other")
            if cat != "passed":
                counts[cat] = counts.get(cat, 0) + 1
    return dict(sorted(counts.items(), key=lambda kv: (-kv[1], kv[0])))


def write_results(run_id: str, prereg_commit: str, tasks: list[dict], models: list[str],
                  targets: list[str], cells: list[dict], baseline_path: Path | None,
                  expected_total: int | None = None) -> tuple[Path, Path]:
    cells_sorted = sorted(cells, key=lambda c: (c["task"], c["model"], c["target"], c.get("arm") or ""))
    has_arms = any(c.get("arm") for c in cells_sorted)
    total_expected = expected_total if expected_total is not None else len(cells_sorted)
    in_progress = len(cells_sorted) < total_expected
    strict_passes = sum(1 for c in cells_sorted if c["strict_pass"])
    v2_passes = sum(1 for c in cells_sorted if c["verify2_pass"] is True)
    nat_passes = sum(1 for c in cells_sorted if c["native_status"] == "pass")
    total_cost = round(sum(c["total_cost_usd"] for c in cells_sorted), 4)
    total_rounds = sum(len(c["rounds"]) for c in cells_sorted)
    cats = summarize_categories(cells_sorted)

    summary = {
        "run_id": run_id,
        "prereg_commit": prereg_commit,
        "status": "in_progress" if in_progress else "complete",
        "completed_cells": len(cells_sorted),
        "finished_utc": utc_now(),
        "tasks": [t["id"] for t in tasks],
        "models": models,
        "targets": targets,
        "strict_passes": strict_passes,
        "total_cells": total_expected,
        "verify2_passes": v2_passes,
        "native_passes": nat_passes,
        "total_rounds": total_rounds,
        "total_cost_usd": total_cost,
        "failure_categories": cats,
        "cells": [
            {
                "task": c["task"],
                "model": c["model"],
                "target": c["target"],
                "arm": c.get("arm"),
                "strict_pass": c["strict_pass"],
                "rounds_used": len(c["rounds"]),
                "rounds_to_pass": c["rounds_to_pass"],
                "passing_rounds": c.get("passing_rounds", 1 if c["strict_pass"] else 0),
                "best_round": c.get("best_round"),
                "initial_perf": c.get("initial_perf"),
                "best_perf": c.get("best_perf"),
                "stopped_reason": c.get("stopped_reason"),
                "total_cost_usd": c["total_cost_usd"],
                "verify2_pass": c["verify2_pass"],
                "native_status": c["native_status"],
                "native_detail": c["native_detail"],
                "final_metrics": c["final_metrics"],
                "round_categories": [r.get("category") for r in c["rounds"]],
            }
            for c in cells_sorted
        ],
    }

    json_path = EXP_DIR / f"results-{run_id}.json"
    tmp_json = EXP_DIR / f".results-{run_id}.json.tmp"
    with tmp_json.open("w", encoding="utf-8") as f:
        json.dump(summary, f, indent=2)
    os.replace(tmp_json, json_path)

    status_tag = f" (in progress: {len(cells_sorted)}/{total_expected} cells finished)" if in_progress else ""
    md_lines = [
        f"# Results: Pre-Registered Cold-Room Suite `{run_id}`{status_tag}",
        "",
        f"- **Pre-registration commit:** `{prereg_commit}`",
        f"- **Updated (UTC):** `{summary['finished_utc']}`" if in_progress else f"- **Finished (UTC):** `{summary['finished_utc']}`",
        f"- **Strict pass rate:** **{strict_passes}/{len(cells_sorted)}** finished cells" + (f" ({total_expected} scheduled)" if in_progress else ""),
        f"- **Independent second verifier (`verify2.py`):** **{v2_passes}/{strict_passes}** passing cells dual-verified",
        f"- **Real-silicon native harness:** **{nat_passes}/{strict_passes}** passing cells executed and passed on matching hardware",
        f"- **Total rounds / API spend:** {total_rounds} rounds, **${total_cost:.2f}** USD",
        "",
        "## Cell-by-Cell Outcomes",
        "",
        "Each row reports one cold-room cell: verdict, rounds used, API cost, compiled code size, `verify2.py` status, and real-silicon test result.",
        "",
    ]
    if has_arms:
        md_lines += [
            "| Task | Model | Target | Arm | Verdict | Rounds | Initial -> Best `cyc/B` | Unroll (B/it) | Cost (USD) | `verify2.py` | Native CPU |",
            "| --- | --- | --- | --- | --- | ---: | --- | ---: | ---: | --- | --- |",
        ]
        for c in summary["cells"]:
            verdict = f"PASS (R{c['rounds_to_pass']}, best R{c['best_round']})" if c["strict_pass"] else f"FAIL ({c['round_categories'][-1] if c['round_categories'] else 'none'})"
            ip = (c.get("initial_perf") or {}).get("cyc_per_b")
            bp = (c.get("best_perf") or {}).get("cyc_per_b")
            lb = (c.get("best_perf") or {}).get("load_bytes")
            perf_s = f"{ip:.2f} -> **{bp:.2f}**" if (ip is not None and bp is not None) else "—"
            lb_s = f"{lb} B" if lb else "—"
            v2_s = "shown" if c["verify2_pass"] is True else ("refused" if c["verify2_pass"] is False else "—")
            nat_s = c["native_detail"] if c["native_status"] == "pass" else c["native_status"]
            md_lines.append(
                f"| `{c['task']}` | `{c['model']}` | `{c['target']}` | `{c.get('arm') or ''}` | {verdict} | {c['rounds_used']} | "
                f"{perf_s} | {lb_s} | ${c['total_cost_usd']:.2f} | {v2_s} | {nat_s} |"
            )
    else:
        md_lines += [
            "| Task | Model | Target | Verdict | Rounds | Cost (USD) | Code | `verify2.py` | Native CPU |",
            "| --- | --- | --- | --- | --- | --- | --- | --- | --- |",
        ]
        for c in summary["cells"]:
            verdict = f"PASS (R{c['rounds_to_pass']})" if c["strict_pass"] else f"FAIL ({c['round_categories'][-1] if c['round_categories'] else 'none'})"
            fm = c["final_metrics"]
            code_s = f"{fm.get('functions')} fns / {fm.get('instructions')} insns / {fm.get('code_bytes')} B" if c["strict_pass"] else "—"
            v2_s = "shown" if c["verify2_pass"] is True else ("refused" if c["verify2_pass"] is False else "—")
            nat_s = c["native_detail"] if c["native_status"] == "pass" else c["native_status"]
            md_lines.append(
                f"| `{c['task']}` | `{c['model']}` | `{c['target']}` | {verdict} | {c['rounds_used']} | "
                f"${c['total_cost_usd']:.2f} | {code_s} | {v2_s} | {nat_s} |"
            )

    md_lines += [
        "",
        "## Failing Round Breakdown",
        "",
        "Each row counts failing rounds across all cells by root-cause category.",
        "",
        "| Failure category | Failing rounds |",
        "| --- | --- |",
    ]
    if cats:
        for k, v in cats.items():
            md_lines.append(f"| `{k}` | {v} |")
    else:
        md_lines.append("| *(none)* | 0 |")

    if baseline_path and baseline_path.exists():
        with baseline_path.open("r", encoding="utf-8") as f:
            base = json.load(f)
        b_id = base.get("run_id", baseline_path.stem)
        # Totals are compared over the cells both runs have (same task, model and target), so that a run
        # with more tasks is not set against a run with fewer.
        b_all = {(c["task"], c["model"], c["target"]): c for c in base.get("cells", [])}
        both = [(b_all[k], c) for c in summary["cells"] for k in [(c["task"], c["model"], c["target"])] if k in b_all]
        def tot(cs):
            fc = {}
            for c in cs:
                for cat in c["round_categories"]:
                    if cat != "passed":
                        fc[cat] = fc.get(cat, 0) + 1
            return (sum(1 for c in cs if c["strict_pass"]), sum(c["rounds_used"] for c in cs),
                    round(sum(c["total_cost_usd"] for c in cs), 2), fc)
        bp, br, bc, bf = tot([b for b, _ in both])
        np_, nr, nc, nf = tot([c for _, c in both])
        md_lines += [
            "",
            f"## Before vs. After Comparison (`{b_id}` -> `{run_id}`)",
            "",
            f"The first table compares totals over the {len(both)} cells that both runs have (the same task, model and target); "
            "each cell was run once in each run, so a difference in one cell may be chance. "
            "The second table sets each such cell of the two runs side by side.",
            "",
            f"| Metric (over the {len(both)} shared cells) | `{b_id}` | `{run_id}` | Delta |",
            "| --- | --- | --- | --- |",
            f"| Strict passes | {bp}/{len(both)} | {np_}/{len(both)} | {np_ - bp:+d} |",
            f"| Total rounds | {br} | {nr} | {nr - br:+d} |",
            f"| Total API spend (USD) | ${bc:.2f} | ${nc:.2f} | ${nc - bc:+.2f} |",
        ]
        for ck in sorted(set(bf) | set(nf)):
            md_lines.append(f"| Failing rounds: `{ck}` | {bf.get(ck, 0)} | {nf.get(ck, 0)} | {nf.get(ck, 0) - bf.get(ck, 0):+d} |")

        b_map = {(c["task"], c["model"], c["target"]): c for c in base.get("cells", [])}
        md_lines += [
            "",
            f"| Task | Model | Target | `{b_id}` | `{run_id}` |",
            "| --- | --- | --- | --- | --- |",
        ]
        for c in summary["cells"]:
            key = (c["task"], c["model"], c["target"])
            bc = b_map.get(key)
            b_str = (f"PASS (R{bc['rounds_to_pass']}, ${bc['total_cost_usd']:.2f})" if bc["strict_pass"]
                     else f"FAIL (${bc['total_cost_usd']:.2f})") if bc else "—"
            n_str = (f"PASS (R{c['rounds_to_pass']}, ${c['total_cost_usd']:.2f})" if c["strict_pass"]
                     else f"FAIL (${c['total_cost_usd']:.2f})")
            md_lines.append(f"| `{c['task']}` | `{c['model']}` | `{c['target']}` | {b_str} | {n_str} |")

    md_path = EXP_DIR / f"results-{run_id}.md"
    tmp_md = EXP_DIR / f".results-{run_id}.md.tmp"
    tmp_md.write_text("\n".join(md_lines) + "\n", encoding="utf-8")
    os.replace(tmp_md, md_path)
    return json_path, md_path


def self_test_cli(targets: list[str]) -> None:
    """Verify `ode pack`, `ode audit`, and `verify2.py` CLI wiring locally in <2s before any API call."""
    trivial = (
        "fn id_fn(x: number)\n"
        "    returns x\n"
        "    trace depends on x\n"
        "    stack 0\n"
        "{\n"
        "    for x86_64 {\n"
        "        mov rax, rdi\n"
        "        ret\n"
        "    }\n"
        "    for arm64 {\n"
        "        ret\n"
        "    }\n"
        "}\n"
    )
    with tempfile.TemporaryDirectory(prefix="ode_selftest_") as td:
        td_p = Path(td)
        src = td_p / "id.ode"
        src.write_text(trivial, encoding="utf-8")
        for tgt in targets:
            out_o = td_p / f"id_{tgt}.o"
            out_p = td_p / f"id_{tgt}.proof"
            rc_p, out_p_txt, _ = run_tool([
                sys.executable, str(ODE_TOOL), "pack", str(src),
                "--fn", "id_fn", "--target", tgt,
                "--out", str(out_o), "--proof", str(out_p),
            ], td_p, timeout=30)
            if rc_p != 0 or not out_o.exists() or not out_p.exists():
                raise SystemExit(f"CLI self-test failed on `ode pack` ({tgt}): {out_p_txt}")
            cid_m = re.search(r"BLAKE3\(contract\):\s+([a-z2-7]{52})", out_p_txt)
            if not cid_m:
                raise SystemExit(f"CLI self-test failed: no BLAKE3(contract) in pack output ({tgt}): {out_p_txt}")
            rc_a, out_a_txt, _ = run_tool([
                sys.executable, str(ODE_TOOL), "audit", str(out_o),
                "--proof", str(out_p), "--expect-contract", cid_m.group(1),
            ], td_p, timeout=30)
            if rc_a != 0 or "VERDICT:           shown" not in out_a_txt:
                raise SystemExit(f"CLI self-test failed on `ode audit` ({tgt}): {out_a_txt}")
            v2_ok, v2_msg, _ = run_verify2_on_bundle(out_o, out_p, tgt)
            if not v2_ok:
                raise SystemExit(f"CLI self-test failed on `verify2.py` ({tgt}): {v2_msg}")


def check_references(tasks: list[dict], targets: list[str], x86_exec_script: str | None) -> None:
    """Before any model is asked: a task that names a reference solution must be solvable as posed.

    The reference is put through the very steps a candidate is (`ode pack`, `ode audit` with the task's
    expected contract ID, `verify2.py`, the native harness). A task whose reference fails any of them is a
    fault of the task, the tools or the harness, and would otherwise be read as a failure of the models.
    A task with no reference is named, so the report can say its solvability was not shown beforehand."""
    for task in tasks:
        ref = task.get("reference_solution")
        if not ref:
            print(f"[reference] {task['id']}: no reference solution named (solvability not shown beforehand)", flush=True)
            continue
        for tgt in targets:
            with tempfile.TemporaryDirectory(prefix="ode_ref_") as td:
                td_p = Path(td)
                shutil.copy2(ROOT / task["spec_file"], td_p / task["spec_basename"])
                cand = td_p / f"{task['id']}.ode"
                shutil.copy2(ROOT / ref, cand)
                out_o, out_p = td_p / "out.o", td_p / "out.proof"
                rc_p, txt_p, _ = run_tool([
                    sys.executable, str(ODE_TOOL), "pack", str(cand), "--fn", task["entry_fn"],
                    "--target", tgt, "--out", str(out_o), "--proof", str(out_p)], td_p, timeout=120)
                if rc_p != 0 or not out_o.exists():
                    raise SystemExit(f"reference of task `{task['id']}` fails `ode pack` ({tgt}): {txt_p[-800:]}")
                rc_a, txt_a, _ = run_tool([
                    sys.executable, str(ODE_TOOL), "audit", str(out_o), "--proof", str(out_p),
                    "--expect-contract", task["expected_contract_id"]], td_p, timeout=120)
                if rc_a != 0 or "VERDICT:           shown" not in txt_a:
                    raise SystemExit(f"reference of task `{task['id']}` fails `ode audit` ({tgt}): {txt_a[-800:]}")
                v2_ok, v2_msg, _ = run_verify2_on_bundle(out_o, out_p, tgt)
                nat_st, nat_det = run_native_test(out_o, task, tgt, x86_exec_script)
                if nat_st == "fail":
                    raise SystemExit(f"reference of task `{task['id']}` fails the native harness ({tgt}): {nat_det}")
                print(f"[reference] {task['id']} {tgt}: pack+audit shown; verify2: {v2_msg}; native: {nat_st} ({nat_det})", flush=True)


def check_quickstart_leakage(tasks: list[dict]) -> None:
    """Refuse a task whose specification file or entry function appears verbatim in docs/QUICKSTART.md."""
    qs = QUICKSTART_PATH.read_text(encoding="utf-8")
    for task in tasks:
        if task.get("allow_quickstart_overlap"):
            continue
        hits = []
        if task["spec_basename"] in qs:
            hits.append(f"spec_basename `{task['spec_basename']}`")
        if re.search(rf"\bfn\s+{re.escape(task['entry_fn'])}\b", qs):
            hits.append(f"fn `{task['entry_fn']}`")
        if hits:
            raise SystemExit(
                f"Task `{task['id']}` overlaps docs/QUICKSTART.md ({', '.join(hits)}); "
                f"models receive the Quickstart verbatim, so this would test copying rather than coding. "
                f"Choose an unseen task (or set `allow_quickstart_overlap: true` in the task JSON to override)."
            )


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Push-button pre-registered cold-room experiment runner for Ode.")
    ap.add_argument("--run-id", required=True, help="Short run identifier, e.g. ebpf-v2")
    ap.add_argument("--tasks", default="ebpf", help="Comma-separated task IDs from paper/EXPERIMENTS/tasks/")
    ap.add_argument("--models", default=(
        "openai/gpt-6.2-astra-pro,anthropic/claude-fable-5.2,google/gemini-4-neon,"
        "anthropic/claude-sonnet-5.5,anthropic/claude-haiku-5.5,"
        "qwen/qwen3.8-2.4t-a95b,moonshotai/kimi-k3.1-pro"
    ))
    ap.add_argument("--targets", default="x86_64,arm64")
    ap.add_argument("--max-rounds", type=int, default=8)
    ap.add_argument("--perf-arms", default="", help="Comma-separated optimization arms (e.g. blind,advised); empty = single-pass correctness suite")
    ap.add_argument("--opt-rounds", type=int, default=3, help="Extra optimization rounds after first verified pass when --perf-arms is active")
    ap.add_argument("--tool-timeout", type=int, default=45)
    ap.add_argument("--cell-timeout", type=int, default=540, help="Per-cell wall-clock cap in seconds (0 = off)")
    ap.add_argument("--max-truncations", type=int, default=2, help="Stop a cell after N consecutive output_token_limit replies (0 = off)")
    ap.add_argument("--prover-slots", type=int, default=10, help="Max simultaneous local ode pack/audit runs")
    ap.add_argument("--api-timeout", type=int, default=240)
    ap.add_argument("--max-tokens", type=int, default=32000)
    ap.add_argument("--temperature", type=float, default=0.2)
    ap.add_argument("--effort", default="medium")
    ap.add_argument("--max-usd", type=float, default=60.0, help="Cumulative API spend circuit breaker")
    ap.add_argument("--workers", type=int, default=16)
    ap.add_argument("--baseline", default="", help="Optional baseline results JSON for before/after diff")
    ap.add_argument("--out-dir", required=True, help="Private directory for full JSON transcripts and .o/.proof/.ode artifacts")
    ap.add_argument("--x86-exec-script", default="", help="Optional executable taking `<obj.o> <harness.c>` to run x86_64 native tests")
    ap.add_argument("--commit-prereg", action="store_true", help="Commit prereg-<run-id>.md before starting any task call")
    ap.add_argument("--allow-dirty", action="store_true", help="Allow running with uncommitted files (for dry-runs)")
    ap.add_argument("--dry-run", action="store_true", help="Run preflight & print plan without writing prereg or calling models")
    args = ap.parse_args(argv)

    task_ids = [t.strip() for t in args.tasks.split(",") if t.strip()]
    models = [m.strip() for m in args.models.split(",") if m.strip()]
    targets = [t.strip() for t in args.targets.split(",") if t.strip()]
    arms: list[str | None] = [a.strip() for a in args.perf_arms.split(",") if a.strip()] or [None]

    tasks = []
    for tid in task_ids:
        tp = TASKS_DIR / f"{tid}.json"
        if not tp.exists():
            raise SystemExit(f"Unknown task `{tid}` (missing {tp})")
        with tp.open("r", encoding="utf-8") as f:
            tasks.append(json.load(f))

    if not args.allow_dirty and git_dirty():
        raise SystemExit("Refusing to run on dirty git tree (commit or pass --allow-dirty for dry-run).")

    hashes = {
        "docs/QUICKSTART.md": blake3_hex(QUICKSTART_PATH),
        "core/x86.tab": blake3_hex(ROOT / "core/x86.tab"),
        "arm64/arm64.tab": blake3_hex(ROOT / "arm64/arm64.tab"),
        "proof-core/verify2.py": blake3_hex(VERIFY2),
        "paper/EXPERIMENTS/run_suite.py": blake3_hex(EXP_DIR / "run_suite.py"),
    }
    if ODEVERIFY.exists():
        hashes["proof-core/.lake/build/bin/odeverify"] = blake3_hex(ODEVERIFY)
    for t in tasks:
        hashes[t["spec_file"]] = blake3_hex(ROOT / t["spec_file"])
        if t.get("native_harness"):
            hashes[t["native_harness"]] = blake3_hex(ROOT / t["native_harness"])

    check_quickstart_leakage(tasks)
    self_test_cli(targets)
    check_references(tasks, targets, args.x86_exec_script or None)

    if args.dry_run:
        print(f"DRY-RUN OK (CLI self-test passed on {targets}): run_id={args.run_id} tasks={task_ids} models={len(models)} targets={targets} arms={arms} cells={len(tasks)*len(models)*len(targets)*len(arms)}")
        for k, v in sorted(hashes.items()):
            print(f"  {v[:16]}...  {k}")
        return 0

    api_key = load_openrouter_key()
    print(f"[preflight] pinging {len(models)} models...", flush=True)
    pings = preflight_ping(models, api_key, args.effort)
    for m, info in pings.items():
        print(f"[preflight] {m}: OK ({info['s']}s, ${info['cost_usd']:.4f}, reply={info['reply']!r})", flush=True)

    started_utc = utc_now()
    base_sha = git_head()
    prereg_path = write_prereg(args.run_id, tasks, models, targets, args, hashes, base_sha, started_utc, arms=arms)
    print(f"[prereg] wrote {prereg_path.relative_to(ROOT)}", flush=True)

    prereg_sha = base_sha
    if args.commit_prereg:
        subprocess.run(["git", "-C", str(ROOT), "add", str(prereg_path.relative_to(ROOT))], check=True)
        env = dict(os.environ, TZ="UTC")
        subprocess.run(
            ["git", "-C", str(ROOT), "commit", "-m", f"Pre-register cold-room experiment suite {args.run_id}"],
            check=True, env=env,
        )
        prereg_sha = git_head()
        print(f"[prereg] committed {prereg_sha}", flush=True)

    out_dir = Path(args.out_dir).expanduser().resolve()
    out_dir.mkdir(parents=True, exist_ok=True)
    budget = BudgetGuard(args.max_usd)
    prover_sem = threading.BoundedSemaphore(max(1, args.prover_slots))

    baseline_p = Path(args.baseline) if args.baseline else None
    if baseline_p and not baseline_p.is_absolute():
        baseline_p = ROOT / baseline_p

    jobs = [(t, m, tgt, arm) for t in tasks for m in models for tgt in targets for arm in arms]
    cells = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=min(args.workers, len(jobs))) as ex:
        futs = [ex.submit(run_cell, t, m, tgt, args, api_key, budget, out_dir, prover_sem, arm) for (t, m, tgt, arm) in jobs]
        for fut in concurrent.futures.as_completed(futs):
            cells.append(fut.result())
            # Progressive atomic summary update so finished cells are readable immediately without waiting for stragglers.
            write_results(args.run_id, prereg_sha, tasks, models, targets, cells, baseline_p, expected_total=len(jobs))

    j_path, m_path = write_results(args.run_id, prereg_sha, tasks, models, targets, cells, baseline_p, expected_total=len(jobs))
    print(f"[done] wrote {j_path.relative_to(ROOT)} and {m_path.relative_to(ROOT)}", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
