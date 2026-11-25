#!/usr/bin/env pypy3
"""Pre-registered multi-model cold-room experiment runner for RFC 9669 eBPF in Ode.

See `paper/EXPERIMENTS/prereg-ebpf-v1.md` for the locked protocol, exact input hashes,
model panel, timeouts, and primary/secondary outcome criteria.

Usage (from repository root):
    pypy3 paper/EXPERIMENTS/ebpf_v1_runner.py \
        --model anthropic/claude-fable-5.2 \
        --target arm64 \
        --out ~/tmp/exp-v1/fable52-arm64.json \
        --artifact ~/tmp/exp-v1/fable52-arm64.ode
"""
import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
SPEC_PATH = ROOT / "proof-core" / "examples" / "ebpf" / "ebpf_spec.ode"
QUICKSTART_PATH = ROOT / "docs" / "QUICKSTART.md"
ODE_TOOL = ROOT / "lang" / "ode_tool.py"
VERIFY2 = ROOT / "proof-core" / "verify2.py"

EXPECTED_CONTRACT_ID = "d7b6z5hr3w25whmsn56nvv3qcsq5ugtcxifauztdznaekaiiahfa"

CONTRACT_HEADER = """\
use bpf = "ebpf_spec.ode"

fn ebpf_run(prog: n bytes, n: number, fuel: number, arg1: number)
    requires n < 18446744073709551615
    requires arg1 < 4294967296
    returns bpf.ebpf_run(prog, fuel, arg1)
    trace depends on prog, n, fuel, arg1
    stack 128
"""

SYSTEM_PROMPT = """\
You are a systems programmer writing verified native machine code in Ode.
You have NEVER seen an implementation of this task before. You are given:
1. The complete Ode Quickstart (`docs/QUICKSTART.md`).
2. The complete target instruction table (`core/x86.tab` or `arm64/arm64.tab`).
3. The complete specification file (`ebpf_spec.ode`), which already sits in the working
   directory alongside your `.ode` file.

Your goal is to write ONE complete, self-contained `.ode` file that imports
`ebpf_spec.ode` via `use bpf = "ebpf_spec.ode"` and implements `fn ebpf_run` for the
requested target architecture so that `ode check`, `ode pack`, and `ode audit` all
return `shown` against the exact canonical contract header below.

Rules:
- Keep the exact `fn ebpf_run` signature and contract clauses given in the task prompt
  (so its canonical contract ID matches the expected 52-character BLAKE3 identifier).
- You may define private helper functions with `calling { in ...; out ...; preserves ... }`
  in the same file (placed above `fn ebpf_run`, callees before callers), or write a single function.
- Output the complete `.ode` source file inside a single fenced code block (` ```ode ... ``` `).
- Do NOT modify `ebpf_spec.ode`; reference its definitions via `bpf.<name>`.
- If the verifier or compiler reports an error, diagnose it and return a complete updated
  `.ode` file in a single ` ```ode ... ``` ` block.\
"""


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


def extract_ode_source(reply: str) -> str:
    """Extract the `.ode` source from a fenced block (preferring ```ode, else largest fence)."""
    blocks = re.findall(r"```(?:ode)?[ \t]*\n(.*?)```", reply, flags=re.DOTALL)
    if blocks:
        # Prefer the last block that contains `fn ebpf_run` (in case reasoning showed a snippet first)
        for b in reversed(blocks):
            if "fn ebpf_run" in b:
                return b.strip() + "\n"
        return blocks[-1].strip() + "\n"
    return reply.strip() + "\n"


def call_openrouter(model: str, messages: list[dict], api_key: str,
                    temperature: float = 0.2, max_tokens: int = 16000,
                    effort: str = "medium", timeout: int = 220) -> tuple[str, dict, float]:
    payload = {
        "model": model,
        "temperature": temperature,
        "max_tokens": max_tokens,
        "reasoning": {"effort": effort},
        "messages": messages,
    }
    req = urllib.request.Request(
        "https://openrouter.ai/api/v1/chat/completions",
        data=json.dumps(payload).encode("utf-8"),
        headers={
            "Authorization": f"Bearer {api_key}",
            "Content-Type": "application/json",
            "HTTP-Referer": "https://github.com/samshackleton-tech/ode",
            "X-Title": "Ode Pre-Registered eBPF Experiment v1",
        },
        method="POST",
    )
    t0 = time.monotonic()
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        data = json.loads(resp.read().decode("utf-8"))
    dt = time.monotonic() - t0
    ch = data["choices"][0]
    content = (ch["message"].get("content") or "").strip()
    usage = data.get("usage", {})
    usage["finish_reason"] = ch.get("finish_reason")
    return content, usage, dt


def run_tool(cmd: list[str], cwd: Path, timeout: int = 120) -> tuple[int, str, float]:
    t0 = time.monotonic()
    try:
        r = subprocess.run(cmd, cwd=str(cwd), capture_output=True, text=True, timeout=timeout)
        return r.returncode, (r.stdout + "\n" + r.stderr).strip(), time.monotonic() - t0
    except subprocess.TimeoutExpired as e:
        out = (e.stdout.decode("utf-8", "replace") if isinstance(e.stdout, bytes) else (e.stdout or ""))
        err = (e.stderr.decode("utf-8", "replace") if isinstance(e.stderr, bytes) else (e.stderr or ""))
        return 124, f"TIMEOUT after {timeout}s\n{out}\n{err}".strip(), time.monotonic() - t0


def build_initial_user_prompt(target: str) -> str:
    quickstart = QUICKSTART_PATH.read_text(encoding="utf-8")
    tab_path = ROOT / ("arm64/arm64.tab" if target == "arm64" else "core/x86.tab")
    tab_text = tab_path.read_text(encoding="utf-8")
    spec_text = SPEC_PATH.read_text(encoding="utf-8")
    return (
        f"## Task\n\n"
        f"Implement and verify the RFC 9669 eBPF bytecode interpreter `ebpf_run` for target `{target}`.\n\n"
        f"Use this EXACT import and exported contract header for `ebpf_run` (expected canonical contract ID: "
        f"`{EXPECTED_CONTRACT_ID}`):\n\n"
        f"```ode\n{CONTRACT_HEADER}```\n\n"
        f"Return a single complete `.ode` file implementing `for {target} {{ ... }}` (and any optional private "
        f"`for {target} calling {{ ... }}` helpers you choose to define).\n\n"
        f"---\n\n"
        f"## Complete Ode Quickstart (`docs/QUICKSTART.md`)\n\n{quickstart}\n\n"
        f"---\n\n"
        f"## Complete Target Instruction Table (`{tab_path.relative_to(ROOT)}`)\n\n```\n{tab_text}\n```\n\n"
        f"---\n\n"
        f"## Complete Specification (`ebpf_spec.ode`)\n\n```ode\n{spec_text}\n```\n"
    )


def parse_audit_metrics(audit_out: str) -> dict:
    m = re.search(
        r"COVERAGE:\s+100% of executable code \((.+?)\)",
        audit_out,
    )
    info = {"coverage_line": m.group(1) if m else None}
    mi = re.search(r"(\d+) instructions,\s+(\d+) B", audit_out)
    if mi:
        info["instructions"] = int(mi.group(1))
        info["bytes"] = int(mi.group(2))
    mf = re.search(r"\((\d+) functions?", audit_out)
    if mf:
        info["functions"] = int(mf.group(1))
    return info


def main() -> None:
    ap = argparse.ArgumentParser(description="Pre-registered RFC 9669 eBPF Ode experiment runner")
    ap.add_argument("--model", required=True)
    ap.add_argument("--target", choices=["x86_64", "arm64"], required=True)
    ap.add_argument("--max-rounds", type=int, default=8)
    ap.add_argument("--api-timeout", type=int, default=220)
    ap.add_argument("--tool-timeout", type=int, default=120)
    ap.add_argument("--temperature", type=float, default=0.2)
    ap.add_argument("--max-tokens", type=int, default=16000)
    ap.add_argument("--effort", default="medium")
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--artifact", type=Path, required=True)
    args = ap.parse_args()

    api_key = load_openrouter_key()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.artifact.parent.mkdir(parents=True, exist_ok=True)

    py = shutil.which("python3") or sys.executable
    messages = [
        {"role": "system", "content": SYSTEM_PROMPT},
        {"role": "user", "content": build_initial_user_prompt(args.target)},
    ]

    record = {
        "experiment": "prereg-ebpf-v1",
        "model": args.model,
        "target": args.target,
        "expected_contract_id": EXPECTED_CONTRACT_ID,
        "params": {
            "max_rounds": args.max_rounds,
            "api_timeout": args.api_timeout,
            "tool_timeout": args.tool_timeout,
            "temperature": args.temperature,
            "max_tokens": args.max_tokens,
            "effort": args.effort,
        },
        "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "passed": False,
        "rounds_to_pass": None,
        "total_cost_usd": 0.0,
        "total_api_s": 0.0,
        "total_tool_s": 0.0,
        "final_metrics": {},
        "rounds": [],
    }

    with tempfile.TemporaryDirectory(prefix=f"ode_exp_{args.target}_") as td:
        work = Path(td)
        shutil.copy2(SPEC_PATH, work / "ebpf_spec.ode")
        cand = work / "ebpf_candidate.ode"
        out_o = work / "ebpf_candidate.o"
        out_p = work / "ebpf_candidate.proof"

        for rnum in range(1, args.max_rounds + 1):
            rlog = {"round": rnum}
            try:
                reply, usage, api_s = call_openrouter(
                    args.model, messages, api_key,
                    temperature=args.temperature,
                    max_tokens=args.max_tokens,
                    effort=args.effort,
                    timeout=args.api_timeout,
                )
            except Exception as e:
                rlog["api_error"] = str(e)
                record["rounds"].append(rlog)
                break

            cost = float(usage.get("cost") or 0.0)
            record["total_cost_usd"] += cost
            record["total_api_s"] += api_s
            rlog["api_s"] = round(api_s, 2)
            rlog["usage"] = usage

            if not reply:
                rlog["error"] = "empty_reply"
                record["rounds"].append(rlog)
                messages.append({"role": "assistant", "content": ""})
                messages.append({"role": "user", "content": "Your previous reply was empty. Output the complete `.ode` file inside a single ```ode ... ``` block."})
                continue

            src = extract_ode_source(reply)
            cand.write_text(src, encoding="utf-8")
            args.artifact.write_text(src, encoding="utf-8")
            rlog["source_lines"] = len(src.splitlines())
            rlog["source_bytes"] = len(src.encode("utf-8"))

            # Step A: fast development feedback via `ode check` (checks all fns in file)
            chk_rc, chk_out, chk_s = run_tool(
                [py, str(ODE_TOOL), "check", str(cand), "--target", args.target],
                cwd=ROOT, timeout=args.tool_timeout,
            )
            record["total_tool_s"] += chk_s
            rlog["check_rc"] = chk_rc
            rlog["check_s"] = round(chk_s, 2)
            rlog["check_out_tail"] = chk_out[-2500:]

            if chk_rc == 0 and chk_out.lstrip().startswith("shown"):
                # Step B: full pack + audit against locked expected contract ID
                pk_rc, pk_out, pk_s = run_tool(
                    [py, str(ODE_TOOL), "pack", str(cand), "--fn", "ebpf_run", "--target", args.target,
                     "--out", str(out_o), "--proof", str(out_p)],
                    cwd=ROOT, timeout=args.tool_timeout,
                )
                record["total_tool_s"] += pk_s
                rlog["pack_rc"] = pk_rc
                rlog["pack_s"] = round(pk_s, 2)
                rlog["pack_out_tail"] = pk_out[-2000:]

                if pk_rc == 0:
                    au_rc, au_out, au_s = run_tool(
                        [py, str(ODE_TOOL), "audit", str(out_o), "--proof", str(out_p),
                         "--expect-contract", EXPECTED_CONTRACT_ID],
                        cwd=ROOT, timeout=args.tool_timeout,
                    )
                    record["total_tool_s"] += au_s
                    rlog["audit_rc"] = au_rc
                    rlog["audit_s"] = round(au_s, 2)
                    rlog["audit_out"] = au_out
                    if au_rc == 0 and "VERDICT:" in au_out and "shown" in au_out:
                        metrics = parse_audit_metrics(au_out)
                        metrics["proof_bytes"] = out_p.stat().st_size
                        metrics["obj_bytes"] = out_o.stat().st_size
                        metrics["audit_s"] = round(au_s, 3)
                        record["passed"] = True
                        record["rounds_to_pass"] = rnum
                        record["final_metrics"] = metrics
                        record["rounds"].append(rlog)
                        print(f"[PASS] {args.model} ({args.target}) round {rnum}/{args.max_rounds}: "
                              f"{metrics} cost=${record['total_cost_usd']:.3f}", flush=True)
                        break
                    feedback = f"`ode check` passed, but `ode audit --expect-contract {EXPECTED_CONTRACT_ID}` failed (exit {au_rc}):\n\n```\n{au_out[-3000:]}\n```\nFix the contract header or code so `ode audit` passes with the exact expected contract ID."
                else:
                    feedback = f"`ode check` passed, but `ode pack` failed (exit {pk_rc}):\n\n```\n{pk_out[-3000:]}\n```\nFix the issue and return the complete updated `.ode` file."
            else:
                feedback = (
                    f"`ode check --target {args.target}` failed (exit {chk_rc}, {chk_s:.1f}s):\n\n"
                    f"```\n{chk_out[-3500:]}\n```\n\n"
                    f"Diagnose the failure above and return the complete fixed `.ode` file inside a single ```ode ... ``` block."
                )

            record["rounds"].append(rlog)
            print(f"[R{rnum}] {args.model} ({args.target}): check_rc={chk_rc} ({chk_s:.1f}s) "
                  f"api={api_s:.1f}s cost=${record['total_cost_usd']:.3f}", flush=True)

            messages.append({"role": "assistant", "content": reply})
            messages.append({"role": "user", "content": feedback})

            # Keep conversation bounded while preserving the initial prompt + latest 3 rounds verbatim
            if len(messages) > 2 + 6:
                messages = messages[:2] + messages[-6:]

    record["finished_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    record["total_cost_usd"] = round(record["total_cost_usd"], 5)
    record["total_api_s"] = round(record["total_api_s"], 2)
    record["total_tool_s"] = round(record["total_tool_s"], 2)

    with args.out.open("w", encoding="utf-8") as f:
        json.dump(record, f, indent=2)
        f.write("\n")

    if not record["passed"]:
        print(f"[FAIL] {args.model} ({args.target}) did not pass in {args.max_rounds} rounds "
              f"(cost=${record['total_cost_usd']:.3f})", flush=True)


if __name__ == "__main__":
    main()
