#!/usr/bin/env python3
"""Spec-First AI Factory runner: turns declarative Ode specs into Lean-4-verified
x86-64 and AArch64 machine code using a tiered AI coder ladder + `ode_tool.py serve`.

Tiered escalation ladder (clean panel; excludes dropped models):
  Tier 1: deepseek/deepseek-v3.2      (ultra-cheap, ~$0.003/ver)
  Tier 2: openai/gpt-5-mini           (fast reasoning, ~$0.007/ver)
  Tier 3: anthropic/claude-sonnet-5.5 (frontier fallback, ~$0.024/ver)

Every passing artifact is verified by the Lean 4 `odeverify` binary and saved under
`factory/verified/<id>_<target>.{spec,ode,proof,statement,o}` along with its
static `ode_tool` performance advice.
"""
import argparse, concurrent.futures, json, os, queue, shutil, sys, tempfile, threading, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path[:0] = [HERE, os.path.join(ROOT, "paper", "coder-exp"), os.path.join(ROOT, "lang")]

import catalog
import run_experiment as rexp

DEFAULT_TIERS = [
    ("deepseek/deepseek-v3.2", 3),
    ("openai/gpt-5-mini", 3),
    ("anthropic/claude-sonnet-5.5", 4),
]

ARCH_FOR_TARGET = {"x86_64": "zen5", "arm64": "apple_m"}


class FactoryWorker:
    """Persistent `ode_tool.py serve` worker supporting `out` artifact saving and `arch` advice."""
    def __init__(self, python_exe=None):
        self.w = rexp.ToolWorker(python_exe=python_exe or sys.executable)

    def check(self, ode_path, spec_path, out_dir=None, arch=None):
        req = {"cmd": "check", "source": ode_path, "spec": spec_path}
        if out_dir:
            req["out"] = out_dir
        if arch:
            req["arch"] = arch
        t0 = time.perf_counter()
        self.w.p.stdin.write(json.dumps(req) + "\n")
        self.w.p.stdin.flush()
        line = self.w.p.stdout.readline()
        dt = time.perf_counter() - t0
        if not line:
            raise RuntimeError("ode_tool serve exited unexpectedly")
        return json.loads(line), dt

    def close(self):
        self.w.close()


def load_openrouter_key():
    key = os.environ.get("OPENROUTER_API_KEY")
    if key:
        return key.strip()
    auth_path = os.path.expanduser("~/.pi/agent/auth.json")
    if os.path.exists(auth_path):
        with open(auth_path) as f:
            data = json.load(f)
        if isinstance(data, dict):
            ent = data.get("openrouter")
            if isinstance(ent, dict) and ent.get("key"):
                return ent["key"].strip()
            if isinstance(ent, str) and ent.strip():
                return ent.strip()
    raise RuntimeError("No OpenRouter API key found in OPENROUTER_API_KEY or ~/.pi/agent/auth.json")


def spec_for_target(routine, target):
    sp = routine["spec"]
    if target == "x86_64" and routine.get("needs_x86"):
        idx = sp.rfind("}")
        sp = sp[:idx] + routine["needs_x86"] + sp[idx:]
    return sp


def build_factory_prompt(routine, target):
    arch_hint = (
        "Target architecture: `target x86_64` (System V AMD64 ABI: args rdi, rsi, rdx, rcx, r8, r9; return rax)."
        if target == "x86_64" else
        "Target architecture: `target arm64` (AAPCS64 ABI: args x0..x7; return x0; scratch x9..x15; callee-saved x19..x30)."
    )
    sp = spec_for_target(routine, target)
    return (
        f"Routine `{routine['id']}` — {routine['title']}\n"
        f"{arch_hint}\n"
        f"Notes: {routine['prompt_notes']}\n\n"
        f"Locked specification and contract:\n"
        f"```spec\n{sp.strip()}\n```\n\n"
        f"Write clean, fast, idiomatic Ode code that satisfies the contract completely. "
        f"Return ONE complete `.ode` file inside ```ode ... ```."
    )


def run_one_target(routine, target, tiers, card_text, api_key, worker_pool, spend_lock, spend_box, max_usd, verified_dir):
    t_start = time.perf_counter()
    tid = f"{routine['id']}_{target}"
    arch = ARCH_FOR_TARGET[target]
    sys_prompt = rexp.build_system_prompt("arm_c", card_text)
    user_prompt = build_factory_prompt(routine, target)

    total_cost = 0.0
    total_llm_s = 0.0
    total_tool_s = 0.0
    total_in = 0
    total_out = 0
    attempts = []
    winner = None
    final_meta = None

    with tempfile.TemporaryDirectory(prefix=f"ode_fac_{tid}_") as td:
        spec_txt = spec_for_target(routine, target)
        spec_p = os.path.join(td, f"{tid}.spec")
        with open(spec_p, "w") as f:
            f.write(spec_txt)

        for tier_idx, (model, max_turns) in enumerate(tiers, start=1):
            messages = [
                {"role": "system", "content": sys_prompt},
                {"role": "user", "content": user_prompt},
            ]
            tier_passed = False
            for turn in range(1, max_turns + 1):
                with spend_lock:
                    if spend_box[0] >= max_usd:
                        attempts.append({"tier": tier_idx, "model": model, "turn": turn, "bucket": "budget_cap"})
                        break
                try:
                    reply, pt, ct, cost, llm_s = rexp.call_openrouter(model, messages, api_key)
                except BaseException as e:
                    attempts.append({"tier": tier_idx, "model": model, "turn": turn, "bucket": "api_error", "error": str(e)[:200]})
                    break
                with spend_lock:
                    spend_box[0] += cost
                total_cost += cost
                total_llm_s += llm_s
                total_in += pt
                total_out += ct

                ode_src = rexp.extract_ode_source(reply)
                ode_p = os.path.join(td, f"t{tier_idx}_{turn}.ode")
                out_d = os.path.join(td, f"out_{tier_idx}_{turn}")
                os.makedirs(out_d, exist_ok=True)
                with open(ode_p, "w") as f:
                    f.write(ode_src)

                worker = worker_pool.get()
                try:
                    resp, tool_s = worker.check(ode_p, spec_p, out_dir=out_d, arch=arch)
                finally:
                    worker_pool.put(worker)
                total_tool_s += tool_s
                bucket = rexp.classify_failure(resp)
                attempts.append({
                    "tier": tier_idx, "model": model, "turn": turn,
                    "bucket": bucket, "cost_usd": round(cost, 6),
                    "llm_s": round(llm_s, 3), "tool_s": round(tool_s, 3),
                })
                if not resp.get("ok"):
                    diag_txt = (resp.get("error") or (resp.get("result") or {}).get("diagnostic") or (resp.get("result") or {}).get("raw") or "")
                    attempts[-1]["diag"] = diag_txt[:400]
                    err_brief = diag_txt[:110].replace("\n", " | ")
                    print(f"  try  {tid:30s} T{tier_idx} t{turn} -> {bucket:18s} (llm {llm_s:4.1f}s, tool {tool_s:4.1f}s) {err_brief}", flush=True)

                if resp.get("ok"):
                    tier_passed = True
                    winner = {"tier": tier_idx, "model": model, "turn": turn}
                    res = resp.get("result") or {}
                    st = res.get("static") or {}
                    wh = st.get("whole") or {}
                    final_meta = {
                        "proof_bytes": res.get("proof_bytes"),
                        "verify_s": res.get("verify_s"),
                        "prove_s": res.get("prove_s"),
                        "compile_s": res.get("compile_s"),
                        "insns": wh.get("instructions"),
                        "bytes": wh.get("bytes"),
                        "uops": wh.get("uops"),
                        "cycles_est": wh.get("compute_lower_bound"),
                        "critical_path": wh.get("critical_path"),
                        "bottleneck": wh.get("limiting"),
                        "arch": arch,
                    }
                    os.makedirs(verified_dir, exist_ok=True)
                    with open(os.path.join(verified_dir, f"{tid}.spec"), "w") as f:
                        f.write(spec_txt)
                    with open(os.path.join(verified_dir, f"{tid}.ode"), "w") as f:
                        f.write(ode_src)
                    for fn in os.listdir(out_d):
                        src_f = os.path.join(out_d, fn)
                        if fn.endswith(".proof"):
                            shutil.copyfile(src_f, os.path.join(verified_dir, f"{tid}.proof"))
                        elif fn.endswith(".statement"):
                            shutil.copyfile(src_f, os.path.join(verified_dir, f"{tid}.statement"))
                    break

                messages.append({"role": "assistant", "content": reply})
                messages.append({"role": "user", "content": rexp.format_feedback("arm_c", resp)})

            if tier_passed:
                break

    wall_s = time.perf_counter() - t_start
    return {
        "id": routine["id"],
        "target": target,
        "tid": tid,
        "pillar": routine["pillar"],
        "symbol": routine["symbol"],
        "passed": winner is not None,
        "winner": winner,
        "meta": final_meta,
        "cost_usd": round(total_cost, 6),
        "llm_s": round(total_llm_s, 3),
        "tool_s": round(total_tool_s, 3),
        "wall_s": round(wall_s, 3),
        "prompt_tokens": total_in,
        "completion_tokens": total_out,
        "attempts": attempts,
    }


def main():
    ap = argparse.ArgumentParser(description="Run Spec-First AI Factory over Wave 1 routines.")
    ap.add_argument("--only", action="append", default=None, help="restrict to routine id(s)")
    ap.add_argument("--target", choices=["x86_64", "arm64", "both"], default="both")
    ap.add_argument("--wave", choices=["1", "2", "all"], default="1")
    ap.add_argument("--workers", type=int, default=12)
    ap.add_argument("--tool-workers", type=int, default=6)
    ap.add_argument("--max-usd", type=float, default=15.0)
    ap.add_argument("--out", default=os.path.join(HERE, "results", "wave1-20261124.jsonl"))
    ap.add_argument("--verified-dir", default=os.path.join(HERE, "verified"))
    ap.add_argument("--resume", action="store_true", help="skip targets already passed in --out")
    ap.add_argument("--start-tier", type=int, default=1, help="1-indexed starting tier in DEFAULT_TIERS")
    args = ap.parse_args()
    tiers = DEFAULT_TIERS[max(0, args.start_tier - 1):]

    api_key = load_openrouter_key()
    card_text = rexp.load_card()
    targets = ["x86_64", "arm64"] if args.target == "both" else [args.target]
    routines = (
        catalog.WAVE1_ROUTINES if args.wave == "1"
        else catalog.WAVE2_ROUTINES if args.wave == "2"
        else catalog.ALL_ROUTINES
    )
    if args.only:
        want = set(args.only)
        routines = [r for r in routines if r["id"] in want]

    done_tids = set()
    if args.resume and os.path.exists(args.out):
        with open(args.out) as f:
            for line in f:
                if line.strip():
                    rec = json.loads(line)
                    if rec.get("passed"):
                        done_tids.add(rec["tid"])

    jobs = [(r, t) for r in routines for t in targets if f"{r['id']}_{t}" not in done_tids]
    print(f"Spec-First AI Factory Wave {args.wave}: {len(jobs)} jobs to run ({len(done_tids)} resumed), max ${args.max_usd:.2f}")
    sys.stdout.flush()

    os.makedirs(os.path.dirname(args.out), exist_ok=True)
    pool = queue.Queue()
    workers = [FactoryWorker() for _ in range(min(args.tool_workers, max(1, len(jobs))))]
    for w in workers:
        pool.put(w)

    spend_lock = threading.Lock()
    file_lock = threading.Lock()
    spend_box = [0.0]
    t0 = time.perf_counter()
    passed_cnt = 0

    try:
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as ex:
            futs = [
                ex.submit(run_one_target, r, t, tiers, card_text, api_key,
                          pool, spend_lock, spend_box, args.max_usd, args.verified_dir)
                for r, t in jobs
            ]
            for fut in concurrent.futures.as_completed(futs):
                rec = fut.result()
                with file_lock:
                    with open(args.out, "a") as f:
                        f.write(json.dumps(rec) + "\n")
                if rec["passed"]:
                    passed_cnt += 1
                    w = rec["winner"]
                    m = rec["meta"] or {}
                    print(
                        f"SHOWN  {rec['tid']:30s} | T{w['tier']} {w['model']:28s} turn {w['turn']} | "
                        f"${rec['cost_usd']:.4f} | {rec['wall_s']:5.1f}s | "
                        f"{str(m.get('insns')):>3s} insns, {str(m.get('cycles_est')):>5s} cyc, "
                        f"proof {m.get('proof_bytes')}B"
                    )
                else:
                    last = rec["attempts"][-1] if rec["attempts"] else {}
                    print(
                        f"FAIL   {rec['tid']:30s} | {len(rec['attempts']):2d} tries | "
                        f"${rec['cost_usd']:.4f} | {rec['wall_s']:5.1f}s | last={last.get('bucket')}"
                    )
                sys.stdout.flush()
    finally:
        for w in workers:
            w.close()

    dt = time.perf_counter() - t0
    print(f"\nDONE: {passed_cnt}/{len(jobs)} shown in {dt:.1f}s wall, total spend ${spend_box[0]:.4f}")


if __name__ == "__main__":
    main()
