#!/usr/bin/env python3
"""Pre-registered Performance-Modeling A/B Experiment runner (`paper/PERF-MODEL-EXPERIMENT.md`).

Compares Arm P0 (blind optimization) vs Arm P1 (`ode_tool advise` + turn-by-turn `compare` feedback)
across 8 verified Wave 1 baselines (4 routines x 2 architectures) and the clean 5-model panel
(80 paired episodes, up to 4 turns each). Saves all verified candidates for real-silicon timing.
"""

import argparse
import concurrent.futures
import hashlib
import json
import os
import queue
import sys
import tempfile
import threading
import time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path[:0] = [
    os.path.join(ROOT, "paper", "coder-exp"),
    os.path.join(ROOT, "factory"),
    os.path.join(ROOT, "lang"),
    os.path.join(ROOT, "kcheck"),
    os.path.join(ROOT, "proof-core"),
    os.path.join(ROOT, "advice"),
]

import ode_tool
import run_experiment as rexp
import run_factory as rf

MODELS = [
    "anthropic/claude-sonnet-5.5",
    "openai/gpt-5-mini",
    "deepseek/deepseek-v3.2",
    "mistralai/devstral-2512",
    "qwen/qwen3-coder-30b-a3b-instruct",
]

TASKS = [
    ("base64_char_val", "x86_64", "zen5"),
    ("base64_char_val", "arm64", "apple_m"),
    ("der_tlv_len", "x86_64", "zen5"),
    ("der_tlv_len", "arm64", "apple_m"),
    ("sha256_big_sigma_4x", "x86_64", "zen5"),
    ("sha256_big_sigma_4x", "arm64", "apple_m"),
    ("adler32_s1", "x86_64", "zen5"),
    ("adler32_s1", "arm64", "apple_m"),
]

VERIFIED_DIR = os.path.join(ROOT, "factory", "verified")


def format_advise_block(whole, arch):
    ut = ", ".join(f"{k}={v}" for k, v in sorted((whole.get("unit_throughput") or {}).items()))
    return (
        f"Static performance estimate (`ode_tool advise --arch {arch}`):\n"
        f"  instructions        : {whole['instructions']}\n"
        f"  code bytes          : {whole['bytes']}\n"
        f"  uops                : {whole['uops']}\n"
        f"  compute_lower_bound : {whole['compute_lower_bound']} cycles\n"
        f"  critical_path       : {whole['critical_path']} cycles\n"
        f"  frontend_issue      : {whole['frontend_issue']} cycles\n"
        f"  limiting bottleneck : {whole['limiting']}\n"
        f"  unit throughput     : {ut}\n"
        f"  distinct registers  : {whole.get('distinct_gpr', 0)} GPR, {whole.get('distinct_vec', 0)} VEC"
    )


def format_compare_block(base_w, cand_w, arch):
    def delta(key):
        d = round(cand_w[key] - base_w[key], 2)
        return f"{d:+g}"
    return (
        f"VERIFIED `shown`! Comparison vs baseline (`{arch}`):\n"
        f"  instructions        : {base_w['instructions']} -> {cand_w['instructions']} ({delta('instructions')})\n"
        f"  code bytes          : {base_w['bytes']} -> {cand_w['bytes']} ({delta('bytes')})\n"
        f"  uops                : {base_w['uops']} -> {cand_w['uops']} ({delta('uops')})\n"
        f"  compute_lower_bound : {base_w['compute_lower_bound']} -> {cand_w['compute_lower_bound']} ({delta('compute_lower_bound')})\n"
        f"  critical_path       : {base_w['critical_path']} -> {cand_w['critical_path']} ({delta('critical_path')})\n"
        f"  limiting bottleneck : {base_w['limiting']} -> {cand_w['limiting']}"
    )


def score_tuple(w):
    return (w["compute_lower_bound"], w["critical_path"], w["instructions"], w["bytes"])


def build_initial_prompt(rid, target, arch, arm, spec_txt, base_ode, base_w, card):
    hdr = (
        f"You are optimizing an already-verified Ode implementation of `{rid}` for target `{target}` "
        f"(microarchitecture `{arch}`).\n"
        "Your goal is to make the function execute as FAST as possible on real hardware while remaining "
        "100% verified `shown` by Ode's Lean 4 verifier `odeverify` against the exact contract below.\n"
        "Output ONLY the complete updated `.ode` file inside a single ```ode ... ``` fenced code block.\n"
    )
    if arm == "P1":
        hdr += (
            "\nYou have live feedback from Ode's static performance estimator (`ode_tool advise`). "
            "Target the limiting bottleneck first: reduce `compute_lower_bound` (and `critical_path`, "
            "`uops`, and `instructions` — e.g. eliminate redundant branches/moves, shorten dependency chains, "
            "reorder fast paths, or unroll hot loops cleanly while keeping the proof valid).\n\n"
            + format_advise_block(base_w, arch) + "\n"
        )
    else:
        hdr += (
            "\nOptimize for maximum execution speed on real hardware (fewer redundant branches/moves, "
            "shorter dependency chains, tighter hot loops, faster common paths) while keeping the proof valid.\n"
        )
    return (
        f"{hdr}\n"
        f"--- Ode Quick Reference ---\n{card}\n"
        f"--- Specification (.spec) ---\n```ode\n{spec_txt.strip()}\n```\n\n"
        f"--- Current Verified Baseline (.ode) ---\n```ode\n{base_ode.strip()}\n```\n"
    )


def run_episode(rid, target, arch, model, arm, card, api_key, pool, spend_lock, spend, max_usd, cand_dir, max_turns=4):
    tid = f"{rid}_{target}"
    ep_id = f"{tid}__{model.split('/')[-1]}__{arm}"
    ode_p = os.path.join(VERIFIED_DIR, f"{tid}.ode")
    spec_p = os.path.join(VERIFIED_DIR, f"{tid}.spec")
    with open(ode_p) as f:
        base_ode = f.read()
    with open(spec_p) as f:
        spec_txt = f.read()

    # Measure baseline static metrics
    base_adv = ode_tool.run_advise(ode_p, spec_path=spec_p, arch=arch)
    base_w = base_adv["static"]["whole"]
    base_hash = hashlib.sha256(base_ode.strip().encode()).hexdigest()[:12]

    system_msg = (
        "You are an expert low-level assembly and Ode programmer. "
        "Return ONLY valid Ode source code in one ```ode ... ``` code block, preserving the exact "
        "`target` directive and exported symbol name(s)."
    )
    user_msg = build_initial_prompt(rid, target, arch, arm, spec_txt, base_ode, base_w, card)
    messages = [{"role": "system", "content": system_msg}, {"role": "user", "content": user_msg}]

    t_start = time.time()
    ep_cost = 0.0
    attempts = []
    verified_list = []
    seen_verified_hashes = {base_hash}

    with tempfile.TemporaryDirectory(prefix=f"ode_perf_{ep_id}_") as td:
        tmp_spec = os.path.join(td, "task.spec")
        with open(tmp_spec, "w") as f:
            f.write(spec_txt)

        for turn in range(1, max_turns + 1):
            with spend_lock:
                if spend[0] >= max_usd:
                    break
            try:
                content, pt, ct, cost, t_llm = rexp.call_openrouter(model, messages, api_key, timeout=120, max_retries=2)
            except Exception as e:
                attempts.append({"turn": turn, "bucket": "api_error", "error": str(e)[:300]})
                break
            t_llm = round(t_llm, 2)
            ep_cost += cost
            with spend_lock:
                spend[0] += cost

            messages.append({"role": "assistant", "content": content})
            code = rexp.extract_ode_source(content)
            if not code:
                attempts.append({"turn": turn, "bucket": "no_code_block", "llm_s": t_llm, "cost": round(cost, 6)})
                messages.append({"role": "user", "content": "No ```ode ... ``` block found. Reply with ONLY one complete ```ode``` code block."})
                continue

            src_p = os.path.join(td, f"turn_{turn}.ode")
            with open(src_p, "w") as f:
                f.write(code + "\n")
            c_hash = hashlib.sha256(code.strip().encode()).hexdigest()[:12]

            worker = pool.get()
            try:
                resp, t_tool = worker.check(src_p, tmp_spec, arch=arch, out_dir=td)
            finally:
                pool.put(worker)
            t_tool = round(t_tool, 3)

            res = resp.get("result") or {}
            if resp.get("ok"):
                cw = (res.get("static") or {}).get("whole")
                if not cw:
                    adv = ode_tool.run_advise(src_p, spec_path=tmp_spec, arch=arch)
                    cw = adv["static"]["whole"]
                changed = (c_hash != base_hash)
                strict_better = score_tuple(cw) < score_tuple(base_w)
                rec = {
                    "turn": turn, "bucket": "shown", "hash": c_hash, "changed": changed,
                    "strict_better": strict_better, "llm_s": t_llm, "tool_s": t_tool,
                    "cost": round(cost, 6), "whole": cw, "verify_s": res.get("verify_s", 0.0),
                    "proof_bytes": res.get("proof_bytes", 0),
                }
                attempts.append(rec)
                verified_list.append((rec, code))

                # Save every distinct verified candidate for real-silicon benchmarking!
                if changed and c_hash not in seen_verified_hashes:
                    seen_verified_hashes.add(c_hash)
                    os.makedirs(cand_dir, exist_ok=True)
                    out_p = os.path.join(cand_dir, f"{ep_id}__t{turn}__{c_hash}.ode")
                    with open(out_p, "w") as f:
                        f.write(code + "\n")

                if turn == max_turns:
                    break
                if arm == "P1":
                    cmp_txt = format_compare_block(base_w, cw, arch)
                    messages.append({
                        "role": "user",
                        "content": (
                            f"{cmp_txt}\n\n"
                            "Can you reduce `compute_lower_bound`, `critical_path`, or `instructions` even further "
                            "while keeping it verified `shown`? Reply with ONLY one complete ```ode``` code block."
                        ),
                    })
                else:
                    # Arm P0: blind feedback — ONLY say verified `shown` (no static numbers!)
                    messages.append({
                        "role": "user",
                        "content": (
                            "Verified `shown`! Can you make this implementation even faster on real hardware "
                            "while keeping it verified `shown`? Reply with ONLY one complete ```ode``` code block."
                        ),
                    })
            else:
                diag = resp.get("error") or res.get("diagnostic") or res.get("raw") or str(resp)
                bucket = rexp.classify_failure(resp)
                attempts.append({
                    "turn": turn, "bucket": bucket, "llm_s": t_llm, "tool_s": t_tool,
                    "cost": round(cost, 6), "diag": diag[:300],
                })
                messages.append({
                    "role": "user",
                    "content": f"Verification failed ({bucket}):\n{diag}\n\nFix the code and reply with ONLY one complete ```ode``` code block.",
                })

    # Choose episode's selected candidate per pre-registered rule
    selected = None
    if verified_list:
        if arm == "P1":
            best_rec, _ = min(verified_list, key=lambda x: score_tuple(x[0]["whole"]))
            selected = best_rec
        else:
            # Arm P0: last verified submission (P0 sees no static estimator)
            selected = verified_list[-1][0]

    out = {
        "ep_id": ep_id, "rid": rid, "target": target, "arch": arch, "model": model, "arm": arm,
        "base_hash": base_hash, "base_whole": base_w,
        "any_verified": bool(verified_list),
        "any_changed_verified": any(r["changed"] for r, _ in verified_list),
        "selected": selected,
        "best_verified": min((r for r, _ in verified_list), key=lambda r: score_tuple(r["whole"])) if verified_list else None,
        "cost_usd": round(ep_cost, 6),
        "wall_s": round(time.time() - t_start, 2),
        "attempts": attempts,
    }
    tag = "BETTER" if (selected and selected["strict_better"]) else ("VERIF " if selected else "FAIL  ")
    if selected:
        sw = selected["whole"]
        print(
            f"{tag} {ep_id:48s} | lb {base_w['compute_lower_bound']:4.1f}->{sw['compute_lower_bound']:4.1f} "
            f"| crit {base_w['critical_path']:4.1f}->{sw['critical_path']:4.1f} "
            f"| ins {base_w['instructions']:2d}->{sw['instructions']:2d} | ${ep_cost:.4f} | {out['wall_s']:5.1f}s",
            flush=True,
        )
    else:
        print(f"{tag} {ep_id:48s} | no verified candidate | ${ep_cost:.4f} | {out['wall_s']:5.1f}s", flush=True)
    return out


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--out", default=os.path.join(ROOT, "paper", "coder-exp", "perf-results-20261124.jsonl"))
    p.add_argument("--cand-dir", default=os.path.join(ROOT, "paper", "coder-exp", "perf-candidates"))
    p.add_argument("--workers", type=int, default=10)
    p.add_argument("--tool-workers", type=int, default=4)
    p.add_argument("--max-usd", type=float, default=15.0)
    p.add_argument("--max-turns", type=int, default=4)
    p.add_argument("--resume", action="store_true")
    p.add_argument("--only", default="")
    args = p.parse_args()

    api_key = rf.load_openrouter_key()
    card = rexp.load_card()

    done = set()
    if args.resume and os.path.exists(args.out):
        with open(args.out) as f:
            for line in f:
                if line.strip():
                    done.add(json.loads(line)["ep_id"])

    jobs = []
    for rid, tgt, arch in TASKS:
        if args.only and args.only not in f"{rid}_{tgt}":
            continue
        for model in MODELS:
            for arm in ("P0", "P1"):
                ep_id = f"{rid}_{tgt}__{model.split('/')[-1]}__{arm}"
                if ep_id not in done:
                    jobs.append((rid, tgt, arch, model, arm))

    print(f"Perf-Model Experiment: {len(jobs)} episodes to run ({len(done)} resumed), max ${args.max_usd:.2f}", flush=True)
    pool = queue.Queue()
    workers = [rf.FactoryWorker() for _ in range(args.tool_workers)]
    for w in workers:
        pool.put(w)

    spend_lock = threading.Lock()
    spend = [0.0]
    write_lock = threading.Lock()
    t0 = time.time()
    try:
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as ex:
            futs = [
                ex.submit(
                    run_episode, rid, tgt, arch, model, arm, card, api_key,
                    pool, spend_lock, spend, args.max_usd, args.cand_dir, args.max_turns,
                )
                for (rid, tgt, arch, model, arm) in jobs
            ]
            for fut in concurrent.futures.as_completed(futs):
                rec = fut.result()
                with write_lock:
                    with open(args.out, "a") as f:
                        f.write(json.dumps(rec) + "\n")
    finally:
        for w in workers:
            w.close()

    print(f"DONE in {time.time() - t0:.1f}s wall, total spend ${spend[0]:.4f}", flush=True)


if __name__ == "__main__":
    main()
