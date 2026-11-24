#!/usr/bin/env python3
"""Pre-registered empirical AI coder evaluation harness for Ode (paper/CODER-EXPERIMENT.md).

Evaluates cheap open-weight and frontier models across 8 locked tasks (4 categories x 2 targets:
x86-64 and AArch64) under 3 ablation arms:
  - arm_a: Baseline (task contract + raw verifier output; no reference card; raw label syntax only)
  - arm_b: +Card (docs/ODE-CARD.md in system prompt + raw verifier output)
  - arm_c: Full Step 2 (docs/ODE-CARD.md + ode_tool surgical diagnostics + structured control flow)

Every candidate `.ode` program is judged strictly by the Lean 4 verifier `odeverify` via `ode_tool.py`.
Runs cleanly in `--mock` mode (zero network, zero cost) for deterministic testing, or `--live` against
OpenRouter with a hard `--max-usd` cap enforced before every API request.
"""
import argparse, json, os, re, subprocess, sys, tempfile, time, urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
CARD_PATH = os.path.join(ROOT, "docs", "ODE-CARD.md")
TOOL_PATH = os.path.join(ROOT, "lang", "ode_tool.py")
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, "lang"))
sys.path.insert(0, os.path.join(ROOT, "proof-core"))
import tasks as task_mod

ARMS = ("arm_a", "arm_b", "arm_c")
DEFAULT_MODELS = [
    "qwen/qwen3-coder-30b-a3b-instruct",
    "z-ai/glm-4.7-flash",
    "qwen/qwen3-coder-next",
    "deepseek/deepseek-v3.2",
    "mistralai/devstral-2512",
    "openai/gpt-5-mini",
    "anthropic/claude-sonnet-5.5",
]

# Pre-registered pricing snapshots (USD per 1M tokens, input / output) used as conservative fallback
# when OpenRouter omits `usage.cost` in a response.
FALLBACK_PRICING = {
    "qwen/qwen3-coder-30b-a3b-instruct": (0.07, 0.28),
    "z-ai/glm-4.7-flash": (0.06, 0.40),
    "qwen/qwen3-coder-next": (0.12, 0.80),
    "deepseek/deepseek-v3.2": (0.26, 0.38),
    "mistralai/devstral-2512": (0.40, 2.00),
    "openai/gpt-5-mini": (0.25, 2.00),
    "anthropic/claude-sonnet-5.5": (2.00, 10.00),
}


def load_card():
    with open(CARD_PATH) as f:
        return f.read()


def strip_structured_ctrl_from_card(card_text):
    """For Arm B (card without structured control flow), omit the structured control-flow bullet."""
    lines = card_text.splitlines()
    out, skipping = [], False
    for line in lines:
        if line.startswith("- **Explicit local control flow"):
            skipping = True
            continue
        if skipping and (line.startswith("- **") or line.startswith("## ")):
            skipping = False
        if not skipping:
            out.append(line)
    return "\n".join(out)


def build_system_prompt(arm, card_text):
    base = (
        "You are an expert systems programmer writing verified assembly in the Ode language. "
        "Always reply with ONE complete `.ode` source file inside a single fenced ```ode ... ``` block. "
        "Do not omit any instructions or placeholders."
    )
    if arm == "arm_a":
        return base + (
            "\nSyntax reminder: `target x86_64` or `target arm64`, `fn NAME as \"SYMBOL\" { ... }` "
            "(closing `}` at column 0), labels `@label:`, loop invariants `place { name ...; fact ...; decreases ... }`."
        )
    if arm == "arm_b":
        return base + "\n\n" + strip_structured_ctrl_from_card(card_text)
    if arm == "arm_c":
        return base + "\n\n" + card_text
    raise ValueError(f"unknown arm: {arm}")


def build_task_prompt(task):
    return (
        f"Task `{task['id']}` (target: `{task['target']}`):\n"
        f"{task['prompt']}\n\n"
        f"Locked specification and contract:\n"
        f"```spec\n{task['spec'].strip()}\n```\n\n"
        f"Return the complete `.ode` file inside ```ode ... ```."
    )


def extract_ode_source(reply_text):
    """Extract the last ```ode ... ``` (or plain ``` ... ```) fenced block, else raw text."""
    m = re.findall(r"```(?:ode)?\s*\n(.*?)```", reply_text, flags=re.S)
    if m:
        return m[-1].strip() + "\n"
    return reply_text.strip() + "\n"


def classify_failure(resp):
    """Map an `ode_tool.py serve` response to a coarse failure taxonomy bucket."""
    if resp.get("ok"):
        return "shown"
    err = resp.get("error", "")
    if err:
        low = err.lower()
        if "unknown condition" in low or "is no" in low or "cannot" in low or "line " in low:
            return "compile_error"
        return "tool_error"
    res = resp.get("result") or {}
    verdict = res.get("verdict", "")
    diag = res.get("diagnostic", "")
    raw = res.get("raw", "")
    if verdict == "FALSE":
        return "false_functional"
    if "with no place" in diag or "with no place" in raw:
        return "missing_place"
    if "values kept out of the trace" in diag or "values kept out of the trace" in raw:
        return "trace_violation"
    if "register a callee keeps" in diag or "register a callee keeps" in raw:
        return "abi_callee_saved"
    if "multiple of 16" in diag or "more stack" in diag:
        return "stack_or_align"
    if "need entail" in diag or "need know" in diag or "need entail" in raw or "need know" in raw:
        return "proof_arithmetic"
    return "other_refused"


def format_feedback(arm, resp):
    """Construct the turn feedback message seen by the model under each arm."""
    if resp.get("error"):
        return f"Compilation / tool error:\n{resp['error']}\nPlease fix the `.ode` file and return the complete code."
    res = resp.get("result") or {}
    if arm in ("arm_a", "arm_b"):
        # Raw verifier / prover failure message only (no decoded inequalities, hints, or concrete probes).
        raw = (res.get("raw") or "").strip()
        # Keep raw output concise (first 25 lines) so context stays bounded.
        lines = raw.splitlines()[:25]
        return "Verifier did not accept the code:\n" + "\n".join(lines) + "\nPlease fix the `.ode` file."
    # Arm C: full surgical diagnostic + decoded arithmetic + concrete counterexample + hint
    diag = (res.get("diagnostic") or res.get("raw") or "").strip()
    return f"ode_tool check failed (verdict={res.get('verdict')}):\n{diag}\nPlease fix the `.ode` file and return the complete code."


class ToolWorker:
    """Persistent `ode_tool.py serve` worker keeping Python and instruction tables warm."""
    def __init__(self, python_exe=None):
        self.python_exe = python_exe or sys.executable
        self.p = subprocess.Popen(
            [self.python_exe, TOOL_PATH, "serve"],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True,
        )

    def check(self, ode_path, spec_path):
        t0 = time.perf_counter()
        self.p.stdin.write(json.dumps({"cmd": "check", "source": ode_path, "spec": spec_path}) + "\n")
        self.p.stdin.flush()
        line = self.p.stdout.readline()
        dt = time.perf_counter() - t0
        if not line:
            raise RuntimeError("ode_tool serve exited unexpectedly")
        return json.loads(line), dt

    def close(self):
        if self.p is not None:
            self.p.stdin.close()
            self.p.stdout.close()
            self.p.wait()
            self.p = None


def call_openrouter(model, messages, api_key, max_tokens=2048, timeout=120):
    payload = json.dumps({
        "model": model,
        "messages": messages,
        "temperature": 0.0,
        "max_tokens": max_tokens,
    }).encode("utf-8")
    req = urllib.request.Request(
        "https://openrouter.ai/api/v1/chat/completions",
        data=payload,
        headers={
            "Authorization": f"Bearer {api_key}",
            "Content-Type": "application/json",
            "X-Title": "ode-coder-experiment",
        },
        method="POST",
    )
    t0 = time.perf_counter()
    with urllib.request.urlopen(req, timeout=timeout) as r:
        data = json.loads(r.read().decode("utf-8"))
    dt = time.perf_counter() - t0
    choice = data["choices"][0]["message"]["content"]
    usage = data.get("usage") or {}
    pt = int(usage.get("prompt_tokens", 0) or 0)
    ct = int(usage.get("completion_tokens", 0) or 0)
    if "cost" in usage and usage["cost"] is not None:
        cost = float(usage["cost"])
    else:
        pin, pout = FALLBACK_PRICING.get(model, (1.0, 4.0))
        cost = (pt * pin + ct * pout) / 1e6
    return choice, pt, ct, cost, dt


def run_trial(worker, task, arm, model, call_fn, card_text, max_turns=5):
    """Run one (model, arm, task) trial up to `max_turns` turns; returns structured record."""
    messages = [
        {"role": "system", "content": build_system_prompt(arm, card_text)},
        {"role": "user", "content": build_task_prompt(task)},
    ]
    turns = []
    total_cost = 0.0
    total_llm_s = 0.0
    total_tool_s = 0.0
    total_in = 0
    total_out = 0
    passed_turn = None
    last_bucket = "not_run"

    with tempfile.TemporaryDirectory() as td:
        spec_p = os.path.join(td, "task.spec")
        with open(spec_p, "w") as f:
            f.write(task["spec"])
        for turn in range(1, max_turns + 1):
            reply, pt, ct, cost, llm_s = call_fn(model, messages, turn, task, arm)
            total_cost += cost
            total_llm_s += llm_s
            total_in += pt
            total_out += ct
            ode_src = extract_ode_source(reply)
            ode_p = os.path.join(td, f"try_{turn}.ode")
            with open(ode_p, "w") as f:
                f.write(ode_src)
            # Arm A prohibits structured control flow syntax so baseline isolates raw Ode
            if arm == "arm_a" and re.search(r"^\s*(if\s+\w+\s*\{|loop\s*\{|break\b|continue\b)", ode_src, re.M):
                resp = {"ok": False, "error": "Arm A baseline allows raw labels only (structured if/loop disabled in Arm A)"}
                tool_s = 0.0
            else:
                resp, tool_s = worker.check(ode_p, spec_p)
            total_tool_s += tool_s
            bucket = classify_failure(resp)
            last_bucket = bucket
            turns.append({
                "turn": turn,
                "ok": bool(resp.get("ok")),
                "bucket": bucket,
                "llm_s": round(llm_s, 3),
                "tool_s": round(tool_s, 3),
                "prompt_tokens": pt,
                "completion_tokens": ct,
                "cost_usd": round(cost, 6),
            })
            if resp.get("ok"):
                passed_turn = turn
                break
            messages.append({"role": "assistant", "content": reply})
            messages.append({"role": "user", "content": format_feedback(arm, resp)})

    return {
        "model": model,
        "arm": arm,
        "task_id": task["id"],
        "category": task["category"],
        "target": task["target"],
        "passed": passed_turn is not None,
        "passed_turn": passed_turn,
        "pass_at_1": passed_turn == 1,
        "turns_used": len(turns),
        "final_bucket": last_bucket,
        "llm_s": round(total_llm_s, 3),
        "tool_s": round(total_tool_s, 3),
        "prompt_tokens": total_in,
        "completion_tokens": total_out,
        "cost_usd": round(total_cost, 6),
        "turns": turns,
    }


def summarize_records(records):
    """Compute per-(model, arm) pass@1, pass@K, mean turns, latency share, and USD per verified function."""
    groups = {}
    for r in records:
        groups.setdefault((r["model"], r["arm"]), []).append(r)
    rows = []
    for (model, arm), items in sorted(groups.items()):
        n = len(items)
        p1 = sum(1 for x in items if x["pass_at_1"])
        pk = sum(1 for x in items if x["passed"])
        cost = sum(x["cost_usd"] for x in items)
        llm_s = sum(x["llm_s"] for x in items)
        tool_s = sum(x["tool_s"] for x in items)
        share = (100.0 * tool_s / (llm_s + tool_s)) if (llm_s + tool_s) > 0 else 0.0
        rows.append({
            "model": model, "arm": arm, "n": n, "pass1": p1, "passK": pk,
            "cost_usd": round(cost, 4),
            "usd_per_verified": round(cost / pk, 4) if pk else None,
            "tool_share_pct": round(share, 2),
        })
    return rows


def main(argv=None):
    ap = argparse.ArgumentParser(description="Pre-registered Ode AI coder experiment runner.")
    ap.add_argument("--mode", choices=("mock", "live"), default="mock")
    ap.add_argument("--models", nargs="+", default=DEFAULT_MODELS)
    ap.add_argument("--arms", nargs="+", choices=ARMS, default=list(ARMS))
    ap.add_argument("--tasks", nargs="+", default=None, help="subset of task IDs")
    ap.add_argument("--max-turns", type=int, default=5)
    ap.add_argument("--max-usd", type=float, default=5.0, help="hard cumulative USD cap in live mode")
    ap.add_argument("--out", required=True, help="JSONL output log path")
    args = ap.parse_args(argv)

    selected = [t for t in task_mod.TASKS if args.tasks is None or t["id"] in args.tasks]
    if not selected:
        raise SystemExit("no tasks selected")
    card_text = load_card()

    spent = [0.0]
    if args.mode == "live":
        api_key = os.environ.get("OPENROUTER_API_KEY")
        if not api_key:
            raise SystemExit("OPENROUTER_API_KEY must be set for --mode live")
        def call_fn(model, messages, turn, task, arm):
            if spent[0] >= args.max_usd:
                raise SystemExit(f"hard budget cap reached: ${spent[0]:.4f} >= ${args.max_usd:.2f}")
            reply, pt, ct, cost, dt = call_openrouter(model, messages, api_key)
            spent[0] += cost
            return reply, pt, ct, cost, dt
    else:
        # Deterministic mock: Turn 1 returns the planted negative control; Turn 2 returns the reference
        # in Arm C (simulating repair after surgical feedback), while Arm A keeps returning negative.
        def call_fn(model, messages, turn, task, arm):
            code = task["reference"] if (arm == "arm_c" and turn >= 2) else task["negative"]
            return f"```ode\n{code}\n```", 500, 150, 0.0001, 0.01

    records = []
    worker = ToolWorker()
    try:
        os.makedirs(os.path.dirname(os.path.abspath(args.out)), exist_ok=True)
        with open(args.out, "w") as logf:
            for model in args.models:
                for arm in args.arms:
                    for task in selected:
                        rec = run_trial(worker, task, arm, model, call_fn, card_text, max_turns=args.max_turns)
                        records.append(rec)
                        logf.write(json.dumps(rec) + "\n")
                        logf.flush()
    finally:
        worker.close()

    for row in summarize_records(records):
        print(json.dumps(row))
    return 0


if __name__ == "__main__":
    sys.exit(main())
