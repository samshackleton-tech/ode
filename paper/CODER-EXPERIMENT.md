# Pre-Registered Experiment: AI Coder Productivity in Ode

**Status:** Pre-registered before running any model on any task in this suite (November 24, 2026). No live
language-model call has been executed yet.

## 1. Purpose

Ode's priorities are, in order:

1. Justified confidence for the auditor (Bob) with a small reliance set.
2. Machine-code speed competitive with hand-written assembly.
3. Coder productivity without sacrificing either (1) or (2).

Because the verifier checks the compiled binary directly (`odeverify`), Bob does not rely on whoever wrote
the code. That makes Ode unusually well suited to **cheap, smaller, abundant AI models** iterating against
a fast verifier loop: if a small model makes a mistake, `odeverify` refuses it; if it succeeds, Bob has
the same Lean-proved guarantee as for hand-written code.

This document pre-registers an empirical experiment measuring how much three coder-facing upgrades (which
add zero lines to Bob's reliance set) improve verified success rate, repair turns, and cost per verified
function across cheap open-weight models and frontier reference models on both x86-64 and AArch64.

## 2. Tool Latency Baseline (CPython vs PyPy and Persistent Worker)

Before testing AI coders, we measured the local tool latency so that tool checks do not bottleneck model
iteration.

### CPython 3.14 vs PyPy 8.0 (Python 3.12) on Ode workloads

Each cell in the table below gives the wall-clock time (seconds) for one run under CPython 3.14 and PyPy
8.0 on an Apple M6, and the PyPy speedup (`CPython / PyPy`, values above `1.00x` mean PyPy is faster).

| Workload | CPython 3.14 | PyPy 8.0 | PyPy speedup |
|---|---:|---:|---:|
| `ode_tool.py advise compress_arm64.ode --trace` (1 CLI call) | 0.037 s | 0.085 s | 0.44x |
| `statement.py` on all 14 BLAKE3 functions (1 CLI call) | 0.185 s | 0.406 s | 0.46x |
| `statement.py` on all 14 BLAKE3 functions (10 calls in one process) | 1.523 s | 1.326 s | **1.15x** |
| `kcheck/verify.py odebase64.o` (~2 s pure Python) | 2.032 s | 2.009 s | **1.01x** |
| `kcheck/verify.py b3hashr.o` (all 14 BLAKE3 functions) | 15.821 s | 8.811 s | **1.80x** |

Conclusion from these measurements: PyPy pays ~50–70 ms startup and JIT warmup overhead on short one-shot
CLI calls (below ~2 seconds), crosses over around 2 seconds, and runs **1.80x faster** on longer pure-Python
verification (`kcheck/verify.py b3hashr.o`). For short sub-second `ode_tool.py` edit-check cycles, CPython
starts faster, while keeping a persistent worker process (`ode_tool.py serve`) removes startup overhead on
every turn.

### End-to-end `ode_tool.py check` latency after Step 2 speedups

Three changes cut `ode_tool.py check` latency without changing `odeverify` or its soundness proofs:

- `proof-core/built.py` checks executable timestamps against Lean source files (~0.1 ms) instead of
  spawning `lake build` (~135 ms) on every CLI run when `odeverify` and `odeprove` are already current.
- `core/table.py` and `arm64/word.py` cache parsed instruction tables and encoding ways per process.
- `lang/ode_tool.py serve` keeps a single persistent JSON-lines worker running across coder repair turns.

Each cell below gives wall-clock time (milliseconds) on an x86-64 Linux work machine to compile, search
for a proof, verify with `odeverify`, and check static advice:

| Example | Cold CLI before | Cold CLI after | Persistent `serve` worker |
|---|---:|---:|---:|
| `blake3_servil_compress_in_place_arm64` (116 insns) | ~260 ms | 127 ms | **106 ms** |
| `b3l_pad_arm64` (15 insns, 64-turn loop) | ~280 ms | 143 ms | **124 ms** |
| `v_all_zero` (x86-64 loop) | ~240 ms | 98 ms | **75 ms** |

## 3. Upgrades Under Test (Zero Changes to Bob's Reliance Set)

- **Upgrade A — Surgical diagnostics (`lang/ode_tool.py`):** decodes `need entail` / `need know` rows
  into human-readable inequalities naming the function's contract parameters and register aliases (for
  example `cannot show: rsi(n) >= v18` beside `relevant facts: rsi(n) + 1 >= v18`), names modified
  callee-saved registers on ABI refusals, gives a tailored one-line hint, and runs concrete counterexample
  probes (`lang/refute_conc.py`) to separate real functional bugs (`FALSE`) from missing loop invariants
  (`no proof found`).
- **Upgrade B — Explicit local structured control flow (`lang/odec.py`):** adds `if COND { ... } [else { ... }]`,
  `loop { ... } [while COND]`, `break [if COND]`, and `continue [if COND]` over the four branch conditions
  present in both `core/x86.tab` and `arm64/arm64.tab` (`eq`, `ne`, `ult`, `uge`). The coder still writes
  every `cmp`/`test` instruction explicitly; the compiler emits zero hidden instructions and produces
  byte-for-byte identical object files to hand-labeled Ode (`lang/test_ctrl.py`).
- **Upgrade C — Compact verified reference card (`docs/ODE-CARD.md`):** a ~2,300-word cheat sheet covering
  calling conventions, Ode notation, verified x86-64 and AArch64 instructions, contracts, common
  diagnostics, and 4 complete worked examples automatically verified `shown` by `proof-core/test_card.py`.

## 4. Locked Task Suite (`paper/coder-exp/tasks.py`)

Eight self-contained tasks form a balanced 4 categories × 2 architectures (x86-64 and AArch64) matrix.
Every task's locked contract, prompt, known-good reference solution (verified `shown`), and planted
negative control (verified refused) live in `paper/coder-exp/tasks.py` and are checked by
`proof-core/test_coder_exp.py` before any model runs.

Each row below gives one task category, the x86-64 task ID, the AArch64 task ID, and the verification
skills tested.

| Category | x86-64 task | AArch64 task | Skills tested |
|---|---|---|---|
| 1. Constant-time SIMD | `T1_x86_mix_step` | `T2_arm_mix_step` | 128-bit vector loads/stores/XOR/rotate, no one-past-end pointer overflow, zero branches |
| 2. Byte-scanning loop | `T3_x86_lead_zeros` | `T4_arm_lead_zeros` | Loop control flow, `place { name; fact; decreases }`, byte loads, unsigned bounds |
| 3. Constant-time write loop | `T5_x86_pad16` | `T6_arm_pad16` | `wrote out[i ..]` loop invariant, keeping input data bytes out of the execution trace |
| 4. Stack frame + call | `T7_x86_mix_twice` | `T8_arm_mix_twice` | Frame layout, callee-saved preservation, 16-byte stack alignment, calling a helper twice |

## 5. Experimental Protocol and Ablation Arms

Every `(model, arm, task)` trial runs at `temperature = 0.0`, `max_tokens = 2048`, up to **5 turns**
(`max_turns = 5`), judged strictly by Lean's `odeverify` binary via `paper/coder-exp/run_experiment.py`.
A trial succeeds if and only if `odeverify` prints `shown` for the model's complete `.ode` output.

Each row below defines one ablation arm, what system prompt it receives, what syntax it may use, and what
feedback it sees after a failed turn.

| Arm | System prompt | Control-flow notation | Failure feedback between turns |
|---|---|---|---|
| `arm_a` (Baseline) | Minimal task prompt + 3-line syntax reminder (no card) | Raw labels only (`@L:`, `jmp`/`b`) | Raw `odeverify` / prover refusal text (first 25 lines) |
| `arm_b` (+Card) | `docs/ODE-CARD.md` with structured control-flow bullet removed | Raw labels only | Raw `odeverify` / prover refusal text (first 25 lines) |
| `arm_c` (Full Step 2) | Full `docs/ODE-CARD.md` | Structured `if`/`else`/`loop`/`while` + raw labels | Full `ode_tool.py check` surgical diagnostics (`cannot show:`, `relevant facts:`, `hint:`, `FALSE` counterexample) |

## 6. Pre-Registered Model Panel and Cost Cap

Models are queried through OpenRouter using their exact model IDs below. Each row gives the model ID,
tier, and OpenRouter catalog pricing observed on November 24, 2026 (USD per 1M input / output tokens).

| Model ID | Tier | Input ($/1M) | Output ($/1M) |
|---|---|---:|---:|
| `qwen/qwen3-coder-30b-a3b-instruct` | Small sparse open-weight coder (30B / 3B active) | 0.07 | 0.28 |
| `z-ai/glm-4.7-flash` | Small fast open-weight | 0.06 | 0.40 |
| `qwen/qwen3-coder-next` | Open-weight coder | 0.12 | 0.80 |
| `deepseek/deepseek-v3.2` | Open-weight general/coder | 0.26 | 0.38 |
| `mistralai/devstral-2512` | Open-weight coding agent | 0.40 | 2.00 |
| `openai/gpt-5-mini` | Small proprietary reference | 0.25 | 2.00 |
| `anthropic/claude-sonnet-5.5` | Frontier reference | 2.00 | 10.00 |

- **Total planned trials:** 7 models × 3 arms × 8 tasks = **168 trials** (at most 840 API calls).
- **Estimated total spend:** ~$2.50 USD across all 7 models combined (~$0.70 for the 5 open-weight models
  combined).
- **Hard budget cap:** `--max-usd 5.00` enforced in `run_experiment.py` before every API request. Live
  runs wait for explicit confirmation of the OpenRouter dollar cap.

## 7. Pre-Registered Hypotheses and Metrics

Before seeing any live model output, we register four hypotheses and six primary metrics:

- **H1 (Pass rate):** Across the 5 open-weight models pooled, `arm_c` achieves a higher `pass@5` rate than
  `arm_a`, and `arm_b` achieves a higher `pass@5` rate than `arm_a`.
- **H2 (Repair efficiency and cost):** Among tasks solved in both arms, `arm_c` uses fewer mean turns and
  lower USD cost per verified function than `arm_a` and `arm_b`.
- **H3 (Tool latency share):** With `ode_tool.py serve`, total verifier/tool time is under 5% of total
  end-to-end wall-clock time across all live trials (model inference dominates).
- **H4 (Architecture symmetry):** Report x86-64 (`T1, T3, T5, T7`) vs AArch64 (`T2, T4, T6, T8`) pass
  rates separately to identify which target-specific errors (such as AArch64 16-byte `sp` alignment or
  x86-64 single-`ret` structure) most affect small models.

Primary recorded metrics per `(model, arm)`:

1. `pass@1` (verified `shown` on turn 1, out of 8 tasks)
2. `pass@5` (verified `shown` within 5 turns, out of 8 tasks)
3. Mean turns to `shown` (over solved tasks)
4. Total USD cost and **USD per verified function** (`total_usd / pass@5`)
5. Tool wall-clock share (`tool_s / (llm_s + tool_s)`)
6. Failure taxonomy counts (`compile_error`, `false_functional`, `missing_place`, `proof_arithmetic`,
   `trace_violation`, `abi_callee_saved`, `stack_or_align`, `other_refused`)

## 8. Reproducibility

```sh
# Self-test: verifies all 8 reference solutions `shown`, all 8 negatives refused, and mock harness
cd proof-core && python3 test_coder_exp.py -v

# Live run (after confirming API cap; logs every trial to JSONL)
OPENROUTER_API_KEY=... python3 paper/coder-exp/run_experiment.py \
    --mode live --max-usd 5.00 --out results/coder-exp-20261124.jsonl
```
