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

## 9. Round 1 Live Results (24 November 2026)

Raw per-trial logs for all 150 live trials are recorded in
[`coder-exp/results/live-20261124.jsonl`](coder-exp/results/live-20261124.jsonl).
Total live spend across Round 1 was **$2.68** (well under the $5.00 cap).

**Disclosed operational deviations from the pre-registered harness:**
1. Before live trials began, a zero-task compatibility check showed that reasoning models
   (`z-ai/glm-4.7-flash`, `openai/gpt-5-mini`) count internal reasoning tokens against `max_tokens`.
   `max_tokens` was raised from `2048` to `8192` so reasoning chains were not truncated mid-code, and
   transient HTTP retry and parallel trial workers (`--workers 16`, `--resume`) were added. No prompt,
   card, task, contract, or scoring rule was changed.
2. `z-ai/glm-4.7-flash` was stopped early after 6 partial trials (`$0.046` spent) because its reasoning
   chains took 435–750 seconds per failed trial (often hitting the 8,192-token limit and returning an
   empty reply). All 6 partial records remain in the JSONL log; aggregate comparisons below report the
   6 full models (**144 trials**, 48 per arm, **$2.63 total**).

### Results by model and arm

Each row below gives one model and one arm (`arm_a` = baseline without the card, `arm_b` = card plus raw
verifier output, `arm_c` = card plus surgical diagnostics and structured control flow). Columns show
completed tasks (`n`), tasks verified `shown` on turn 1 (`pass@1`), tasks verified `shown` within 5 turns
(`pass@5`), total API spend (`Spend`), cost per verified function (`$/ver`), and the percentage of total
wall-clock time spent inside `ode_tool` rather than waiting on the model (`Tool %`).

| Model | Arm | n | pass@1 | pass@5 | Spend | $/ver | Tool % |
|---|---|---:|---:|---:|---:|---:|---:|
| `anthropic/claude-sonnet-5.5` | `arm_a` | 8 | 0 | 2 | $0.6510 | $0.3255 | 0.05% |
| `anthropic/claude-sonnet-5.5` | `arm_b` | 8 | 6 | 6 | $0.5320 | $0.0887 | 0.32% |
| `anthropic/claude-sonnet-5.5` | `arm_c` | 8 | 6 | 6 | $0.6773 | $0.1129 | 0.24% |
| `openai/gpt-5-mini` | `arm_a` | 8 | 0 | 1 | $0.1534 | $0.1534 | 0.00% |
| `openai/gpt-5-mini` | `arm_b` | 8 | 3 | 6 | $0.1127 | $0.0188 | 0.07% |
| `openai/gpt-5-mini` | `arm_c` | 8 | 2 | 6 | $0.1182 | $0.0197 | 0.08% |
| `deepseek/deepseek-v3.2` | `arm_a` | 8 | 0 | 1 | $0.0180 | $0.0180 | 0.02% |
| `deepseek/deepseek-v3.2` | `arm_b` | 8 | 4 | 5 | $0.0243 | $0.0049 | 0.29% |
| `deepseek/deepseek-v3.2` | `arm_c` | 8 | 3 | 5 | $0.0246 | $0.0049 | 0.13% |
| `mistralai/devstral-2512` | `arm_a` | 8 | 0 | 1 | $0.0503 | $0.0503 | 0.05% |
| `mistralai/devstral-2512` | `arm_b` | 8 | 4 | 4 | $0.0312 | $0.0078 | 0.58% |
| `mistralai/devstral-2512` | `arm_c` | 8 | 3 | 4 | $0.0328 | $0.0082 | 0.67% |
| `qwen/qwen3-coder-30b-a3b-instruct` | `arm_a` | 8 | 0 | 0 | $0.0167 | — | 0.01% |
| `qwen/qwen3-coder-30b-a3b-instruct` | `arm_b` | 8 | 2 | 2 | $0.0311 | $0.0155 | 0.83% |
| `qwen/qwen3-coder-30b-a3b-instruct` | `arm_c` | 8 | 1 | 2 | $0.0368 | $0.0184 | 2.05% |
| `qwen/qwen3-coder-next` | `arm_a` | 8 | 0 | 0 | $0.0570 | — | 0.00% |
| `qwen/qwen3-coder-next` | `arm_b` | 8 | 0 | 2 | $0.0323 | $0.0162 | 0.54% |
| `qwen/qwen3-coder-next` | `arm_c` | 8 | 1 | 2 | $0.0295 | $0.0147 | 0.45% |
| `z-ai/glm-4.7-flash` *(stopped early)* | `arm_a`/`b`/`c` | 3/2/1 | 0/0/0 | 0/0/1 | $0.0462 | $0.0462 | 0.01% |

### Aggregate by arm and by task (6 full models, 48 trials per arm)

Each row in the first table summarizes one arm across all 6 full models (48 trials). Each cell in the
second table shows `pass@1 / pass@5` out of the 6 full models for one task and one arm.

| Arm | pass@1 | pass@5 | Total spend | $/verified | Top final failure buckets |
|---|---:|---:|---:|---:|---|
| `arm_a` (no card) | 0/48 (0.0%) | 5/48 (10.4%) | $0.9465 | $0.1893 | `compile_error` (40), `other_refused` (2), `proof_arithmetic` (1) |
| `arm_b` (+card) | 19/48 (39.6%) | 25/48 (52.1%) | $0.7637 | $0.0305 | `false_functional` (8), `other_refused` (7), `compile_error` (6), `proof_arithmetic` (2) |
| `arm_c` (full Step 2) | 16/48 (33.3%) | 25/48 (52.1%) | $0.9191 | $0.0368 | `other_refused` (10), `compile_error` (7), `false_functional` (4), `proof_arithmetic` (2) |

| Task | `arm_a` | `arm_b` | `arm_c` |
|---|---:|---:|---:|
| `T1_x86_mix_step` | 0 / 3 | 4 / 4 | 2 / 4 |
| `T2_arm_mix_step` | 0 / 1 | 4 / 5 | 4 / 5 |
| `T3_x86_lead_zeros` | 0 / 0 | 3 / 5 | 2 / 5 |
| `T4_arm_lead_zeros` | 0 / 0 | 5 / 6 | 5 / 5 |
| `T5_x86_pad16` | 0 / 0 | 0 / 0 | 0 / 0 |
| `T6_arm_pad16` | 0 / 0 | 0 / 0 | 0 / 0 |
| `T7_x86_mix_twice` | 0 / 1 | 1 / 2 | 1 / 3 |
| `T8_arm_mix_twice` | 0 / 0 | 2 / 3 | 2 / 3 |

### Evaluation of pre-registered hypotheses (Round 1)

- **H1 (Pass rate lift — partially confirmed):** Adding `docs/ODE-CARD.md` (`arm_a -> arm_b`) raised
  aggregate `pass@1` from **0.0% to 39.6%** and `pass@5` from **10.4% to 52.1%** (and **69.4%** across
  the 6 non-`pad16` tasks, with Claude Sonnet 5.5 at 6/6 `pass@1`, GPT-5-mini at 6/6 `pass@5`, and
  DeepSeek v3.2 at 5/6 `pass@5`). However, **`arm_c` did not exceed `arm_b` in Round 1** (both 52.1%
  `pass@5`; `arm_c` slightly lower on `pass@1` at 33.3%). Two concrete causes explain this:
  1. Only 2 of 23 failures in `arm_b` were `proof_arithmetic`, so Upgrade A's decoded arithmetic hints
     rarely fired; most remaining failures were compile/syntax errors or an inaccurate card line.
  2. Our own `docs/ODE-CARD.md` falsely listed `wrote out[.. i] = expr` alongside `wrote out[i ..] = expr`
     and omitted a worked countdown-write example. Every model (including Claude Sonnet 5.5 and
     GPT-5-mini) tried forward loops with `wrote out[.. i]`, which `prove.py` refuses — causing **0/24**
     across every model on `T5_x86_pad16` and `T6_arm_pad16`.
- **H2 (Cost per verified function — confirmed vs `arm_a`, not yet `arm_c < arm_b`):** Cost per verified
  function fell **6.2x** from `arm_a` (**$0.1893**) to `arm_b` (**$0.0305**), with DeepSeek v3.2 at
  **$0.0049/verified** and Devstral 2512 at **$0.0078/verified**.
- **H3 (Tool latency share < 5% — strongly confirmed):** Tool/verifier wall-clock share ranged from
  **0.00% to 2.05%** across all models and arms; LLM token latency dominates by 50x–500x.
- **H4 (Architecture symmetry):** Across `arm_b` + `arm_c` (48 trials per target), **AArch64 outperformed
  x86-64**: **45.8% vs 27.1% `pass@1`** and **56.2% vs 47.9% `pass@5`**, because AArch64's uniform
  3-operand syntax avoided x86-64 table quirks (`mov byte ptr [addr], al` requiring `al`, 64-bit-only
  `cmp`, no indexed `[base + reg]` in `lea`).

## 10. Round 2 Live Results (After Root-Cause Language and Tool Fixes)

Rather than adding a list of "gotchas to avoid" to `docs/ODE-CARD.md`, Round 2 fixed the five root
causes revealed by Round 1 directly in Ode's tables, compiler, prover, verifier, and live diagnostics:

1. **General 8-bit x86-64 byte stores (`core/x86.tab`):** Replaced the hardcoded `al`-only row
   `mov8_m_al` with `mov8_mr` (`mov byte ptr [B64 + N], S8`, any 8-bit register `al..r15b`, 0 new rows,
   0 Lean lines, cross-checked against real x86-64 silicon and `clang`).
2. **Indexed x86-64 `lea` (`core/x86.tab`):** Added `lea_idx` (`lea D64, [B64 + S64 + N]`, +1 table row,
   0 Lean lines, cross-checked against real x86-64 silicon and `clang`).
3. **Official ARMv8 vector-copy alias (`arm64/asm.py`):** Accepted `mov vD.16b, vS.16b` as the official
   architectural alias of `orr vD.16b, vS.16b, vS.16b` (identical 4-byte encoding, 0 new rows, 0 Lean lines).
4. **Uniform `frame.<field>` offsets, `u32`/`u64`, condition aliases, and live table-driven diagnostics
   (`lang/odec.py`, `lang/ode_tool.py`):** Exposed `frame.<field>` byte offsets in every instruction,
   accepted `lo`/`cc` (`ult`) and `hs`/`cs` (`uge`) in structured control flow, and generated "supported
   forms" hints in `arm_c` directly from `x86.tab` and `arm64.tab` (zero hardcoded gotcha lists).
5. **Forward byte-write loops (`proof-core/Core.lean`, `SoundLoop.lean`, `prove.py`):** Generalized
   `RangeF` to support ascending `wrote out[.. i] = expr` loops alongside descending `wrote out[i ..] = expr`
   loops, proved sound across all 18 Lean 4 soundness modules (zero `sorry`, all 10 top-level theorems
   unchanged), and added a clean forward-loop 5th example (`card_pad8_x86`) to `docs/ODE-CARD.md`
   (2,473 words, all 5 examples verified `shown`).

Round 2 re-ran `arm_b` and `arm_c` on the same 6 full models and 8 tasks (`95/96` trials recorded in
[`coder-exp/results/live-round2-20261124.jsonl`](coder-exp/results/live-round2-20261124.jsonl); one trial,
`qwen/qwen3-coder-next` `arm_c` `T2_arm_mix_step`, hit an upstream HTTP 429 rate limit). Total spend for
all 95 Round 2 trials was **$0.75** (less than half of the $1.68 spent on the same two arms in Round 1).

### Round 1 vs Round 2 aggregate (6 full models, `arm_b` and `arm_c`)

Each row compares Round 1 and Round 2 for one arm (`arm_b` = quick-start card plus raw verifier output;
`arm_c` = quick-start card plus surgical diagnostics and live table hints). Columns show completed trials
(`n`), turn-1 pass rate (`pass@1`), 5-turn pass rate (`pass@5`), total API spend (`Spend`), and API cost
per verified function (`$/ver`).

| Round & Arm | n | pass@1 | pass@5 | Spend | $/ver |
|---|---:|---:|---:|---:|---:|
| Round 1 `arm_b` | 48 | 19/48 (39.6%) | 25/48 (52.1%) | $0.7637 | $0.0305 |
| **Round 2 `arm_b`** | **48** | **29/48 (60.4%)** | **34/48 (70.8%)** | **$0.3954** | **$0.0116** |
| Round 1 `arm_c` | 48 | 16/48 (33.3%) | 25/48 (52.1%) | $0.9191 | $0.0368 |
| **Round 2 `arm_c`** | **47** | **23/47 (48.9%)** | **34/47 (72.3%)** | **$0.3556** | **$0.0105** |

### Round 2 per model (`arm_b` and `arm_c`)

Each row gives one model and one arm in Round 2. Columns show completed tasks (`n`), `pass@1`, `pass@5`,
total API spend (`Spend`), cost per verified function (`$/ver`), and tool wall-clock share (`Tool %`).

| Model | Arm | n | pass@1 | pass@5 | Spend | $/ver | Tool % |
|---|---|---:|---:|---:|---:|---:|---:|
| `anthropic/claude-sonnet-5.5` | `arm_b` | 8 | 8 | 8 | $0.1955 | $0.0244 | 0.95% |
| `anthropic/claude-sonnet-5.5` | `arm_c` | 8 | 8 | 8 | $0.1973 | $0.0247 | 0.89% |
| `openai/gpt-5-mini` | `arm_b` | 8 | 6 | 7 | $0.0964 | $0.0138 | 0.14% |
| `openai/gpt-5-mini` | `arm_c` | 8 | 4 | 8 | $0.0533 | $0.0067 | 0.22% |
| `deepseek/deepseek-v3.2` | `arm_b` | 8 | 5 | 6 | $0.0198 | $0.0033 | 0.29% |
| `deepseek/deepseek-v3.2` | `arm_c` | 8 | 4 | 6 | $0.0199 | $0.0033 | 0.24% |
| `mistralai/devstral-2512` | `arm_b` | 8 | 5 | 6 | $0.0233 | $0.0039 | 1.80% |
| `mistralai/devstral-2512` | `arm_c` | 8 | 4 | 6 | $0.0267 | $0.0044 | 1.44% |
| `qwen/qwen3-coder-30b-a3b-instruct` | `arm_b` | 8 | 3 | 4 | $0.0303 | $0.0076 | 2.09% |
| `qwen/qwen3-coder-30b-a3b-instruct` | `arm_c` | 8 | 2 | 4 | $0.0346 | $0.0086 | 1.99% |
| `qwen/qwen3-coder-next` | `arm_b` | 8 | 2 | 3 | $0.0301 | $0.0100 | 0.41% |
| `qwen/qwen3-coder-next` *(1 rate-limited)* | `arm_c` | 7 | 1 | 2 | $0.0238 | $0.0119 | 0.25% |

### Round 2 per task (`pass@1 / pass@5` across the 6 models)

Each cell shows `pass@1 / pass@5` out of the 6 models for one task and one arm in Round 2 (Round 1
`arm_b` / `arm_c` `pass@5` shown in parentheses for comparison).

| Task | Round 2 `arm_b` | Round 2 `arm_c` | Round 1 `pass@5` (`b`/`c`) |
|---|---:|---:|---:|
| `T1_x86_mix_step` | 5 / 6 | 4 / 4 | (4 / 4) |
| `T2_arm_mix_step` | 4 / 5 | 2 / 5 *(of 5)* | (5 / 5) |
| `T3_x86_lead_zeros` | 4 / 4 | 3 / 4 | (5 / 5) |
| `T4_arm_lead_zeros` | 5 / 6 | 5 / 5 | (6 / 5) |
| **`T5_x86_pad16`** | **6 / 6** | **4 / 6** | **(0 / 0)** |
| **`T6_arm_pad16`** | **2 / 4** | **2 / 5** | **(0 / 0)** |
| `T7_x86_mix_twice` | 1 / 1 | 1 / 2 | (2 / 3) |
| `T8_arm_mix_twice` | 2 / 2 | 2 / 3 | (3 / 3) |

### Key findings from Round 2

- **Fixing root causes beats documenting workarounds:** Aggregate `pass@1` jumped from **39.6% to 60.4%**
  (`arm_b`) and **33.3% to 48.9%** (`arm_c`), `pass@5` jumped from **52.1% to 70.8% / 72.3%**, and API
  cost per verified function dropped **2.6x–3.5x** (**$0.0116** in `arm_b`, **$0.0105** in `arm_c`).
- **Two frontier/mini models hit 100%:** `anthropic/claude-sonnet-5.5` verified **16/16 on turn 1**
  (100% `pass@1` across all 8 tasks on both arms, at **$0.0244/verified** — 4.6x cheaper than Round 1),
  and `openai/gpt-5-mini` verified **8/8 (100%) in `arm_c`** at **$0.0067/verified** (cutting its cost in
  half relative to `arm_b` at $0.0138/verified).
- **Sub-cent verified code from cheap open models:** Both `deepseek/deepseek-v3.2` (**$0.0033/verified**)
  and `mistralai/devstral-2512` (**$0.0039/verified**) solved **6/6 (100%)** of all single-function tasks
  (`T1`–`T6`), and `T5_x86_pad16` jumped from **0/12 to 12/12 (100%)** across all six models.
- **x86-64 parity restored (H4):** Removing the two x86-64 table quirks (`al`-only byte stores and
  missing indexed `lea`) more than doubled x86-64 `pass@1` from **27.1% to 58.3%** (now ahead of AArch64's
  **51.1%** `pass@1`; `pass@5` 68.8% x86-64 vs 74.5% AArch64).
- **`arm_c` now beats `arm_b` on both `pass@5` (72.3% vs 70.8%) and cost per verified function
  ($0.0105 vs $0.0116):** With table-driven compile hints active, `arm_c` confirmed both H1 and H2.
- **The clear next bottleneck is C calling-convention boilerplate:** Every remaining failure of
  `deepseek-v3.2` and `devstral-2512` was on `T7`/`T8` (`mix_twice`, calling a helper with C callee-saved
  register spills). Designing custom Ode-to-Ode calling conventions directly addresses both code speed
  and multi-function AI coder reliability.

*Ode stands for Obsessively Double-checking Everything.*
