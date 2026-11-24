# Performance-Modeling Experiment (Pre-Registered)

*Status: completed and measured on real Zen 5 and Apple M6 hardware (November 24, 2026). Pre-registration commit: `57ce09c8`; live episode data and 127 verified candidates: `a793446b`.*

## 1. Question

Ode includes a static performance estimator (`lang/ode_tool.py advise` and `advice/estimate.py`)
that computes an instruction count, micro-operation count, critical-path length, per-unit throughput
bound, and overall limiting factor for any compiled Ode function on a chosen processor model (`zen5`
for x86-64 or `apple_m` for AArch64).

This experiment asks two plain questions:
1. When an AI coder is given an already-verified Ode function and asked to make it faster while
   keeping it verified `shown` by the Lean 4 verifier `odeverify`, does giving the coder live
   `ode_tool advise` numbers (and turn-by-turn `compare` deltas against the baseline) produce faster
   code on **real Zen 5 and Apple M6 hardware** than asking the coder to optimize without those
   numbers?
2. How accurately do `ode_tool advise`'s static bounds (`compute_lower_bound` and `critical_path`)
   track actual measured speedups on real Zen 5 and Apple M6 processors?

## 2. Experimental Arms (Paired A/B)

Every `(task, model)` pair runs under two matched arms with the same baseline source file, the same
specification, the same quick-reference card (`docs/ODE-CARD.md`), and the same budget of **4 turns**
per episode:

- **Arm P0 (Blind Optimization Control):** The prompt gives the baseline `.ode` file and `.spec`
  file and asks the model to optimize the implementation for maximum execution speed on the target
  processor (`zen5` for x86-64, `apple_m` for AArch64) while staying verified `shown`. On each turn,
  the harness compiles, proves, and verifies the submission via `odeverify`, returning only the
  verdict (`shown` or the verifier's diagnostic on refusal). No static cycle estimates, critical-path
  numbers, or unit bottlenecks are shown.
- **Arm P1 (Performance-Model Guided):** The prompt gives the exact same baseline `.ode` file,
  `.spec` file, and card, **plus** the baseline's full `ode_tool advise` summary (`instructions`,
  `bytes`, `uops`, `compute_lower_bound`, `critical_path`, `limiting` bottleneck, and per-unit
  throughput breakdown), and asks the model to reduce `compute_lower_bound` and `critical_path` while
  staying verified `shown`. After every turn that verifies `shown`, the harness returns the exact
  before-vs-after delta (`instructions`, `uops`, `compute_lower_bound`, `critical_path`, and
  remaining `limiting` bottleneck) and invites the model to improve further if turns remain (stopping
  early only if the model repeats an identical verified solution or reaches turn 4).

In both arms, an episode keeps the **best verified `shown` submission** found across its 4 turns
(for Arm P0: the last verified submission, since P0 sees no static score; for Arm P1: the verified
submission with the lowest `compute_lower_bound`, breaking ties by `critical_path`, then `instructions`).
In addition, **all** distinct verified submissions from both arms are saved and timed on real silicon
so the comparison is not biased by the stopping rule.

## 3. Baseline Tasks (4 Routines x 2 Architectures = 8 Tasks)

Every task starts from a real-world Wave 1 routine in `factory/verified/` that is already verified
`shown` by `odeverify` and passes real-silicon RFC/ITU/FIPS tests. The table below lists each
baseline's architecture, processor model, instruction count, code bytes, static lower bound
(`compute_lower_bound`), critical-path length, and limiting factor from `ode_tool advise`.

| Task ID | Architecture | Model | Baseline Insns | Bytes | Lower Bound | Critical Path | Limiting Factor |
|---|---|---|---:|---:|---:|---:|---|
| `base64_char_val_x86_64` | x86-64 | `zen5` | 45 | 130 | 15.5 | 1.0 | `branch_throughput` |
| `base64_char_val_arm64` | AArch64 | `apple_m` | 28 | 112 | 7.0 | 2.0 | `branch_throughput` |
| `der_tlv_len_x86_64` | x86-64 | `zen5` | 74 | 262 | 19.0 | 7.0 | `branch_throughput` |
| `der_tlv_len_arm64` | AArch64 | `apple_m` | 62 | 248 | 12.5 | 9.0 | `branch_throughput` |
| `sha256_big_sigma_4x_x86_64` | x86-64 | `zen5` | 27 | 117 | 12.0 | 12.0 | `critical_path` |
| `sha256_big_sigma_4x_arm64` | AArch64 | `apple_m` | 27 | 108 | 15.0 | 15.0 | `critical_path` |
| `adler32_s1_x86_64` | x86-64 | `zen5` | 13 | 51 | 8.0 | 8.0 | `critical_path` |
| `adler32_s1_arm64` | AArch64 | `apple_m` | 15 | 60 | 8.0 | 8.0 | `critical_path` |

## 4. Model Panel (5 Models, 80 Paired Episodes)

This experiment uses the clean 5-model panel from Round 2 (excluding previously dropped models):
1. `anthropic/claude-sonnet-5.5`
2. `openai/gpt-5-mini`
3. `deepseek/deepseek-v3.2`
4. `mistralai/devstral-2512`
5. `qwen/qwen3-coder-30b-a3b-instruct`

Total live runs: `8 tasks x 5 models x 2 arms = 80 episodes` (up to 4 turns each).

## 5. Hardware Measurement Protocol

Every verified candidate produced by Arm P0 or Arm P1 is compiled to native machine code and timed
directly against its Wave 1 baseline inside the same C driver process, alternating baseline and
candidate across 15 paired trials (reporting the median nanoseconds per call and speedup ratio
`baseline_ns / candidate_ns`):

- **`base64_char_val`**: loop over all 256 byte values (`0..255`), 20,000 sweeps per trial.
- **`der_tlv_len`**: loop over a fixed 16-entry corpus of valid short-form, 1-byte long, 2-byte
  long, and rejected malformed DER TLV inputs, 200,000 sweeps per trial.
- **`sha256_big_sigma_4x`**: 500,000 calls per trial with output fed back into input to measure
  critical-path latency, plus an independent-buffer throughput pass.
- **`adler32_s1`**: 10,000 calls per trial on a 4,096-byte input buffer.

x86-64 measurements run on the Ryzen 9700X (Zen 5) measurement host through `pinned-run` under its
bench lock. AArch64 measurements run on the Apple M6 build Mac.

## 6. Pre-Registered Primary Endpoints & Hypotheses

1. **Primary Endpoint 1 (Verified Static Improvement Rate):** Fraction of episodes producing a
   verified `shown` variant with strictly lower `compute_lower_bound` (or equal `compute_lower_bound`
   and strictly lower `critical_path` or `instructions`) than baseline.
   *Hypothesis H1:* Arm P1 beats Arm P0 in verified improvement rate and median static bound
   reduction, especially on `branch_throughput`-limited tasks (`base64_char_val`, `der_tlv_len`) and
   `critical_path`-limited SIMD tasks (`sha256_big_sigma_4x`).
2. **Primary Endpoint 2 (Real-Silicon Speedup):** Geometric mean speedup (`baseline_ns / candidate_ns`)
   across verified candidates on real Zen 5 and real Apple M6 hardware.
   *Hypothesis H2:* Arm P1 achieves strictly greater real-hardware speedup than Arm P0 across paired
   `(task, model)` cells where both arms verify a changed binary, and produces faster best-of-panel
   binaries.
3. **Primary Endpoint 3 (Model Calibration):** Rank correlation (Spearman rho) between `ode_tool
   advise`'s predicted speedup (`baseline_lb / candidate_lb`) and measured hardware speedup across
   all verified candidates on Zen 5 and Apple M6.
   *Hypothesis H3:* Positive correlation (rho > 0.4) overall, with any divergences (such as branch
   misprediction or loop unrolling vs straight-line estimates) documented clearly for improving
   `advice/estimate.py`.

## 7. Results

All 80 paired episodes (`8 tasks x 5 models x 2 arms`, 320 total attempts) completed for **$3.0251**
in API spend (`$1.4061` for Arm P0, `$1.6190` for Arm P1), producing **127 distinct verified
`shown` candidate binaries** (58 unique selected changed binaries across the two architectures:
27 on x86-64, 31 on AArch64). Every verified candidate passed Lean 4 `odeverify` (`shown`) and
passed an exhaustive output-equality check against its Wave 1 baseline inside the C benchmark driver
before timing.

x86-64 candidates were timed on the Ryzen 9700X (Zen 5) measurement machine through `pinned-run`
under its exclusive bench lock (`ode-perf-exp-zen5-20261124T082637-00762ede`, `VERIFIED`; raw data
in `paper/coder-exp/perf-timing-zen5.json`). AArch64 candidates were timed on the Apple M6 build
machine (raw data in `paper/coder-exp/perf-timing-apple-m6.json`).

### 7.1 Summary of Pre-Registered Endpoints

The table below compares Arm P0 (blind optimization) against Arm P1 (guided by `ode_tool advise` and
turn-by-turn `compare` deltas) across all 40 matched `(task, model)` pairs. Each cell reports the
count or ratio for that arm across the full panel and split by target architecture.

| Metric | Arm P0 (Blind) | Arm P1 (`advise` + `compare`) | Verdict on Hypothesis |
|---|---:|---:|---|
| Episodes producing a verified `shown` binary | 34 / 40 (85.0%) | 36 / 40 (90.0%) | +2 verified episodes for P1 |
| **Endpoint 1:** Strictly better static summary | 6 / 40 (15.0%) | 9 / 40 (22.5%) | **H1 supported** |
| **Endpoint 1:** Strictly lower `compute_lower_bound` | 4 / 40 (10.0%) | 8 / 40 (20.0%) | **H1 supported (2.0x rate)** |
| Static `compute_lower_bound` regressions | 2 / 40 (5.0%) | 1 / 40 (2.5%) | Fewer regressions in P1 |
| **Endpoint 2:** Real speedups `>= 1.05x` (all) | 7 / 34 (20.6%) | 7 / 36 (19.4%) | **H2 split by architecture** |
| **Endpoint 2:** Real speedups `>= 1.05x` (Zen 5 x86-64) | 3 / 15 (20.0%) | 5 / 17 (29.4%) | P1 ahead on Zen 5 |
| **Endpoint 2:** Real speedups `>= 1.05x` (Apple M6 arm64) | 4 / 19 (21.1%) | 2 / 19 (10.5%) | P0 ahead on Apple M6 |
| Mean real speedup across verified runs (Zen 5) | `1.0720x` | `1.0995x` | P1 ahead on Zen 5 |
| Mean real speedup across verified runs (Apple M6) | `1.0588x` | `1.0020x` | P0 ahead on Apple M6 |
| Paired head-to-head wins (`>1%` margin, 40 pairs) | 10 wins (21 ties) | 9 wins (21 ties) | Zen 5: 5–4 P1; M6: 6–4 P0 |
| Paired geometric mean `P1 / P0` (33 both-verified pairs) | — | `0.9724x` | Zen 5 `1.0000x`; M6 `0.9526x` |
| Total API cost (40 episodes / cost per verified ep) | `$1.4061` (`$0.0414`) | `$1.6190` (`$0.0450`) | +15% cost for `advise` turns |

### 7.2 Primary Endpoint 3: Calibration of `ode_tool advise` vs Real Silicon

The table below reports Spearman rank correlation (`rho`) between predicted speedup
(`baseline_lb / candidate_lb` from `ode_tool advise`, and simple instruction-count ratio
`baseline_ins / candidate_ins`) and actual measured speedup (`baseline_ns / candidate_ns`) across
all 58 unique verified changed binaries.

| Subset of Verified Candidates | Count (`N`) | Spearman `rho` (`advise` lower bound) | Spearman `rho` (instruction count) |
|---|---:|---:|---:|
| **Zen 5 (x86-64) — all unique candidates** | 27 | **`+0.707`** | `+0.744` |
| Zen 5 (x86-64) — branchy tasks (`base64_char_val`, `der_tlv_len`) | 11 | `+0.397` | `+0.375` |
| **Apple M6 (AArch64) — all unique candidates** | 31 | **`-0.266`** | `+0.072` |
| Apple M6 (AArch64) — branchy tasks (`base64_char_val`, `der_tlv_len`) | 16 | **`-0.399`** | `+0.016` |
| Combined (Zen 5 + Apple M6) | 58 | `+0.268` | `+0.461` |

**Hypothesis H3 is supported on Zen 5 (`rho = +0.707`, exceeding the pre-registered `0.4` bar) and
refuted on Apple M6 (`rho = -0.266`, inverting to `-0.399` on branchy functions).**

### 7.3 Root-Cause Diagnosis: Why `ode_tool advise` Inverted on Apple M6

Inspecting the exact AArch64 binaries where `ode_tool advise` and Apple M6 disagreed exposed two
concrete defects in `advice/estimate.py`'s whole-function static analyzer:

1. **Whole-function critical-path analysis crosses `ret` boundaries (penalizing real speedups):**
   On `der_tlv_len_arm64`, `devstral-2512` (candidate `aa4465f24bed`) cut instructions from `62` to
   `45` and ran **`1.328x` faster on Apple M6** (`1.127 ns -> 0.848 ns`). Yet `ode_tool advise`
   scored it **worse** than baseline (`compute_lower_bound` rose from `12.5` to `18.0`, predicting
   `0.694x`!). The cause: `aa4465f24bed` structured the short-form, 1-byte long-form, and 2-byte
   long-form handlers as three separate early-returning blocks (`@short_form`, `@long_form_1`,
   `@long_form_2`) that all write register `x4` and immediately execute `ret`. `advice/estimate.py`'s
   whole-function pass scanned instructions sequentially across `ret` instructions, chaining
   register dependencies across mutually exclusive paths that can never execute after one another.
2. **Flat static branch counting rewards deleting early `ret` instructions (proxy gaming):**
   On `base64_char_val_arm64`, `claude-sonnet-5.5` in Arm P1 (candidate `ae0594b63d4d`) saw
   `limiting: branch_throughput (7.0 cyc)` and deleted all 5 early `ret` instructions from the
   baseline so control fell straight through every range check to one `ret` at the bottom. Because
   `estimate.py` counts static branch/return instructions across the whole function as if every
   instruction executed once, removing 5 `ret` instructions dropped static `compute_lower_bound`
   from `7.0` to `4.5` (predicted `1.556x`, winning the P1 static objective). On real Apple M6
   silicon, removing early exits forced every ASCII character to execute every remaining branch,
   making the binary **slower (`0.935x`, `1.806 ns -> 1.932 ns`)**. Meanwhile, in Arm P0,
   `gpt-5-mini` (candidate `d12111262ec5`) kept early exits and folded each two-sided range check
   into a single unsigned range test (`sub t, b, 65; cmp t, 26; b.lo`), running **`1.549x` faster on
   Apple M6** (`1.814 ns -> 1.171 ns`) even though `advise` predicted `1.000x` (`lb = 7.0`).

### 7.4 Best Real-Silicon Speedups and Per-Model Breakdown

The first table lists the fastest verified `shown` binary found in each arm for every task on real
hardware, together with its measured speedup over the Wave 1 baseline, static lower bound,
instruction count, and winning model.

| Task | Hardware | Best Arm P0 (Blind) | Best Arm P1 (`advise` + `compare`) |
|---|---|---|---|
| `base64_char_val_x86_64` | Zen 5 | **`1.620x`** (`1.988->1.227 ns`, `lb=10.0`, 30 ins, `claude-sonnet-5.5`) | `1.537x` (`1.881->1.224 ns`, `lb=6.5`, 30 ins, `claude-sonnet-5.5`) |
| `base64_char_val_arm64` | Apple M6 | **`1.549x`** (`1.814->1.171 ns`, `lb=7.0`, 31 ins, `gpt-5-mini`) | `1.000x` (`lb=7.0`, 28 ins, `gpt-5-mini`; best static `ae0594b6` ran `0.935x`) |
| `der_tlv_len_x86_64` | Zen 5 | `1.171x` (`1.259->1.075 ns`, `lb=9.0`, 50 ins, `gpt-5-mini`) | **`1.279x`** (`1.262->0.986 ns`, `lb=10.0`, 43 ins, `devstral-2512`); also `1.254x` (34 ins, `claude-sonnet-5.5`) |
| `der_tlv_len_arm64` | Apple M6 | `1.313x` (`1.112->0.847 ns`, `lb=18.0`, 45 ins, `devstral-2512`) | **`1.328x`** (`1.127->0.848 ns`, `lb=18.0`, 45 ins, `devstral-2512`); also `1.118x` (`lb=9.0`, `gpt-5-mini`) |
| `sha256_big_sigma_4x_x86_64` | Zen 5 | `1.001x` (`lb=12.0`, 27 ins, `deepseek-v3.2`) | `1.003x` (`lb=12.0`, 27 ins, `qwen3-coder-30b`) |
| `sha256_big_sigma_4x_arm64` | Apple M6 | `1.002x` (`lb=15.0`, 27 ins, `gpt-5-mini`) | `1.000x` (`lb=15.0`, 27 ins, `qwen3-coder-30b`) |
| `adler32_s1_x86_64` | Zen 5 | `1.002x` (`lb=8.0`, 13 ins, `devstral-2512`) | `1.002x` (`lb=8.0`, 13 ins, `qwen3-coder-30b`) |
| `adler32_s1_arm64` | Apple M6 | `1.002x` (`lb=8.0`, 15 ins, `devstral-2512`) | `1.000x` (`lb=8.0`, 15 ins, `deepseek-v3.2`) |

The second table breaks down verified episodes, static lower-bound improvements, maximum real-silicon
speedup, and API spend by model across both arms (8 episodes per model per arm).

| Model | Arm P0 Verified | P0 Lower-LB Wins | P0 Max Real Speedup | P0 Cost | Arm P1 Verified | P1 Lower-LB Wins | P1 Max Real Speedup | P1 Cost |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `claude-sonnet-5.5` | 8 / 8 | 2 | `1.620x` | `$1.078` | 8 / 8 | 3 | `1.537x` | `$1.265` |
| `deepseek-v3.2` | 6 / 8 | 0 | `1.013x` | `$0.047` | 8 / 8 | 2 | **`1.357x`** | `$0.051` |
| `devstral-2512` | 6 / 8 | 0 | `1.313x` | `$0.052` | 7 / 8 | 1 | **`1.328x`** | `$0.059` |
| `gpt-5-mini` | 8 / 8 | 2 | `1.549x` | `$0.186` | 7 / 8 | 2 | `1.270x` | `$0.200` |
| `qwen3-coder-30b-a3b-instruct` | 6 / 8 | 0 | `1.002x` | `$0.043` | 6 / 8 | 0 | `1.003x` | `$0.044` |

### 7.5 Takeaways for Ode

1. **AI coders guided by a verified oracle reliably find large, proved speedups:** Without changing
   a single line of specification or verifier code, AI coders found Lean-4-verified rewrites running
   **`1.62x` faster** (`base64_char_val` on Zen 5), **`1.55x` faster** (`base64_char_val` on Apple
   M6), **`1.28x` faster** (`der_tlv_len` on Zen 5), and **`1.33x` faster** (`der_tlv_len` on Apple
   M6), cutting instruction counts by up to **54%** (`74 -> 34` instructions on `der_tlv_len_x86_64`).
2. **Cheaper models benefit most from structured advice when the model is calibrated:** On Zen 5
   (where `rho = +0.707`), `deepseek-v3.2` jumped from `0` improvements and `1.01x` max in Arm P0 to
   `8/8` verified and `1.36x` real speedup in Arm P1 for `$0.051`, and `devstral-2512` jumped from
   failing `der_tlv_len_x86_64` in Arm P0 to winning the task at `1.28x` in Arm P1 for `$0.0068`.
3. **Never optimize blindly against a static proxy that has not been checked against hardware:** The Apple M6 inversion
   (`rho = -0.266`) demonstrates why real-silicon measurement is mandatory. Fixing `advice/estimate.py`
   so whole-function analysis respects control-flow blocks (stopping dependency chains at `ret` and
   analyzing per-path cost instead of summing mutually exclusive early returns) is the immediate
   engineering follow-up.
4. **Already-tight kernels (`sha256_big_sigma_4x`, `adler32_s1`) need structural freedom to move:**
   Neither arm improved `sha256_big_sigma_4x` (already at the instruction-table lower bound) or
   `adler32_s1` (unrolling requires a multi-step `place` invariant).

### 7.6 Attempt Outcome Breakdown

Across all 160 attempts per arm:
- **Arm P0:** 88 `shown`, 46 `compile_error`, 13 `other_refused`, 7 `proof_arithmetic`, 5 `false_functional`, 1 `tool_error`.
- **Arm P1:** 92 `shown`, 39 `compile_error`, 19 `other_refused`, 8 `proof_arithmetic`, 2 `false_functional`, 0 `tool_error`.

### 7.7 Post-Experiment Fix to `advice/estimate.py` (Re-Scored on Frozen Hardware Data)

Following the diagnosis in Section 7.3, `advice/estimate.py` was updated so `static_analyze` splits
branching functions into basic blocks and evaluates each acyclic entry-to-exit path separately
(never chaining register dependencies across `ret` boundaries, and reporting per-path min, expected,
mean, and worst-case cycle lower bounds in `paths`). Straight-line functions and single-entry loops
are unchanged.

Re-scoring the exact same **58 frozen real-silicon timings** from Section 7.2 without re-running any
model or benchmark produced the calibration shift below (each cell shows Spearman `rho` between
predicted and measured speedup):

| Subset (`N`) | Pre-Fix Flat `advise` (`rho`) | Post-Fix CFG Worst-Path `advise` (`rho`) | Shift |
|---|---:|---:|---:|
| Combined Zen 5 + Apple M6 (58) | `+0.268` | **`+0.474`** | **`+0.206`** |
| Zen 5 branchy (`base64_char_val`, `der_tlv_len`, 11) | `+0.397` | **`+0.918`** | **`+0.521`** |
| Apple M6 all (31) | `-0.266` | **`+0.286`** | **`+0.552`** |
| Apple M6 branchy (`base64_char_val`, `der_tlv_len`, 16) | `-0.399` | **`+0.364`** | **`+0.763`** |

Specifically, on `base64_char_val_arm64`, the proxy-gaming variant `ae0594b63d4d` (which deleted 5
early `ret` instructions and ran `0.935x` slower on Apple M6) now scores worse on expected path cost
(`3.75` vs `2.55` cycles) rather than better (`4.5` vs `7.0`), and `der_tlv_len_arm64` `aa4465f24bed`
(`1.328x` faster on Apple M6) no longer suffers the bogus cross-`ret` `18.0`-cycle critical-path
penalty (`8.0` cycles worst-path).
