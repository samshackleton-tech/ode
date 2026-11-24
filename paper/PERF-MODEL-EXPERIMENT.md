# Performance-Modeling Experiment (Pre-Registered)

*Status: pre-registered before live model runs (November 24, 2026).*

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

*(To be appended verbatim after live runs and real-hardware timing complete.)*
