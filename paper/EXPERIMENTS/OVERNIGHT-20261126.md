# Overnight Experiment Log — 2026-11-26

This document records each pre-registered cold-room experiment run overnight, in plain language: what was tested and why, what happened (including real-silicon timings where relevant), what we learned about Ode and about our experimental process, and the concrete changes made before the next iteration.

Every experiment below runs in an isolated git worktree with a pre-registered commit containing BLAKE3 hashes of the task specification, instruction tables, quickstart, and verifiers before any model API call starts. Apple M6 timings are measured on a local Mac that is not reserved and under no timing lock; AMD Zen 4 timings are pinned with `taskset -c 2` on the x86-64 workhorse.

---

## Iteration 1: `suite-v6` — Evaluating Zero-Boilerplate `place` and `suite-v5` Diagnostics

- **Design:** Re-run the exact 16-cell `suite-v5` benchmark (`header_score`, `ebpf` × 4 models × `x86_64`, `arm64`) on commit `be0ddc9f` (which introduced auto-bound `reg` aliases and 64-bit hardware registers inside `place { ... }`, plus concrete `need below` and `stack` diagnostics) against `results-suite-v5.json`.
- **Pre-registration / Results:** [`prereg-suite-v6.md`](prereg-suite-v6.md), [`results-suite-v6.md`](results-suite-v6.md) (commit `d48b45cd`).
- **Headline results:**
  - Strict pass rate rose from **11/16** (`54` rounds, `$13.83`) to **12/16** (`44` rounds, `$13.19`), with **12/12** dual-verified by `verify2.py` and **12/12** passing on real silicon.
  - **`header_score` reached 8/8 (100%)** (up from 6/8 in `suite-v5`): `claude-sonnet-5.5`, which had failed both targets in `suite-v5` with zero join points on `need below`, inserted 16 zero-boilerplate join points and passed both `x86_64` (Round 2, `$0.17`) and `arm64` (Round 4, `$0.28`).
  - **Zero-boilerplate `place` adoption:** **15/16** cells (and **12/12** passing cells) wrote zero `name x = reg` lines inside `place { ... }`.
  - **`ebpf` (4/8 vs. 5/8 in `suite-v5`):** `claude-fable-5.2` on `arm64` dropped from Round 4 (`$2.73`, 220 insns) to **Round 1 (`$0.90`, 193 insns)**; all four failing `ebpf` cells stopped at the 900 s wall-clock cap after repeated `prover_timeout_120s` rounds.
- **What we learned & changed:**
  - **Ode (`190cac74`):** 21 of 32 failing rounds in `suite-v6` (and 28 of 51 in `perf-v1`) were 120-second prover timeouts from deep unfolding or cross-goal backtracking. Fixed `proof-core/prove.py` to track `furthest_root` (stopping backtracking into already-closed `spec` goals) and fail fast at depth 14 with an actionable mid-loop `place { ... }` proof-cut diagnostic in `lang/ode_tool.py` (`perf-v1`'s 32× loop dropped from `120.0 s` timeout to `2.8 s`). Also added `b.hi`/`b.ls` macro-op fusion on Apple M-series in `advice/uica_sim.py`.
  - **Experimental process:** 21 × 120 s timeouts wasted 45+ CPU-minutes of wall clock. Prepared harness speedups for Iteration 3 (`--tool-timeout 45`, `--workers 16`, `--prover-slots 10`, multiplexed SSH in x86-64 native runner).

---

## Iteration 2: `perf-v2` — Compute-Heavy Optimization A/B (`weighted_sum`, Adler-32 Inner Loop)

- **Design:** Controlled A/B test (`blind` vs. `advised`, 3 optimization rounds after first verified pass, 16 cells across 4 models × 2 targets) on a new unseen compute-heavy constant-time task `weighted_sum` (`s1 += a[i]`, `s2 += s1`, `requires n <= 4096`, `stack 0`, canonical ID `dlj5zmyx5h52zjp64x66mwebhrwevsttwvvbbgujxktxk6eat4vq`), running on `190cac74`. Unlike `byte_sum` (load-pipe bound), `weighted_sum` has a 2-cycle serial `s1 -> s2` dependency chain that rewards algebraic unrolling and parallel accumulators.
- **Pre-registration / Results:** [`prereg-perf-v2.md`](prereg-perf-v2.md), [`results-perf-v2.md`](results-perf-v2.md).
- **Headline results:**
  - **15/16 strict passes** (**8/8 = 100%** `advised`, **7/8** `blind`), **15/15** native CPU pass (`112/112` vectors), **$23.76 USD**, 32 min wall clock.
  - **Real-silicon speedups (`n = 4,096` B):**
    - **Apple M6** *(local Mac, not reserved and under no timing lock)*: `870.8 ns` (1 B/it) → **`312.6 ns`** (`2.79x`, `gemini-4-neon advised`). `advised` beat `blind` on **all four models** (`312.6` vs. fail; `325.6` vs. `342.0`; `343.2` vs. `366.6`; `375.8` vs. `379.1 ns`).
    - **AMD Zen 4:** `1,372.0 ns` (1 B/it) → **`530.0 ns`** (`2.59x`, `gpt-6.2-astra-pro advised`, which discovered a dual even/odd accumulator identity `s2 = 2*erun + 2*orun - odd` with a zero-instruction mid-loop proof cut at byte 8 — **10.9% faster** than `blind`'s `587.7 ns`). `claude-fable-5.2 advised` (`631.9 ns`) also beat `blind` (`684.1 ns`, **8.3% faster**).
- **What we learned & changed:**
  - **Static performance model (`advice/uica_sim.py`):** Comparing Zen 4 timings against predictions exposed three simulator bugs: (1) scheduler queues used FIFO `deque`s instead of out-of-order min-heaps (`heapq`); (2) AMD Zen's separate AGU scheduler was merged into the integer ALU scheduler, causing artificial stalls on 16 B/it loops; and (3) a 4-iteration steady-state window aliased period-3 schedules (`[15, 8, 8, 15]`). Fixing all three cut `gpt-6.2-astra-pro advised` Zen 4 error from `+23.4%` to **`+6.2%`** while holding 7-CPU PMU calibration at **132/169 (78.1%)**.
  - **Independent second verifier (`proof-core/verify2.py`):** `gpt-6.2-astra-pro`'s subtraction fact inside `place` (`erun + erun + orun + orun - odd`) showed `verify2.py`'s `assume_fact` omitted the proof stream parameter (`14/15 -> 15/15` verified after fix).
  - **Prover fast-fail worked:** Timeouts dropped by half vs. `perf-v1` (`14/44` vs. `28/51`), and three models used mid-loop `place` proof cuts directly after seeing the new `o 14` diagnostic.
  - **Experimental process:** 32 min wall clock came from `--workers 6` serializing 16 cells into 3 waves, `120 s` prover timeouts burning 40 CPU-minutes, and 5 cold SSH handshakes per x86-64 native run. Fixed all three before Iteration 3 (`--workers 16`, `--prover-slots 10`, `--tool-timeout 45`, `--cell-timeout 540`, SSH ControlMaster multiplexing + tar transfer).

---

## Iteration 3: `der-v1` — Brand-New Complex Contract (`der_valid`) Across Expanded 7-Model Panel

- **New contract (zero prior Ode implementation anywhere in the repo):** `der_valid` (`pyqksm2d6u3quuwvpwjwr4j4kgmgy7zlqjixoqobp2gr24sggfma`) — an ASN.1 / X.690 DER canonical TLV validator with nested `SEQUENCE` containers up to depth 3 (`BOOLEAN`, `INTEGER` minimal two's-complement prefix, `BIT STRING` unused-bit mask, `OCTET STRING`, `NULL`, `OBJECT IDENTIFIER` canonical base-128 loop, short/0x81/0x82 minimal lengths).
- **Way-A reference verification & first-contact friction log (recorded honestly before launching models):**
  - Dual-arch 8-function reference (`x86_64`: 407 insns, 1,555 B, 9.9 s; `arm64`: 435 insns, 1,776 B, 20.4 s) passed `ode pack`, `ode audit`, `verify2.py` (8/8 functions), and `NATIVE_PASS 257/257` on both real CPUs with zero quickstart leakage.
  - **Five concrete Ode gaps exposed while writing this brand-new program:**
    1. *Fixed:* `verify2.py` did not support nested `ifx` conditions (`&&`/`||` in specs).
    2. *Fixed:* `verify2.py` did not yet support verified tail calls (`jmp callee` / `b callee`).
    3. *Fixed:* `verify2.py`'s `assume_fact` lacked the proof stream for subtraction facts in `place`.
    4. *Logged for follow-up:* `kcheck/ode.py` parses `&` in specs, but `Core.lean` refuses scalar `&` (`no rule for &`; `b % 2^k == 0` works cleanly and is proved by `and r, mask`).
    5. *Logged for follow-up:* `statement.py` / `Core.lean` currently accept only constant `stack C` or logarithmic `stack C + D * bits(...)`, not linear `stack C + D * depth`, and do not yet carry return-value range bounds (`ensures result <= 4`) across calls; so bounded recursion peels into `der_seq0..der_seq3` and length decoding uses an in-loop join-point `place`.
- **Expanded 7-model panel:** Original 4 proprietary models + 2 open-weights models (`qwen/qwen3.8-2.4t-a95b`, `moonshotai/kimi-k3.1-pro`) + 1 fast/cheap proprietary model (`anthropic/claude-haiku-5.5`, `$0.10/$0.50` per M tokens).
- **Pre-registration / Results:** [`prereg-der-v1.md`](prereg-der-v1.md), [`results-der-v1.md`](results-der-v1.md) (baseline on `bf49b6f`, which had just fixed `prove.py` join-point `keep` pre-seeding, cutting `der_valid` `arm64` proving from `>120 s` timeout to `5.04 s` and `x86_64` from `9.87 s` to `4.10 s`).
- **Headline results (14 min wall clock, 80 rounds, `$21.16` USD):**
  - **3/14 strict passes** on first contact with this hard 8-function contract (**3/3 `NATIVE_PASS 257/257`** on real CPUs):
    - `google/gemini-4-neon` passed **both** targets: `arm64` in Round 3 (`$0.81`, 10 fns / 399 insns) and `x86_64` in Round 5 (`$1.40`, 7 fns / 431 insns).
    - `openai/gpt-6.2-astra-pro` passed `x86_64` in Round 8 (`$4.78`, 6 fns / 395 insns, `verify2.py` shown).
  - Cost of fast/cheap & open-weights models was tiny: `claude-haiku-5.5` ran 16 rounds across both arches for `$0.13` total (`$0.008/round`); `kimi-k3.1-pro` ran 16 rounds across both arches for `$1.05` total (getting all the way into `der_prim_ok` and `der_seq` on Round 1!).
- **What we learned & changed before Iteration 4 (`der-v2`):**
  1. **Critical harness artifact caught by post-run autopsy (fixed in `run_suite.py`):** The isolated `der-v1` worktree copied `odeverify` but omitted `odeprove` and `odespec`. Without `odeprove`, `prove.py` spawned a subprocess per proof step (5x–10x slower, triggering all 9 `prover_timeout` failures) and `locate()` returned no source locations, blinding all 7 models with raw vector-indexed `f 0 0 ... 1` / `need held c 0` dumps instead of `ode pack`'s source-located `cannot show:` hints. `run_suite.py`'s `self_test_cli` now refuses to start if any of `odeverify`, `odeprove`, or `odespec` is missing.
  2. **Prover backtracking & diagnostic bugs (`proof-core/prove.py`):** Post-run traces with `odeprove` restored revealed two genuine prover bugs: (a) hitting a hard non-spec refusal (like a stack-slot trace mark violation in `claude-fable-5.2`'s `seq1`) did not stop backtracking through `need held` / `need spec`, exploding to 6,748 asks and overwriting the real refusal with `refused: the value held is of another use`; and (b) backtracking to the entry-call `t open 0` overwrote deep arithmetic failures (`add x7, x7, x9` overflow) with shallow bogus goals (`start >= end`). Fixed both with `hard_refusal` short-circuiting and `best_last` (preserving the deepest partial proof).
  3. **Four `verify2.py` completeness gaps (fixed; `der-v1` now 3/3 dual-verified):** Re-running `verify2.py` on `gemini-4-neon`'s passing `arm64` and `x86_64` binaries exposed right-to-left `argumentV` ordering, `same_call` reachability through `eqs`, `place 0` entry execution order, and resetting `visited_places` across `jstack` on loop generalization. All four fixed; `der-v1` rose from `1/3` to **3/3** dual-verified (`test_verify2.py` 8/8 OK).
  4. **Open-weights reasoning cap (`qwen/qwen3.8-2.4t-a95b`):** `qwen3.8-2.4t-a95b` ignored `reasoning: {"effort": "medium"}` and hit the 32,000-token output ceiling twice in a row (~370 s/round, 0 code emitted). OpenRouter probing showed `reasoning: {"max_tokens": 8192}` caps Qwen's thinking cleanly (`finish_reason: "stop"`). Added to `run_suite.py` and raised `--cell-timeout` from `540 s` to `720 s` so slower frontier models (`claude-fable-5.2`) complete 6–8 rounds.
  5. **SHA-256 foundation verified in Lean 4 + real silicon (ready for Iteration 5):** Added `pand128` (`core/x86.tab`, `core/cross.py` 94 rows / 5,000 instances / 0 differ on AMD Zen 4), `and_v` (`arm64/arm64.tab`, `arm64/cross.py` 48 rows / 1,920 instances / 0 differ on Apple M6), `and32` + `&` + `>>` across `Machine.lean`, `Contract.lean`, `Core.lean`, `Sound*.lean` (`test_sound.py` 2/2 OK in `0.659 s`, zero `sorry`, unchanged 11 top-level theorems), `kcheck/ode.py`, and `advice/`. Verified `paper/EXPERIMENTS/tasks/sha256_4way_spec.ode` bit-for-bit against NIST FIPS 180-4 SHA-256 vectors (`""`, `"abc"`, two-block, and 4-block batch).

---

## Iteration 4: `der-v2` — Re-Running `der_valid` Across All 7 Models With Full Diagnostics, Fixed Prover, and Qwen Reasoning Cap

- **Hypothesis (pre-registered):** Restoring `odeprove` source-located diagnostics + `prove.py` `hard_refusal`/`best_last` + Qwen `reasoning.max_tokens = 8192` + `720 s` cell cap should substantially lift strict pass rate on `der_valid` above `der-v1`'s `3/14`, bring `qwen/qwen3.8-2.4t-a95b` from 0% code emission to active multi-round verification, eliminate `verify2.py` refusals on passing cells, and sharply cut `prover_timeout` rounds.
- **Status:** Launching now (`14` cells = 7 models × 2 targets, baseline `results-der-v1.json`). While `der-v2` runs in the background, work proceeds in parallel on the `sha256_4way` dual-arch reference + native NIST benchmark harness and hardware SHA-NI / ARMv8.2 SHA2 instructions.

