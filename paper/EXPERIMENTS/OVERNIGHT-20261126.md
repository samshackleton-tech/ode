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
    - **Apple M6** *(local unreserved Mac caveat)*: `870.8 ns` (1 B/it) → **`312.6 ns`** (`2.79x`, `gemini-4-neon advised`). `advised` beat `blind` on **all four models** (`312.6` vs. fail; `325.6` vs. `342.0`; `343.2` vs. `366.6`; `375.8` vs. `379.1 ns`).
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
- **Status:** Launching now (`14` cells = 7 models × 2 targets). Results and learnings will be appended here upon completion.
