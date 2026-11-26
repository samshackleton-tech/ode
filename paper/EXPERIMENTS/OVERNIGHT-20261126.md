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
- **Pre-registration / Results:** [`prereg-der-v2.md`](prereg-der-v2.md), [`results-der-v2.md`](results-der-v2.md) (pre-reg commit `04cb59aa`, baseline `results-der-v1.json`).
- **Headline results (12 min wall clock, 77 rounds, `$18.55` USD — `$2.61` cheaper than `der-v1`):**
  - **Strict pass rate more than doubled:** `3/14` → **`7/14` (`+4`)**, reaching **7/8 (87.5%)** on the four frontier models:
    - `google/gemini-4-neon`: **2/2** (`arm64` Round 2, `$0.58`, 9 fns / 350 insns; `x86_64` Round 3, `$0.77`, 5 fns / 365 insns) — `$1.35` combined.
    - `openai/gpt-6.2-astra-pro`: **2/2** (`arm64` Round 3, `$1.71`, 7 fns / 347 insns; `x86_64` Round 6, `$3.19`, 5 fns / 338 insns).
    - `anthropic/claude-fable-5.2`: **2/2** (`arm64` Round 3, `$2.49`, 9 fns / 358 insns; `x86_64` Round 6, `$4.58`, 9 fns / 421 insns).
    - `anthropic/claude-sonnet-5.5`: **1/2** (`arm64` Round 8, `$1.52`, 9 fns / 428 insns; `x86_64` ran 8 rounds for `$1.29`, ending at `arith_need_entail` on `lea r8, [rdx + 2]` inside `seq0`).
  - **Independent second verifier (`verify2.py`):** `1/3` → **`7/7` (100% dual-verified)**.
  - **Real-silicon native harness:** **`7/7` (`NATIVE_PASS 257/257`)**.
  - **Targeted failure reductions:** `prover_timeout` dropped `9` → **`1` (`-8`)**; `spec_need_open` (`need held c 0`) dropped `15` → **`0` (`-15`)**.
  - **Fast/cheap & open-weights models (`0/6`, `$2.41` combined):** `claude-haiku-5.5` (`$0.12` across 16 rounds), `kimi-k3.1-pro` (`$1.21` across 16 rounds), and `qwen3.8-2.4t-a95b` (`$1.08` across 6 rounds; `x86_64` emitted real `.ode` for 4 rounds before hitting the `720 s` cell cap, while `arm64` hit `output_token_limit` twice) all parsed into Ode and reached real proof obligations (`arith_need_entail`, `kept_reg_refusal`). `der_valid` separates frontier reasoning (87.5%) from small/open-weights models (0%) without saturating.

---

## Iteration 5: Hardware SHA-NI & ARMv8.2 SHA2, 397× Verifier Speedup, and `sha256-v1` Performance A/B

- **Goal:** Build a wide-dynamic-range cryptographic benchmark (`sha256_4way`: four independent 64-byte SHA-256 block compressions against NIST FIPS 180-4) with a 6×–8× performance span between scalar/SIMD software (`~1,500–2,000+` cycles), single-block hardware crypto (`~512–560` cycles, latency-bound on the 4-cycle crypto chain), and 2-way+ interleaved hardware crypto (`~259–283` cycles, saturating the physical execution-port floor).
- **Hardware instructions added, silicon-tested, and proved sound in Lean 4:**
  - **x86-64 (`core/x86.tab`, `core/asm.py`, `core/conc.py`):** `palignr4`, `palignr8`, `palignr12` (`vpalignr`), `sha256rnds2`, `sha256msg1`, `sha256msg2`. Real AMD Zen 4 hardware cross-check (`core/cross.py`): 100 rows, 2,000 assembler + 3,240 table instances, **0 differ**; decoder 970/970, **0 differ**.
  - **AArch64 (`arm64/arm64.tab`, `core/conc.py`):** `sha256h`, `sha256h2`, `sha256su0`, `sha256su1`, plus self-OR register copy (`mov vD.16b, vS.16b` via `or32 x x = x`). Real Apple M6 hardware cross-check (`arm64/cross.py`): 52 rows, 2,080 instances, **0 differ**.
  - **Lean 4 soundness (`proof-core/*.lean`):** Full `lake build && python3 test_sound.py -v` passed (**55/55 jobs, 2/2 soundness checks OK in `0.656 s`**), zero `sorry`, zero `maxHeartbeats`, standard axioms only (`[propext, Classical.choice, Quot.sound]`), all 11 top-level theorem statements unchanged. `lang/test_asm.py` (8/8 OK) byte-for-byte cross-checked every `.ode` file in the repository—including dual-arch `sha256_4way_reference.ode`—against `clang`.
- **Major Ode verifier breakthrough (397× speedup on SHA-256):**
  - First-contact verification of full 256-round 4-way SHA-256 exposed a Fibonacci duplicate-term blowup in `proof-core/Core.lean`'s `Node.add (xs : List Nat)`: SHA-256's coupled `e' = d + t1`, `a' = t1 + t2` sums duplicated shared sub-terms across rounds into 65,536-entry lists (`117.43 s` on ARM64, `80.74 s` on x86-64).
  - Replaced `Node.add` with a sparse modular linear combination `List (Nat × Nat)` merged in O(N) via `mergeAdd` (mod $2^{32}$, dropping zero coefficients), and added O(1) word-list slicing (`hs[0..8]`) in `Core.lean` + `SoundWord.lean` + `SoundSpecW.lean` + `SoundCallL.lean` (all Lean-proved).
  - Result: full 4-way 256-round hardware SHA-256 (`sha256_4way_reference.ode`) verification dropped from **`117.43 s` → `0.296 s` (397× faster)** on ARM64 (433 insns, 1,732 B) and from **`80.74 s` → `0.347 s` (233× faster)** on x86-64 (625 insns, 3,083 B).
- **Real-silicon micro-probes and static performance model calibration (`advice/`):**
  - **Apple M6 (`4.786 GHz`, local Mac, not reserved and under no timing lock):** `and_v` lat 2.00 / rTP 0.25; `sha256h`/`sha256h2` lat 4.00 / rTP 2.00; `sha256su0` lat 2.00 / rTP 1.00 (confirmed 0.00-cycle contention with `sha256h`, independent crypto pipe); `sha256su1` lat 3.00 / rTP 1.00.
  - **AMD Zen 4 (`5.054 GHz`, `taskset -c 2`):** `vpalignr` lat 1.99 / rTP 0.50; `sha256rnds2` lat 3.98 / rTP 1.00; `sha256msg1` lat 2.99 / rTP 0.65; `sha256msg2` lat 4.13 / rTP 2.00.
  - **Straight-line simulation validation vs. real silicon (`sha256_4way_reference.ode`, `NATIVE_PASS 264/264` NIST FIPS 180-4):**
    - **Apple M6** *(local Mac, not reserved and under no timing lock)*: **`54.11 ns`** per 4 blocks (`256 B`) = **`4.406 GiB/s`** (`259.0 cyc` measured, **98.8%** of the `128 × 2.0 = 256.0 cyc` physical port floor) vs. `ode advise` **`261.0 cyc`** (**`+0.8%` error**, bottleneck `ports:V0` at `98%`).
    - **AMD Zen 4 (`taskset -c 2`):** **`56.04 ns`** per 4 blocks (`256 B`) = **`4.255 GiB/s`** (`283.2 cyc` measured) vs. `ode advise` **`269.0 cyc`** (**`-5.0%` error**, bottleneck `ports:FP0` at `89%`).
- **Way-A friction points logged while building `sha256_4way_reference.ode`:**
  1. *Fixed:* `Node.add` Fibonacci blowup (`117 s` → `0.296 s` via Lean-proved `mergeAdd`).
  2. *Fixed:* `ARM_WHOLE` in `lang/odec.py` needed `q0..q31` (for `ldr q0` / `sha256h q0`) without shadowing ChaCha20's `d0` parameter name, and `odec.assemble` needed `-march=armv8-a+crypto` for `clang` cross-checks.
  3. *Fixed:* `advice/estimate.py` had no straight-line `whole_sim` / `--all-archs` reporting for unrolled cryptographic kernels without loops.
  4. *Known scope boundary (stated in pre-registration):* `proof-core/verify2.py` covers the scalar byte/integer contract fragment and does not yet implement word-vector `ensures out = bytes_of(...)` contracts; `sha256-v1` marks `verify2.py` as `n/a` honestly while running full Lean `ode audit` (`VERDICT: shown`) and `NATIVE_PASS 264/264` NIST FIPS 180-4 vectors on real silicon.
- **Experiment design (`sha256-v1`):** Controlled A/B performance experiment (`blind` vs. `advised`, `--max-rounds 8`, `--opt-rounds 4`, 7 models × 2 targets × 2 arms = **28 cells**, canonical IDs `o3hgxtczokkzp7r2eaybjvdgc4cyrny6vawtweqxrzmxu32hrswa` on `arm64` and `2wohv4skh4liyco6pegmuwcvelhqew4xgp7gbki4hrg44azweuda` on `x86_64`, `stack 512` so both zero-stack interleaved hardware kernels and stack-spilled 4-way kernels are admitted on equal footing).
- **Pre-registration / Results:** [`prereg-sha256-v1.md`](prereg-sha256-v1.md), [`results-sha256-v1.md`](results-sha256-v1.md) (pre-reg commit `1c722390`).
- **Headline results (23 min wall clock, 186 rounds, `$55.55` USD):**
  - **21/28 strict passes (75%)**, **16/16 (100%)** on all four frontier models (`gpt-6.2-astra-pro`, `claude-fable-5.2`, `gemini-4-neon`, `claude-sonnet-5.5`), and **all 7 models** passed at least once — including `$0.06` `anthropic/claude-haiku-5.5` (2/2 on `arm64`) and both open-weights models (`qwen/qwen3.8-2.4t-a95b` 1/2 `arm64`, `moonshotai/kimi-k3.1-pro` 2/2 `arm64` — `0/6` on `x86_64` for small/open models because `sha256rnds2`'s implicit `xmm0` register constraint is harder to schedule than AArch64's orthogonal 3-operand `sha256h`).
  - **21/21 `NATIVE_PASS 264/264`** NIST FIPS 180-4 vectors on real silicon (`verify2.py` `n/a` for word-vector contracts).
- **Real-silicon benchmark results (all 21 passing binaries vs. `ode advise` static sim):**
  - **Apple M6 (`4.786 GHz`, local Mac, not reserved and under no timing lock — caveat applies to all M6 timings below):**
    - `ode advise` achieved **`1.4%` MAE** across all 11 passing `arm64` binaries (`-1.7%` to `+5.3%`; 10/11 within `±1.9%`).
    - Fastest binaries: **`claude-haiku-5.5 advised`** (`$0.07` total!) hit **`53.54 ns` (`256.2 cyc`, `4.453 GiB/s` = `99.9%` of the `256.0 cyc` physical port floor)**; `kimi-k3.1-pro advised` hit `53.55 ns` (`4.453 GiB/s`); `claude-sonnet-5.5 advised` hit `53.65 ns` (`4.444 GiB/s`); `gpt-6.2-astra-pro advised` hit `53.66 ns` (`4.444 GiB/s`); `claude-fable-5.2 blind` hit `53.83 ns` (`4.429 GiB/s`); reference `54.12 ns` (`259.0 cyc`, `4.406 GiB/s`).
    - Slowest passing `arm64` binary: `qwen3.8-2.4t-a95b advised` (`54.73 ns`, still 4-way interleaved!). Nearly every passing `arm64` model independently discovered 2-way or 4-way interleaving even in `blind`, collapsing the `advised` vs. `blind` gap on `arm64` to `< 1%`.
  - **AMD Zen 4 (`5.054 GHz`, `taskset -c 2`) — and a causal `1.81×` (`+200 cyc`) microarchitectural discovery:**
    - Reference (zero-stack 2-way interleaved, 625 insns): **`54.69 ns` (`276.4 cyc`, `4.359 GiB/s`)**.
    - **`claude-fable-5.2 blind`** beat the hand-tuned reference: **`49.46 ns` (`250.0 cyc`, `4.821 GiB/s`)** using a 4-way stack-spilled schedule (`sub rsp, 264`, 16-byte aligned).
    - **`gpt-6.2-astra-pro blind`** emitted `sub rsp, 192` — leaving `rsp % 16 == 8` after System V ABI entry! Its 108 16-byte vector stack loads/stores (`movdqu [rsp + 16*k]`) split 64-byte cache lines and triggered Store-to-Load Forwarding (STLF) replay stalls, running in **`89.46 ns` (`452.1 cyc`, `2.665 GiB/s`)**.
    - **Causal ablation (changing one immediate, `sub rsp, 192` → `sub rsp, 200`):** identical instruction stream, identical verification (`shown`), **`89.46 ns` → `49.36 ns` (`249.5 cyc`, `4.830 GiB/s` = `1.81×` faster, `+10.8%` faster than our hand-tuned reference!)**. Applying the same 16B stack alignment to `claude-fable-5.2 blind` (`sub rsp, 264`) reached **`48.99 ns` (`247.6 cyc`, `4.867 GiB/s`, `+11.7%` vs. reference)**; `gemini-4-neon advised` reached `49.69 ns` (`4.798 GiB/s`); `gpt-6.2-astra-pro advised` reached `50.35 ns` (`4.735 GiB/s`).
  - **Turning the benchmark finding into a permanent static-model upgrade (following Sam's benchmark rule):**
    - Added **`hint [stack-align]`** to `advice/estimate.py`: tracks `rsp % 16` from System V ABI entry (`rsp % 16 == 8`) across `sub rsp`/`add rsp`/`push`/`pop` and flags any 16B/64B stack load/store executing misaligned, suggesting the exact `+8` frame adjustment (`sub rsp, 200` instead of `192`). Verified directly against `gpt-6.2-astra-pro`'s binary (108 misaligned vector spills detected; 0 false positives on aligned kernels).

---

## Iteration 6: Hardware Constant-Time Select (`cmov*`/`csel`), 3 General Core Verifier Upgrades, and `ct-b64-v1`

- **Goal:** Exercise true constant-time data processing (`trace depends on n`, zero data-dependent branches or table lookups) combined with a non-1:1 output-writing loop (`ct_base64_decode`: 256 Base64 characters → 192 decoded bytes + constant-time RFC 4648 validity bit).
- **Hardware instructions added, silicon-tested, and proved sound in Lean 4:**
  - **x86-64 (`core/x86.tab`, `core/asm.py`, `core/conc.py`):** `cmove64_rr`, `cmovne64_rr`, `cmovb64_rr`, `cmovae64_rr`, `cmova64_rr`, `cmovbe64_rr` (6 conditional moves). Real AMD Zen 4 hardware cross-check (`core/cross.py`): 106 rows, 2,120 assembler + 3,360 table instances, **0 differ**; decoder 4,120/4,120, **0 differ**.
  - **AArch64 (`arm64/arm64.tab`, `arm64/cross.py`, `core/conc.py`):** `csel_eq`, `csel_ne`, `csel_lo`, `csel_hs`, `csel_hi`, `csel_ls` (6 conditional selects; `arm64/cross.py` upgraded to test real live `zf`/`cf` flag states). Real Apple M6 hardware cross-check: 58 rows, 4,640 instances, **0 differ**.
  - **Lean 4 soundness (`proof-core/*.lean`):** Full single-run mark-tracked `RunsOk → TraceOk` soundness proof (`SoundTop.lean`) for functions using `.select` (`cmov*`/`csel`), keeping the existing two-run proof for non-`select` functions (`verdictFrom_trace_sound` dispatches cleanly on `hasSelect f.code`). Independent dual verifier `proof-core/verify2.py` also updated (`test_verify2.py` **9/9 OK** in `28.5 s`, including positive x86-64/arm64 `cmov`/`csel` verification and negative refusal when branching on the selected result).
- **Three general core verifier limitations uncovered by Way-A reference construction (all fixed & Lean-proved rather than documented as gotchas):**
  1. *Fixed (`Core.lean` + `SoundCall.lean`):* `Sym.afterCall` cleared `range := none` even across plain callees that write no caller output buffer, breaking any loop `wrote out[.. k]` invariant that calls a helper inside the loop. Preserved `range := s.range` across plain calls and proved `afterCall_wf` / `afterCall_holds`.
  2. *Fixed (`Core.lean` + `SoundMarks.lean`):* `cellsAfterSize` wiped stack-frame trace marks (`s.q.fq`) on every store to an output buffer at a symbolic loop index (causing saved `x30` on AArch64 to fail on loop back-edges). Now preserves `s.q.fq` whenever `size == 1` and `(w, o, _)` is recorded in `s1.wrote` (already bounds-proved by `C.holds.wrote` and disjoint from the frame by `E.out`).
  3. *Fixed (`Core.lean` + `Advice.lean` + `SoundStep.lean` + `SoundTrace.lean` + `prove.py` + `verify2.py`):* `readByte` previously matched buffer reads only by syntactic offset equality (`o' = o`), failing on non-1:1 byte transforms (`4*(j/3)` vs. `in_idx` in Base64 4:3, Hex 2:1, Base32 8:5). Added optional proof-file unification `t samebyte <v>` / `t newbyte 0` (`popSameByte`), gated in `Advice.lean` to non-constant offsets with distinct variable coefficients so constant-offset spec search pays zero overhead.
  4. *Fixed (`advice/estimate.py`):* Measuring `ct_base64_decode_reference.ode` on real silicon exposed that `ode advise`'s loop simulator counted in-loop `call` instructions as 1 uop (`~10 cyc/iter`) while real silicon took `~38 cyc/iter` (Zen 4) and `~20.5 cyc/iter` (Apple M6) across the 4 `call b64_char` sites. Added `hint [loop-calls]` and explicit `excludes N callee(s)` annotation to `ode advise`.
  5. *Full Lean verification after all 4 upgrades:* **`lake build && python3 test_sound.py -v` passed (55/55 modules, 2/2 soundness checks OK in `0.655 s`)**, zero `sorry`, zero `maxHeartbeats`, standard axioms only (`[propext, Classical.choice, Quot.sound]`), all 11 top-level theorem statements unchanged. `lang/test_asm.py` 8/8 OK; `advice/test_estimate.py` 12/12 OK; `proof-core/test_verify2.py` 9/9 OK; `paper/EXPERIMENTS/test_run_suite.py` 2/2 OK.
- **Way-A reference (`ct_base64_decode_reference.ode`, canonical contract ID `5ibuszg65c23xbxdcscfcsjfpw3w3xju3hi672yvtmecj7y7e2dq` on both arches):**
  - `x86_64`: 2 fns, 123 insns, 446 B, `ode pack` `shown` in `15.5 s`, `ode audit` `shown`, **`NATIVE_PASS 333/333`**, real AMD Zen 4 (`taskset -c 2`) **`480.71 ns/256B` (`0.496 GiB/s`)**.
  - `arm64`: 2 fns, 108 insns, 432 B, `ode pack` `shown` in `27.9 s`, `ode audit` `shown`, **`NATIVE_PASS 333/333`**, real Apple M6 *(local Mac, not reserved and under no timing lock)* **`273.91 ns/256B` (`0.870 GiB/s`)**.
  - `check_quickstart_leakage`: 0 leaks. (`skip_verify2: true` stated honestly in pre-registration because `verify2.py` does not yet implement fixed-size output buffers `arg a0 out 192` / `wrote out[.. k]`.)
- **Experiment design (`ct-b64-v1`):** Controlled A/B experiment (`blind` vs. `advised`, `--max-rounds 8`, `--opt-rounds 3`, 7 models × 2 targets × 2 arms = **28 cells**, `--max-usd 60`, `--workers 16`, `--prover-slots 10`).
- **Pre-registration / Results:** [`prereg-ct-b64-v1.md`](prereg-ct-b64-v1.md), [`results-ct-b64-v1.md`](results-ct-b64-v1.md) (pre-reg commit `947b6759`).
- **Headline results (18 min wall clock, 202 rounds, `$33.33` USD):**
  - **6/28 strict passes (21.4%)**, showing a sharp architectural asymmetry on frontier models: **5/8 on `arm64`** (`claude-fable-5.2` 2/2, `gpt-6.2-astra-pro` 2/2, `claude-sonnet-5.5` 1/2 `advised`) vs. **1/8 on `x86_64`** (`claude-fable-5.2` `advised`). Small/open-weights models scored `0/12`, confirming `ct_base64_decode` is a high-headroom frontier discriminator.
  - **Real-silicon native harness:** **6/6 `NATIVE_PASS 333/333`** on matching hardware.
  - **Real-silicon throughput results (initial pass → final optimized pass, all 6 passing binaries):**
    - **Apple M6 (`4.786 GHz`, local Mac, not reserved and under no timing lock — caveat applies to all M6 timings below):**
      - Hand-written reference (`2 fns`, `108 insns`): **`273.91 ns/256B` (`0.870 GiB/s`)**.
      - **`claude-fable-5.2 arm64 blind`**: initial R5 (`2 fns`, `115 insns`) `311.06 ns` (`0.766 GiB/s`) → R7 inlined all 4 character decodes into **1 function (`131 insns`) using 4 acyclic join `place`s (`@j0..@j3`)** to merge `csel` paths → **`256.43 ns/256B` (`0.930 GiB/s`, `+21.3%` over R5, `+6.8%` faster than our hand-written reference!)**.
      - `gpt-6.2-astra-pro arm64 blind`: `277.13 ns` (`0.860 GiB/s`, `2 fns`, `98 insns`); `gpt-6.2-astra-pro arm64 advised`: `280.72 ns` (`0.849 GiB/s`, `2 fns`, `97 insns`); `claude-sonnet-5.5 arm64 advised`: `281.60 ns` (`0.847 GiB/s`, `$0.67`); `claude-fable-5.2 arm64 advised`: `310.94 ns` (`0.767 GiB/s`, hit 45 s prover timeout on R7 inlining attempt).
    - **AMD Zen 4 (`5.054 GHz`, `taskset -c 2`):**
      - Hand-written reference (`2 fns`, `123 insns`): **`480.71 ns/256B` (`0.496 GiB/s`)**.
      - **`claude-fable-5.2 x86_64 advised`**: initial R3 (`2 fns`, `127 insns`) `576.86 ns` (`0.413 GiB/s`) → received `hint [loop-calls]` → R5 inlined all 4 character decodes into **1 function (`167 insns`, `6.00 cyc/B`)** → **`460.32 ns/256B` (`0.518 GiB/s`, `+25.3%` over R3, `+4.4%` faster than our hand-written reference!)**.
- **Failure autopsy & root cause of the `arm64` (5/8) vs. `x86_64` (1/8) frontier gap:**
  - Across all 46 `other` failing rounds, **24/46 (52%)** traced to two concrete x86-64-skewed verifier limitations:
    1. **`15×` `a function using conditional select can only call standard-ABI helpers`:** `gpt-6.2-astra-pro` (both `x86_64` cells), `gemini-4-neon`, and `claude-sonnet-5.5` naturally factored out a custom-calling zero-clobber helper (`calling { in ... out ... preserves ... }`) to avoid register pressure across calls — especially critical on x86-64 (6 callee-saved GPRs vs. 11 on AArch64) — and were blocked by our initial `c.keeps == keptAt i` guard in `Core.lean`.
    2. **`9×` `a place: where the written places begin is not known by a number from where they began before`:** When x86-64 models (`gpt-6.2-astra-pro` R3/R4) fell back to spilling loop temporaries onto the stack (`mov [rsp + c], reg`), `Core.lean:1849` cleared `range := none` on every 8-byte stack store even though the stack frame is disjoint from every output buffer by contract (`E.out`).
  - Additionally, across `arith_need_entail`, every frontier model hit unsigned `sub` underflow on Round 1 (`sub tmp, c, 65` before `cmovae`/`csel`) when writing speculative constant-time arithmetic.

---

## Iteration 7: `ct-b64-v2` — Lifting Custom-Calling & Stack-Spill Limits in Lean 4 + Full Output-Buffer Dual Verification (`verify2.py` 6/6)

- **Three targeted Ode upgrades built directly from `ct-b64-v1`'s autopsy:**
  1. **Custom-calling callees inside `cmov*`/`csel` functions (`Core.lean` + `SoundTop.lean`, Lean 4 proved):** Introduced internal per-callee-preserved `RunsK`/`EndsK` (`keptOf : String → List Nat`) in `SoundTop.lean` and removed the `c.keeps == keptAt i` restriction from `Core.lean:5038`. Constant-time `cmov*`/`csel` callers can now call ANY custom-calling helper (`calling { in ... out ... preserves ... }`) with zero change to any of the 11 top-level theorem statements in `test_sound.py`.
  2. **Preserve `range` across 8-byte stack-frame stores (`Core.lean:1849` + `SoundStep.lean`, Lean 4 proved):** Removed `range := none` from stack-slot stores in `Core.lean` and proved `Holds.write` / `WF.write` preserve `RangeHolds` via frame/output disjointness (`E.out`). Full Lean check: **`lake build && python3 test_sound.py -v` 55/55 jobs, 2/2 OK in `0.656 s`**, zero `sorry`, zero `maxHeartbeats`, standard axioms only, all 11 top-level theorems unchanged.
  3. **Output-buffer support in independent second verifier `proof-core/verify2.py` (6/6 retroactive dual-verification!):** Added `arg ... out N`, `ensures`, `wrote`/`wrote_pre` (for both loop and join `place`s), `mem8` stores, `samebyte`, and exact `symDivide` alignment for `and64`/`shr64`/`/`/`%`. Retroactively dual-verified **6/6 (100%)** of all passing `ct-b64-v1` binaries (both multi-function helpers and 1-function join-place inlined kernels) in `0.22–0.39 s` each (`test_verify2.py` **11/11 OK**). Enabled live `verify2.py` in `ct_base64_decode.json` (removed `skip_verify2: true`).
  4. **Live `ode_tool.py` diagnostic hints:** Added targeted hint when `sub` fails unsigned underflow (`shift intermediate values up by +K and subtract K at the end`) and updated `need below` hint to mention conditional select (`cmov*`/`csel`) + join `place`s alongside branching.
- **Experiment design (`ct-b64-v2`, launching now, baseline `results-ct-b64-v1.json`):** Re-run the exact same 7-model × 2-target × 2-arm (`blind`/`advised`) panel on `ct_base64_decode` (`--max-rounds 8 --opt-rounds 3 --workers 16 --prover-slots 10 --tool-timeout 45 --cell-timeout 600 --max-usd 60`) with live `verify2.py` dual verification enabled.
- **Pre-registered causal hypothesis:** Removing the `15×` custom-calling `hasSelect` refusal and `9×` stack-spill `range` wipe (plus `sub`-underflow hints) should sharply raise `x86_64` frontier pass rate above `ct-b64-v1`'s `1/8`, increase overall strict pass rate above `6/28`, eliminate `verify2.py` gaps (`100%` of passing cells dual-verified live), and produce faster `x86_64` real-silicon kernels via custom-calling zero-clobber helpers and inlining.


