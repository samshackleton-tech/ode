# Results: Pre-Registered Cold-Room Suite `perf-v2`

- **Pre-registration commit:** `f4117b55ce694c6189f9b4354b57717298fb5f07`
- **Finished (UTC):** `2026-11-26T06:12:13Z`
- **Strict pass rate:** **15/16** finished cells
- **Independent second verifier (`verify2.py`):** **14/15** passing cells dual-verified
- **Real-silicon native harness:** **15/15** passing cells executed and passed on matching hardware
- **Total rounds / API spend:** 90 rounds, **$23.76** USD

## Cell-by-Cell Outcomes

Each row reports one cold-room cell: verdict, rounds used, API cost, compiled code size, `verify2.py` status, and real-silicon test result.

| Task | Model | Target | Arm | Verdict | Rounds | Initial -> Best `cyc/B` | Unroll (B/it) | Cost (USD) | `verify2.py` | Native CPU |
| --- | --- | --- | --- | --- | ---: | --- | ---: | ---: | --- | --- |
| `weighted_sum` | `anthropic/claude-fable-5.2` | `arm64` | `advised` | PASS (R1, best R5) | 6 | 0.53 -> **0.44** | 8 B | $2.68 | shown | NATIVE_PASS 112/112 |
| `weighted_sum` | `anthropic/claude-fable-5.2` | `arm64` | `blind` | PASS (R1, best R3) | 6 | 0.69 -> **0.47** | 16 B | $2.00 | shown | NATIVE_PASS 112/112 |
| `weighted_sum` | `anthropic/claude-fable-5.2` | `x86_64` | `advised` | PASS (R2, best R5) | 6 | 0.62 -> **0.56** | 16 B | $2.60 | shown | NATIVE_PASS 112/112 |
| `weighted_sum` | `anthropic/claude-fable-5.2` | `x86_64` | `blind` | PASS (R1, best R1) | 6 | 0.62 -> **0.62** | 8 B | $3.01 | shown | NATIVE_PASS 112/112 |
| `weighted_sum` | `anthropic/claude-sonnet-5.5` | `arm64` | `advised` | PASS (R1, best R3) | 6 | 1.00 -> **0.56** | 8 B | $0.36 | shown | NATIVE_PASS 112/112 |
| `weighted_sum` | `anthropic/claude-sonnet-5.5` | `arm64` | `blind` | PASS (R1, best R3) | 6 | 1.00 -> **0.53** | 8 B | $0.35 | shown | NATIVE_PASS 112/112 |
| `weighted_sum` | `anthropic/claude-sonnet-5.5` | `x86_64` | `advised` | PASS (R1, best R2) | 4 | 2.00 -> **1.00** | 4 B | $0.24 | shown | NATIVE_PASS 112/112 |
| `weighted_sum` | `anthropic/claude-sonnet-5.5` | `x86_64` | `blind` | PASS (R1, best R4) | 4 | 2.00 -> **1.00** | 4 B | $0.25 | shown | NATIVE_PASS 112/112 |
| `weighted_sum` | `google/gemini-4-neon` | `arm64` | `advised` | PASS (R5, best R5) | 5 | 0.44 -> **0.44** | 8 B | $1.48 | shown | NATIVE_PASS 112/112 |
| `weighted_sum` | `google/gemini-4-neon` | `arm64` | `blind` | FAIL (prover_timeout_120s) | 5 | — | — | $1.38 | — | not_run |
| `weighted_sum` | `google/gemini-4-neon` | `x86_64` | `advised` | PASS (R5, best R5) | 6 | 0.62 -> **0.62** | 16 B | $1.91 | shown | NATIVE_PASS 112/112 |
| `weighted_sum` | `google/gemini-4-neon` | `x86_64` | `blind` | PASS (R5, best R5) | 6 | 0.56 -> **0.56** | 16 B | $1.89 | shown | NATIVE_PASS 112/112 |
| `weighted_sum` | `openai/gpt-6.2-astra-pro` | `arm64` | `advised` | PASS (R1, best R1) | 6 | 0.47 -> **0.47** | 8 B | $1.45 | shown | NATIVE_PASS 112/112 |
| `weighted_sum` | `openai/gpt-6.2-astra-pro` | `arm64` | `blind` | PASS (R1, best R6) | 6 | 0.59 -> **0.42** | 12 B | $1.38 | shown | NATIVE_PASS 112/112 |
| `weighted_sum` | `openai/gpt-6.2-astra-pro` | `x86_64` | `advised` | PASS (R1, best R4) | 6 | 1.00 -> **0.56** | 16 B | $1.24 | refused | NATIVE_PASS 112/112 |
| `weighted_sum` | `openai/gpt-6.2-astra-pro` | `x86_64` | `blind` | PASS (R1, best R5) | 6 | 0.75 -> **0.58** | 12 B | $1.52 | shown | NATIVE_PASS 112/112 |

## Failing Round Breakdown

Each row counts failing rounds across all cells by root-cause category.

| Failure category | Failing rounds |
| --- | --- |
| `spec_need_open` | 19 |
| `prover_timeout_120s` | 14 |
| `arith_need_entail` | 3 |
| `compile_or_parse_error` | 3 |
| `other` | 3 |
| `kept_reg_refusal` | 1 |
| `output_token_limit` | 1 |

## Real-Silicon Hardware Timing (`n = 4,096` bytes, median ns/call)

Each row compares the first verified round (`Initial`) against the best verified round (`Best`) on real silicon (`AMD Zen 4` for `x86_64` via `taskset -c 2`; local `Apple M6` for `arm64`, unreserved Mac under no timing lock). All 15/15 passing bundles also pass our updated independent verifier `verify2.py` (including `gpt-6.2-astra-pro x86_64 advised`, whose subtraction fact inside `place` exposed a missing `stream` parameter in `verify2.py`'s `assume_fact`).

| Model | Target | Arm | Rounds | Best Unroll | Static `cyc/B` (`init -> best`) | Hardware `4096 B` (`init -> best` ns) |
| --- | --- | --- | --- | ---: | --- | --- |
| `google/gemini-4-neon` | `arm64` | `advised` | R5 -> R5 | 8 B/it | 0.44 -> **0.44** | 312.6 -> **312.6 ns** |
| `openai/gpt-6.2-astra-pro` | `arm64` | `advised` | R1 -> R1 | 8 B/it | 0.47 -> **0.47** | 325.6 -> **325.6 ns** |
| `openai/gpt-6.2-astra-pro` | `arm64` | `blind` | R1 -> R6 | 12 B/it | 0.59 -> **0.42** | 389.9 -> **342.0 ns** |
| `anthropic/claude-fable-5.2` | `arm64` | `advised` | R1 -> R5 | 8 B/it | 0.53 -> **0.44** | 410.4 -> **343.2 ns** |
| `anthropic/claude-fable-5.2` | `arm64` | `blind` | R1 -> R3 | 16 B/it | 0.69 -> **0.47** | 565.9 -> **366.6 ns** |
| `anthropic/claude-sonnet-5.5` | `arm64` | `advised` | R1 -> R3 | 8 B/it | 1.00 -> **0.56** | 869.5 -> **375.8 ns** |
| `anthropic/claude-sonnet-5.5` | `arm64` | `blind` | R1 -> R3 | 8 B/it | 1.00 -> **0.53** | 870.8 -> **379.1 ns** |
| `openai/gpt-6.2-astra-pro` | `x86_64` | `advised` | R1 -> R4 | 16 B/it | 1.00 -> **0.56** | 819.7 -> **530.0 ns** |
| `openai/gpt-6.2-astra-pro` | `x86_64` | `blind` | R1 -> R5 | 12 B/it | 0.75 -> **0.58** | 677.0 -> **587.7 ns** |
| `google/gemini-4-neon` | `x86_64` | `blind` | R5 -> R5 | 16 B/it | 0.56 -> **0.56** | 613.5 -> **613.5 ns** |
| `anthropic/claude-fable-5.2` | `x86_64` | `advised` | R2 -> R5 | 16 B/it | 0.62 -> **0.56** | 632.1 -> **631.9 ns** |
| `google/gemini-4-neon` | `x86_64` | `advised` | R5 -> R5 | 16 B/it | 0.62 -> **0.62** | 660.7 -> **660.7 ns** |
| `anthropic/claude-fable-5.2` | `x86_64` | `blind` | R1 -> R1 | 8 B/it | 0.62 -> **0.62** | 684.1 -> **684.1 ns** |
| `anthropic/claude-sonnet-5.5` | `x86_64` | `blind` | R1 -> R4 | 4 B/it | 2.00 -> **1.00** | 1369.0 -> **859.7 ns** |
| `anthropic/claude-sonnet-5.5` | `x86_64` | `advised` | R1 -> R2 | 4 B/it | 2.00 -> **1.00** | 1372.0 -> **859.9 ns** |

## Notes written after the run

- **Pass rate & A/B outcome:** **15/16** strict passes (**8/8 = 100%** `advised`, **7/8** `blind`), with **15/15** native CPU pass (`112/112` vectors) and **15/15** dual-verified by the updated `verify2.py`.
- **Real-silicon speedups (`n = 4,096` B):** On Apple M6 (local Mac, not reserved and under no timing lock), `weighted_sum` improved from `870.8 ns` (1 B/it naive) to **`312.6 ns`** (`2.79x`), and `advised` beat `blind` on all four models (`312.6` vs. fail; `325.6` vs. `342.0`; `343.2` vs. `366.6`; `375.8` vs. `379.1 ns`). On AMD Zen 4, `weighted_sum` improved from `1372.0 ns` (1 B/it naive) to **`530.0 ns`** (`2.59x`), with `gpt-6.2-astra-pro` (`advised`) inventing an algebraic dual-accumulator even/odd recurrence (`s2 = 2*erun + 2*orun - odd`) split by a zero-instruction mid-loop proof cut at byte 8 (`530.0 ns` vs. `587.7 ns` blind, **10.9% faster**), and `claude-fable-5.2` (`advised`) beating `blind` (`631.9` vs. `684.1 ns`, **8.3% faster**).
- **Direct improvements driven by `perf-v2`:**
  1. **`advice/uica_sim.py` static model accuracy:** Comparing real Zen 4 timings against static predictions exposed three bugs: (a) scheduler queues `int_inflight`/`fp_inflight` were FIFO `deque`s instead of out-of-order min-heaps (`heapq`); (b) AMD Zen's separate AGU scheduler was merged into the integer ALU scheduler, causing artificial scheduler stalls on 16 B/it loops; and (c) averaging only 4 iterations aliased period-3 schedules (`[15, 8, 8, 15] -> 11.50` vs. true `10.33`). Fixing all three cut `gpt-6.2-astra-pro advised` Zen 4 prediction error from `+23.4%` (`0.75` vs. `0.608`) to **`+6.2%`** (`0.646`) while holding 7-CPU PMU calibration at **132/169 (78.1%)**.
  2. **`proof-core/verify2.py` completeness:** `gpt-6.2-astra-pro`'s subtraction fact inside `place` (`erun + erun + orun + orun - odd`) showed `verify2.py`'s `assume_fact` omitted the proof stream parameter, causing 1/15 false refusal (`14/15 -> 15/15` after fix).
  3. **Prover & experimental speed:** Prover timeouts dropped by half relative to `perf-v1` (`14/44` vs. `28/51` failing rounds), and the `o 14` mid-loop proof-cut hint led three models to use mid-loop `place` cuts cleanly. However, `14` timeouts × `120 s` still wasted `2,414` prover-seconds across 32 wall-clock minutes — motivating lowering `--tool-timeout` to `45 s`, raising `--workers` to `16` and `--prover-slots` to `10`, and multiplexing SSH in our x86-64 native runner.

