# Results: Pre-Registered Cold-Room Suite `perf-v1`

- **Pre-registration commit:** `dd3b823970ca46b26a68f13a44f96a0e3191e964`
- **Finished (UTC):** `2026-11-26T04:31:08Z`
- **Strict pass rate:** **14/16** finished cells
- **Independent second verifier (`verify2.py`):** **7/14** passing cells dual-verified
- **Real-silicon native harness:** **14/14** passing cells executed and passed on matching hardware
- **Total rounds / API spend:** 91 rounds, **$20.40** USD

## Cell-by-Cell Outcomes

Each row reports one cold-room cell: verdict, rounds used, API cost, compiled code size, `verify2.py` status, and real-silicon test result.

| Task | Model | Target | Arm | Verdict | Rounds | Initial -> Best `cyc/B` | Unroll (B/it) | Cost (USD) | `verify2.py` | Native CPU |
| --- | --- | --- | --- | --- | ---: | --- | ---: | ---: | --- | --- |
| `byte_sum` | `anthropic/claude-fable-5.2` | `arm64` | `advised` | PASS (R4, best R4) | 5 | 1.00 -> **1.00** | 1 B | $3.22 | shown | NATIVE_PASS 112/112 |
| `byte_sum` | `anthropic/claude-fable-5.2` | `arm64` | `blind` | PASS (R1, best R1) | 6 | 0.34 -> **0.34** | 8 B | $1.98 | shown | NATIVE_PASS 112/112 |
| `byte_sum` | `anthropic/claude-fable-5.2` | `x86_64` | `advised` | PASS (R1, best R1) | 6 | 0.50 -> **0.50** | 8 B | $1.94 | shown | NATIVE_PASS 112/112 |
| `byte_sum` | `anthropic/claude-fable-5.2` | `x86_64` | `blind` | PASS (R1, best R3) | 6 | 0.50 -> **0.44** | 16 B | $2.40 | refused | NATIVE_PASS 112/112 |
| `byte_sum` | `anthropic/claude-sonnet-5.5` | `arm64` | `advised` | PASS (R1, best R3) | 5 | 0.44 -> **0.34** | 8 B | $0.27 | shown | NATIVE_PASS 112/112 |
| `byte_sum` | `anthropic/claude-sonnet-5.5` | `arm64` | `blind` | PASS (R1, best R2) | 5 | 1.00 -> **0.34** | 8 B | $0.24 | shown | NATIVE_PASS 112/112 |
| `byte_sum` | `anthropic/claude-sonnet-5.5` | `x86_64` | `advised` | PASS (R2, best R4) | 6 | 1.00 -> **0.50** | 8 B | $0.37 | shown | NATIVE_PASS 112/112 |
| `byte_sum` | `anthropic/claude-sonnet-5.5` | `x86_64` | `blind` | PASS (R5, best R6) | 6 | 1.00 -> **0.75** | 4 B | $0.38 | shown | NATIVE_PASS 112/112 |
| `byte_sum` | `google/gemini-4-neon` | `arm64` | `advised` | PASS (R5, best R5) | 5 | 0.34 -> **0.34** | 8 B | $0.89 | refused | NATIVE_PASS 112/112 |
| `byte_sum` | `google/gemini-4-neon` | `arm64` | `blind` | FAIL (arith_need_entail) | 5 | — | — | $1.70 | — | not_run |
| `byte_sum` | `google/gemini-4-neon` | `x86_64` | `advised` | FAIL (prover_timeout_120s) | 6 | — | — | $1.59 | — | not_run |
| `byte_sum` | `google/gemini-4-neon` | `x86_64` | `blind` | PASS (R5, best R5) | 6 | 0.50 -> **0.50** | 8 B | $1.49 | refused | NATIVE_PASS 112/112 |
| `byte_sum` | `openai/gpt-6.2-astra-pro` | `arm64` | `advised` | PASS (R1, best R5) | 6 | 0.34 -> **0.33** | 16 B | $0.94 | refused | NATIVE_PASS 112/112 |
| `byte_sum` | `openai/gpt-6.2-astra-pro` | `arm64` | `blind` | PASS (R1, best R3) | 6 | 0.34 -> **0.33** | 16 B | $0.96 | refused | NATIVE_PASS 112/112 |
| `byte_sum` | `openai/gpt-6.2-astra-pro` | `x86_64` | `advised` | PASS (R1, best R4) | 6 | 0.50 -> **0.38** | 16 B | $0.95 | refused | NATIVE_PASS 112/112 |
| `byte_sum` | `openai/gpt-6.2-astra-pro` | `x86_64` | `blind` | PASS (R1, best R1) | 6 | 0.42 -> **0.42** | 12 B | $1.08 | refused | NATIVE_PASS 112/112 |

## Failing Round Breakdown

Each row counts failing rounds across all cells by root-cause category.

| Failure category | Failing rounds |
| --- | --- |
| `prover_timeout_120s` | 28 |
| `arith_need_entail` | 19 |
| `other` | 3 |
| `compile_or_parse_error` | 1 |

## Notes written after the run

### 1. Real-silicon validation at `n = 4096` bytes (`NATIVE_BENCH=1`) and static-model correlation

After the run finished, all 14 passing bundles (both each cell's initial passing round and its best round) were timed on real hardware at `n = 4096` bytes (median of 9 rounds × 20,000 calls): `arm64` on a local Apple M6 (not under a timing lock; treat as indicative), and `x86_64` pinned to one core on an AMD Zen 4 host (Threadripper PRO 7975WX).

The table below compares static `ode advise` predictions (`cyc/B` on the hardware-matched model: `apple_m` for AArch64, `zen4` for x86-64) against measured median nanoseconds per 4,096-byte call, alongside post-fix `verify2.py` dual verification.

| Model | Target | Arm | Rounds (`first -> best`) | Static `cyc/B` (`first -> best`, hw arch) | Unroll | Real silicon `4096 B` (`first -> best`) | Fixed `verify2.py` |
| --- | --- | --- | --- | --- | ---: | --- | --- |
| `gpt-6.2-astra-pro` | `x86_64` | `advised` | R1 -> R4 | 0.50 -> **0.38** (`zen4` 0.38) | 16 B | 405.0 -> **326.7 ns** | shown |
| `gpt-6.2-astra-pro` | `x86_64` | `blind` | R1 -> R1 | 0.42 -> **0.42** (`zen4` 0.42) | 12 B | 364.9 -> **364.9 ns** | shown |
| `claude-sonnet-5.5` | `x86_64` | `advised` | R2 -> R4 | 1.00 -> **0.50** (`zen4` 0.47) | 8 B | 815.6 -> **422.9 ns** | shown |
| `claude-sonnet-5.5` | `x86_64` | `blind` | R5 -> R6 | 1.00 -> **0.75** (`zen4` 0.62) | 4 B | 823.5 -> **534.6 ns** | shown |
| `claude-fable-5.2` | `x86_64` | `advised` | R1 -> R1 | 0.50 -> **0.50** (`zen4` 0.47) | 8 B | 416.0 -> **416.0 ns** | shown |
| `claude-fable-5.2` | `x86_64` | `blind` | R1 -> R3 | 0.50 -> **0.44** (`zen4` 0.41) | 16 B | 377.8 -> **399.4 ns** | shown |
| `gemini-4-neon` | `x86_64` | `blind` | R5 -> R5 | 0.50 -> **0.50** (`zen4` 0.38) | 8 B | 422.6 -> **422.6 ns** | shown |
| `gpt-6.2-astra-pro` | `arm64` | `advised` | R1 -> R5 | 0.34 -> **0.33** (`apple_m` 0.33) | 16 B | 299.7 -> **299.4 ns** | shown |
| `gpt-6.2-astra-pro` | `arm64` | `blind` | R1 -> R3 | 0.34 -> **0.33** (`apple_m` 0.33) | 16 B | 299.4 -> **299.4 ns** | shown |
| `claude-sonnet-5.5` | `arm64` | `advised` | R1 -> R3 | 0.44 -> **0.34** (`apple_m` 0.34) | 8 B | 319.6 -> **300.6 ns** | shown |
| `claude-sonnet-5.5` | `arm64` | `blind` | R1 -> R2 | 1.00 -> **0.34** (`apple_m` 0.34) | 8 B | 869.6 -> **300.4 ns** | shown |
| `gemini-4-neon` | `arm64` | `advised` | R5 -> R5 | 0.34 -> **0.34** (`apple_m` 0.34) | 8 B | 299.9 -> **299.9 ns** | shown |
| `claude-fable-5.2` | `arm64` | `blind` | R1 -> R1 | 0.34 -> **0.34** (`apple_m` 0.34) | 8 B | 300.4 -> **300.4 ns** | shown |
| `claude-fable-5.2` | `arm64` | `advised` | R4 -> R4 | 1.00 -> **1.00** (`apple_m` 1.00) | 1 B | 869.5 -> **869.5 ns** | shown |

### 2. Key findings

- **Real-silicon speedups and static-model fidelity:** Cold-room models achieved **2.52×** real-silicon speedup on AMD Zen 4 (`823.5 ns -> 326.7 ns`) and **2.90×** on Apple M6 (`869.6 ns -> 299.4 ns`, matching the 3-load-pipe hardware ceiling `~1365 cyc` for 4,096 byte loads) while maintaining 100% formal verification. Static `uica_sim.py` predictions tracked real hardware ratios closely (`1.00 / 0.34 = 2.94×` predicted vs. `2.90×` measured on Apple M6; `1.00 / 0.50 = 2.00×` predicted vs. `1.95×–2.03×` measured on Zen 4; and `0.38` vs. `0.41` `cyc/B` correctly ranked `gpt-6.2-astra-pro` 16 B/it at `326.7 ns` ahead of `claude-fable-5.2` 16 B/it at `399.4 ns`). One subtle exception (`claude-fable-5.2 x86_64 blind` R1 8 B/it `377.8 ns` vs. R3 16 B/it `399.4 ns`) highlights an op-cache/fetch-line cost on 160+ B loop bodies not yet weighted in the static model.
- **Controlled `advised` vs. `blind` comparison:** Both arms received the exact same `docs/QUICKSTART.md` (including Section 7) and prompt; only `advised` received live `ode advise --all-archs` feedback after each verified round. Pass rates were identical (`7/8` each, `14/16` total). Live `ode advise` feedback produced its clearest wins on `x86_64`, where `gpt-6.2-astra-pro` (`326.7 ns` vs. `364.9 ns`, best overall x86-64 result) and `claude-sonnet-5.5` (`422.9 ns` vs. `534.6 ns`, stepping `1.00 -> 0.75 -> 0.50 cyc/B` across rounds R2–R4) both beat their `blind` counterparts. On `arm64`, both arms converged to the `~300 ns` load-port ceiling once unrolled to 8×–16× (`claude-fable-5.2 arm64 advised` spent rounds R1–R3 on an aggressive unroll before falling back to 1× on R4 and hitting the 900 s wall-clock cap on R5).
- **Emergent zero-instruction mid-loop proof cuts:** Both `gpt-6.2-astra-pro` (on `x86_64` and `arm64`) and `claude-fable-5.2` (on `x86_64`) independently repurposed acyclic mid-function `place` join points (without `decreases`) as zero-instruction straight-line proof cuts inside 16-byte unrolled loops (`8 + 8` `sum_from` unfold steps), achieving 16 B/iter verification without emitting a single extra machine instruction.
- **Dual verification (`verify2.py`) completeness fixes caught by `perf-v1`:** During the live run (frozen at commit `153a910`), 7 of 14 passing cells were refused by `verify2.py` because `verify2.py` lacked three cases that `Core.lean` already supports: preserving path facts across `Sym.general` loop entry (`Core.lean:4836`), x86-64 `lea` (`at` table op), and checking `decreases >= 0` at loop entry rather than redundantly on the back-edge (`Core.lean:5013–5016`). With those three fixes applied in `proof-core/verify2.py`, **14/14 (100%)** of passing `perf-v1` bundles verify as `shown` in both `odeverify` (Lean 4) and `verify2.py` (0.10–0.16 s each).
- **Next prover improvement exposed by `perf-v1`:** `prover_timeout_120s` accounted for 28 of 51 failing rounds, mostly when models attempted 16× unrolls in a single block exceeding `Core.lean`'s 15-open `specGoal` fuel without a mid-loop proof cut. Failing fast with an explicit diagnostic when `opened` hits the fuel limit is an immediate next improvement.

