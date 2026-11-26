# Results: Pre-Registered Cold-Room Suite `der-v1`

- **Pre-registration commit:** `285364cf7400eb1097083d5ce6e459a291f29e7d`
- **Finished (UTC):** `2026-11-26T06:51:58Z`
- **Strict pass rate:** **3/14** finished cells
- **Independent second verifier (`verify2.py`):** **1/3** passing cells dual-verified
- **Real-silicon native harness:** **3/3** passing cells executed and passed on matching hardware
- **Total rounds / API spend:** 80 rounds, **$21.16** USD

## Cell-by-Cell Outcomes

Each row reports one cold-room cell: verdict, rounds used, API cost, compiled code size, `verify2.py` status, and real-silicon test result.

| Task | Model | Target | Verdict | Rounds | Cost (USD) | Code | `verify2.py` | Native CPU |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `der_valid` | `anthropic/claude-fable-5.2` | `arm64` | FAIL (arith_need_entail) | 3 | $2.54 | — | — | not_run |
| `der_valid` | `anthropic/claude-fable-5.2` | `x86_64` | FAIL (prover_timeout) | 4 | $3.19 | — | — | not_run |
| `der_valid` | `anthropic/claude-haiku-5.5` | `arm64` | FAIL (spec_need_open) | 8 | $0.06 | — | — | not_run |
| `der_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | FAIL (arith_need_entail) | 8 | $0.07 | — | — | not_run |
| `der_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | FAIL (spec_need_open) | 7 | $1.34 | — | — | not_run |
| `der_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | FAIL (arith_need_entail) | 8 | $1.39 | — | — | not_run |
| `der_valid` | `google/gemini-4-neon` | `arm64` | PASS (R3) | 3 | $0.81 | 10 fns / 399 insns / 1636 B | refused | NATIVE_PASS 257/257 |
| `der_valid` | `google/gemini-4-neon` | `x86_64` | PASS (R5) | 5 | $1.40 | 7 fns / 431 insns / 1726 B | refused | NATIVE_PASS 257/257 |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | FAIL (arith_need_entail) | 8 | $0.67 | — | — | not_run |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | FAIL (other) | 8 | $0.38 | — | — | not_run |
| `der_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | FAIL (spec_need_open) | 6 | $3.71 | — | — | not_run |
| `der_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | PASS (R8) | 8 | $4.78 | 6 fns / 395 insns / 1522 B | shown | NATIVE_PASS 257/257 |
| `der_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | FAIL (output_token_limit) | 2 | $0.41 | — | — | not_run |
| `der_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | FAIL (output_token_limit) | 2 | $0.42 | — | — | not_run |

## Failing Round Breakdown

Each row counts failing rounds across all cells by root-cause category.

| Failure category | Failing rounds |
| --- | --- |
| `arith_need_entail` | 33 |
| `spec_need_open` | 15 |
| `other` | 9 |
| `prover_timeout` | 9 |
| `kept_reg_refusal` | 4 |
| `output_token_limit` | 4 |
| `compile_or_parse_error` | 2 |
| `trace_refusal` | 1 |

## Notes written after the run

- **Harness artifact discovered during post-run autopsy (critical limitation of `der-v1`):** The isolated worktree for `der-v1` copied `odeverify` into `proof-core/.lake/build/bin/` but omitted `odeprove` and `odespec`. Without `odeprove`, `prove.py` fell back to spawning a fresh `odeverify` subprocess per proof step (roughly 5x–10x slower, contributing to all 9 `prover_timeout` rounds) and `locate()` returned no source locations, so failing rounds printed raw vector-indexed `need entail` / `need below` / `need held` dumps instead of `ode pack`'s source-located `cannot show:` diagnostics. `run_suite.py` now checks that all three binaries (`odeverify`, `odeprove`, `odespec`) are present in `self_test_cli` before any API call starts.
- **Dual-verification (`verify2.py`):** Both `google/gemini-4-neon` passing solutions (`arm64` 10 fns / 399 insns; `x86_64` 7 fns / 431 insns) passed `odeverify` and native CPU execution (`257/257`) but exposed four completeness gaps in `proof-core/verify2.py`: (1) right-to-left `argumentV` resolution matching `Core.lean`'s `.cons`; (2) `same_call` reachability through `state["eqs"]`; (3) skipping `place 0` on entry before executing instruction 0; and (4) resetting `visited_places` across `jstack` when generalizing a loop `place` reached from inside a join place. Fixing all four brought `der-v1` dual-verification from `1/3` to **3/3** passing cells.
- **Prover diagnostics (`prove.py`):** Even with `odeprove` present, post-run traces on `claude-fable-5.2` and `claude-sonnet-5.5` showed two prover bugs: (1) backtracking through `need held` / `need spec` after hitting a hard non-spec refusal (such as a stack-slot trace mark violation) exploded to 6,748 asks and overwrote the real refusal with `refused: the value held is of another use`; and (2) backtracking into the entry-call `t open 0` overwrote deeper arithmetic failures with shallow bogus goals (`start >= end`). Both were fixed via `hard_refusal` short-circuiting and `best_last` (deepest partial proof wins) before `der-v2`.
- **Open-weights reasoning cap (`qwen/qwen3.8-2.4t-a95b`):** `qwen/qwen3.8-2.4t-a95b` ignored `reasoning: {"effort": "medium"}` and spent all 32,000 completion tokens thinking (~370 s/round, `finish_reason: "length"`). Probing OpenRouter confirmed that passing `reasoning: {"max_tokens": 8192}` caps Qwen's reasoning chain cleanly and returns `finish_reason: "stop"`.
- **Wall-clock speedup:** Running all 14 cells in one parallel wave (`--workers 16`, `--prover-slots 10`, `--tool-timeout 45`, multiplexed SSH) finished in **14 minutes** (down from 32 minutes for 16 cells in `perf-v2`), though `--cell-timeout 540` clipped slow frontier models (`claude-fable-5.2` at 3–4 rounds); raised to `720 s` for `der-v2`.

