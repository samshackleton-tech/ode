# Results: Pre-Registered Cold-Room Suite `der-v2`

- **Pre-registration commit:** `04cb59aa16b4f187a140489e075eaa3b23842df2`
- **Finished (UTC):** `2026-11-26T07:32:14Z`
- **Strict pass rate:** **7/14** finished cells
- **Independent second verifier (`verify2.py`):** **7/7** passing cells dual-verified
- **Real-silicon native harness:** **7/7** passing cells executed and passed on matching hardware
- **Total rounds / API spend:** 77 rounds, **$18.55** USD

## Cell-by-Cell Outcomes

Each row reports one cold-room cell: verdict, rounds used, API cost, compiled code size, `verify2.py` status, and real-silicon test result.

| Task | Model | Target | Verdict | Rounds | Cost (USD) | Code | `verify2.py` | Native CPU |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `der_valid` | `anthropic/claude-fable-5.2` | `arm64` | PASS (R3) | 3 | $2.49 | 6 fns / 432 insns / 1732 B | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-fable-5.2` | `x86_64` | PASS (R6) | 6 | $4.58 | 8 fns / 405 insns / 1555 B | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-haiku-5.5` | `arm64` | FAIL (arith_need_entail) | 8 | $0.05 | — | — | not_run |
| `der_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | FAIL (arith_need_entail) | 8 | $0.07 | — | — | not_run |
| `der_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | PASS (R8) | 8 | $1.52 | 6 fns / 457 insns / 1856 B | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | FAIL (arith_need_entail) | 8 | $1.29 | — | — | not_run |
| `der_valid` | `google/gemini-4-neon` | `arm64` | PASS (R2) | 2 | $0.58 | 7 fns / 426 insns / 1732 B | shown | NATIVE_PASS 257/257 |
| `der_valid` | `google/gemini-4-neon` | `x86_64` | PASS (R3) | 3 | $0.77 | 8 fns / 449 insns / 1694 B | shown | NATIVE_PASS 257/257 |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | FAIL (other) | 8 | $0.56 | — | — | not_run |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | FAIL (kept_reg_refusal) | 8 | $0.65 | — | — | not_run |
| `der_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | PASS (R3) | 3 | $1.71 | 6 fns / 347 insns / 1420 B | shown | NATIVE_PASS 257/257 |
| `der_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | PASS (R6) | 6 | $3.19 | 11 fns / 338 insns / 1230 B | shown | NATIVE_PASS 257/257 |
| `der_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | FAIL (output_token_limit) | 2 | $0.41 | — | — | not_run |
| `der_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | FAIL (other) | 4 | $0.67 | — | — | not_run |

## Failing Round Breakdown

Each row counts failing rounds across all cells by root-cause category.

| Failure category | Failing rounds |
| --- | --- |
| `arith_need_entail` | 32 |
| `arith_need_compare` | 12 |
| `other` | 7 |
| `trace_refusal` | 6 |
| `kept_reg_refusal` | 5 |
| `compile_or_parse_error` | 3 |
| `output_token_limit` | 3 |
| `calling_syntax_error` | 1 |
| `prover_timeout` | 1 |

## Before vs. After Comparison (`der-v1` -> `der-v2`)

The first table compares totals over the 14 cells that both runs have (the same task, model and target); each cell was run once in each run, so a difference in one cell may be chance. The second table sets each such cell of the two runs side by side.

| Metric (over the 14 shared cells) | `der-v1` | `der-v2` | Delta |
| --- | --- | --- | --- |
| Strict passes | 3/14 | 7/14 | +4 |
| Total rounds | 80 | 77 | -3 |
| Total API spend (USD) | $21.16 | $18.55 | $-2.61 |
| Failing rounds: `arith_need_compare` | 0 | 12 | +12 |
| Failing rounds: `arith_need_entail` | 33 | 32 | -1 |
| Failing rounds: `calling_syntax_error` | 0 | 1 | +1 |
| Failing rounds: `compile_or_parse_error` | 2 | 3 | +1 |
| Failing rounds: `kept_reg_refusal` | 4 | 5 | +1 |
| Failing rounds: `other` | 9 | 7 | -2 |
| Failing rounds: `output_token_limit` | 4 | 3 | -1 |
| Failing rounds: `prover_timeout` | 9 | 1 | -8 |
| Failing rounds: `spec_need_open` | 15 | 0 | -15 |
| Failing rounds: `trace_refusal` | 1 | 6 | +5 |

| Task | Model | Target | `der-v1` | `der-v2` |
| --- | --- | --- | --- | --- |
| `der_valid` | `anthropic/claude-fable-5.2` | `arm64` | FAIL ($2.54) | PASS (R3, $2.49) |
| `der_valid` | `anthropic/claude-fable-5.2` | `x86_64` | FAIL ($3.19) | PASS (R6, $4.58) |
| `der_valid` | `anthropic/claude-haiku-5.5` | `arm64` | FAIL ($0.06) | FAIL ($0.05) |
| `der_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | FAIL ($0.07) | FAIL ($0.07) |
| `der_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | FAIL ($1.34) | PASS (R8, $1.52) |
| `der_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | FAIL ($1.39) | FAIL ($1.29) |
| `der_valid` | `google/gemini-4-neon` | `arm64` | PASS (R3, $0.81) | PASS (R2, $0.58) |
| `der_valid` | `google/gemini-4-neon` | `x86_64` | PASS (R5, $1.40) | PASS (R3, $0.77) |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | FAIL ($0.67) | FAIL ($0.56) |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | FAIL ($0.38) | FAIL ($0.65) |
| `der_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | FAIL ($3.71) | PASS (R3, $1.71) |
| `der_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | PASS (R8, $4.78) | PASS (R6, $3.19) |
| `der_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | FAIL ($0.41) | FAIL ($0.41) |
| `der_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | FAIL ($0.42) | FAIL ($0.67) |
