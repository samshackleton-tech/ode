# Results: Pre-Registered Cold-Room Suite `ct-b64-v2`

- **Pre-registration commit:** `01dbf643ef29d10b14180268005ffaa60a3be5fd`
- **Finished (UTC):** `2026-11-26T12:27:54Z`
- **Strict pass rate:** **8/28** finished cells
- **Independent second verifier (`verify2.py`):** **7/8** passing cells dual-verified
- **Real-silicon native harness:** **8/8** passing cells executed and passed on matching hardware
- **Total rounds / API spend:** 192 rounds, **$31.79** USD

## Cell-by-Cell Outcomes

Each row reports one cold-room cell: verdict, rounds used, API cost, compiled code size, `verify2.py` status, and real-silicon test result.

| Task | Model | Target | Arm | Verdict | Rounds | Initial -> Best `cyc/B` | Unroll (B/it) | Cost (USD) | `verify2.py` | Native CPU |
| --- | --- | --- | --- | --- | ---: | --- | ---: | ---: | --- | --- |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `arm64` | `advised` | PASS (R4, best R4) | 7 | — | — | $2.95 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `arm64` | `blind` | FAIL (arith_need_entail) | 7 | — | — | $3.80 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `x86_64` | `advised` | PASS (R1, best R1) | 5 | — | — | $3.02 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `x86_64` | `blind` | PASS (R3, best R3) | 5 | — | — | $3.01 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `arm64` | `advised` | FAIL (other) | 8 | — | — | $0.05 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `arm64` | `blind` | FAIL (arith_need_entail) | 8 | — | — | $0.06 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `x86_64` | `advised` | FAIL (other) | 8 | — | — | $0.06 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `x86_64` | `blind` | FAIL (other) | 8 | — | — | $0.05 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `arm64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.68 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `arm64` | `blind` | FAIL (arith_need_entail) | 8 | — | — | $0.63 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `x86_64` | `advised` | PASS (R7, best R7) | 8 | — | — | $0.74 | refused | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `x86_64` | `blind` | FAIL (prover_timeout) | 8 | — | — | $0.74 | — | not_run |
| `ct_base64_decode` | `google/gemini-4-neon` | `arm64` | `advised` | FAIL (arith_need_entail) | 3 | — | — | $1.07 | — | not_run |
| `ct_base64_decode` | `google/gemini-4-neon` | `arm64` | `blind` | FAIL (arith_need_entail) | 3 | — | — | $1.25 | — | not_run |
| `ct_base64_decode` | `google/gemini-4-neon` | `x86_64` | `advised` | FAIL (arith_need_entail) | 5 | — | — | $1.06 | — | not_run |
| `ct_base64_decode` | `google/gemini-4-neon` | `x86_64` | `blind` | FAIL (arith_need_entail) | 5 | — | — | $1.23 | — | not_run |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `arm64` | `advised` | FAIL (compile_or_parse_error) | 8 | — | — | $0.43 | — | not_run |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `arm64` | `blind` | FAIL (prover_timeout) | 6 | — | — | $0.41 | — | not_run |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.39 | — | not_run |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `blind` | FAIL (other) | 8 | — | — | $0.54 | — | not_run |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `arm64` | `advised` | PASS (R3, best R3) | 8 | — | — | $1.79 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `arm64` | `blind` | PASS (R3, best R3) | 8 | — | — | $2.13 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `x86_64` | `advised` | PASS (R3, best R3) | 8 | — | — | $1.85 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `x86_64` | `blind` | PASS (R3, best R3) | 8 | — | — | $2.03 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `advised` | FAIL (other) | 8 | — | — | $0.38 | — | not_run |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `blind` | FAIL (arith_need_entail) | 5 | — | — | $0.51 | — | not_run |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `advised` | FAIL (other) | 8 | — | — | $0.47 | — | not_run |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `blind` | FAIL (compile_or_parse_error) | 5 | — | — | $0.45 | — | not_run |

## Failing Round Breakdown

Each row counts failing rounds across all cells by root-cause category.

| Failure category | Failing rounds |
| --- | --- |
| `arith_need_entail` | 87 |
| `other` | 29 |
| `compile_or_parse_error` | 22 |
| `prover_timeout` | 21 |
| `output_token_limit` | 3 |
| `kept_reg_refusal` | 2 |
| `arith_need_compare` | 1 |
| `isa_table_error` | 1 |

## Before vs. After Comparison (`ct-b64-v1` -> `ct-b64-v2`)

The first table compares totals over the 28 cells that both runs have (the same task, model and target); each cell was run once in each run, so a difference in one cell may be chance. The second table sets each such cell of the two runs side by side.

| Metric (over the 28 shared cells) | `ct-b64-v1` | `ct-b64-v2` | Delta |
| --- | --- | --- | --- |
| Strict passes | 4/28 | 8/28 | +4 |
| Total rounds | 200 | 192 | -8 |
| Total API spend (USD) | $33.66 | $31.79 | $-1.87 |
| Failing rounds: `arith_need_compare` | 0 | 1 | +1 |
| Failing rounds: `arith_need_entail` | 98 | 87 | -11 |
| Failing rounds: `compile_or_parse_error` | 24 | 22 | -2 |
| Failing rounds: `isa_table_error` | 4 | 1 | -3 |
| Failing rounds: `kept_reg_refusal` | 0 | 2 | +2 |
| Failing rounds: `other` | 42 | 29 | -13 |
| Failing rounds: `output_token_limit` | 6 | 3 | -3 |
| Failing rounds: `prover_timeout` | 16 | 21 | +5 |

| Task | Model | Target | `ct-b64-v1` | `ct-b64-v2` |
| --- | --- | --- | --- | --- |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `arm64` | PASS (R5, $3.50) | PASS (R4, $2.95) |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `arm64` | PASS (R5, $3.50) | FAIL ($3.80) |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `x86_64` | FAIL ($3.87) | PASS (R1, $3.02) |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `x86_64` | FAIL ($3.87) | PASS (R3, $3.01) |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `arm64` | FAIL ($0.05) | FAIL ($0.05) |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `arm64` | FAIL ($0.05) | FAIL ($0.06) |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `x86_64` | FAIL ($0.06) | FAIL ($0.06) |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `x86_64` | FAIL ($0.06) | FAIL ($0.05) |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `arm64` | FAIL ($0.74) | FAIL ($0.68) |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `arm64` | FAIL ($0.74) | FAIL ($0.63) |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `x86_64` | FAIL ($0.83) | PASS (R7, $0.74) |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `x86_64` | FAIL ($0.83) | FAIL ($0.74) |
| `ct_base64_decode` | `google/gemini-4-neon` | `arm64` | FAIL ($1.11) | FAIL ($1.07) |
| `ct_base64_decode` | `google/gemini-4-neon` | `arm64` | FAIL ($1.11) | FAIL ($1.25) |
| `ct_base64_decode` | `google/gemini-4-neon` | `x86_64` | FAIL ($1.33) | FAIL ($1.06) |
| `ct_base64_decode` | `google/gemini-4-neon` | `x86_64` | FAIL ($1.33) | FAIL ($1.23) |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `arm64` | FAIL ($0.31) | FAIL ($0.43) |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `arm64` | FAIL ($0.31) | FAIL ($0.41) |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `x86_64` | FAIL ($0.37) | FAIL ($0.39) |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `x86_64` | FAIL ($0.37) | FAIL ($0.54) |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `arm64` | PASS (R3, $1.86) | PASS (R3, $1.79) |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `arm64` | PASS (R3, $1.86) | PASS (R3, $2.13) |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `x86_64` | FAIL ($1.80) | PASS (R3, $1.85) |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `x86_64` | FAIL ($1.80) | PASS (R3, $2.03) |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | FAIL ($0.28) | FAIL ($0.38) |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | FAIL ($0.28) | FAIL ($0.51) |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | FAIL ($0.72) | FAIL ($0.47) |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | FAIL ($0.72) | FAIL ($0.45) |
