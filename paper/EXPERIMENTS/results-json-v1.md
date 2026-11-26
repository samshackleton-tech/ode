# Results: Pre-Registered Cold-Room Suite `json-v1`

- **Pre-registration commit:** `8f2718f86f92f25e4608cbab5d7215cf6507cfd2`
- **Finished (UTC):** `2026-11-26T12:55:27Z`
- **Strict pass rate:** **17/28** finished cells
- **Independent second verifier (`verify2.py`):** **17/17** passing cells dual-verified
- **Real-silicon native harness:** **17/17** passing cells executed and passed on matching hardware
- **Total rounds / API spend:** 187 rounds, **$30.64** USD

## Cell-by-Cell Outcomes

Each row reports one cold-room cell: verdict, rounds used, API cost, compiled code size, `verify2.py` status, and real-silicon test result.

| Task | Model | Target | Arm | Verdict | Rounds | Initial -> Best `cyc/B` | Unroll (B/it) | Cost (USD) | `verify2.py` | Native CPU |
| --- | --- | --- | --- | --- | ---: | --- | ---: | ---: | --- | --- |
| `json_str_valid` | `anthropic/claude-fable-5.2` | `arm64` | `advised` | PASS (R6, best R6) | 8 | 1.00 -> **1.00** | 22 B | $3.72 | shown | NATIVE_PASS 681/681 |
| `json_str_valid` | `anthropic/claude-fable-5.2` | `arm64` | `blind` | PASS (R2, best R2) | 5 | 1.31 -> **1.31** | 18 B | $3.21 | shown | NATIVE_PASS 681/681 |
| `json_str_valid` | `anthropic/claude-fable-5.2` | `x86_64` | `advised` | PASS (R4, best R4) | 4 | 3.12 -> **3.12** | 8 B | $3.50 | shown | NATIVE_PASS 681/681 |
| `json_str_valid` | `anthropic/claude-fable-5.2` | `x86_64` | `blind` | PASS (R6, best R6) | 6 | 1.00 -> **1.00** | 7 B | $3.57 | shown | NATIVE_PASS 681/681 |
| `json_str_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `advised` | FAIL (prover_timeout) | 8 | — | — | $0.04 | — | not_run |
| `json_str_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `blind` | FAIL (prover_timeout) | 8 | — | — | $0.04 | — | not_run |
| `json_str_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `advised` | PASS (R1, best R1) | 5 | 2.44 -> **2.44** | 6 B | $0.02 | shown | NATIVE_PASS 681/681 |
| `json_str_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `blind` | FAIL (arith_need_compare) | 8 | — | — | $0.04 | — | not_run |
| `json_str_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | `advised` | PASS (R2, best R2) | 7 | 3.67 -> **3.67** | 6 B | $0.52 | shown | NATIVE_PASS 681/681 |
| `json_str_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | `blind` | PASS (R3, best R5) | 7 | 3.50 -> **3.43** | 7 B | $0.53 | shown | NATIVE_PASS 681/681 |
| `json_str_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | `advised` | PASS (R2, best R2) | 5 | 1.45 -> **1.45** | 6 B | $0.43 | shown | NATIVE_PASS 681/681 |
| `json_str_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | `blind` | PASS (R5, best R5) | 8 | 1.45 -> **1.45** | 6 B | $0.71 | shown | NATIVE_PASS 681/681 |
| `json_str_valid` | `google/gemini-4-neon` | `arm64` | `advised` | FAIL (prover_timeout) | 6 | — | — | $1.22 | — | not_run |
| `json_str_valid` | `google/gemini-4-neon` | `arm64` | `blind` | FAIL (prover_timeout) | 6 | — | — | $1.05 | — | not_run |
| `json_str_valid` | `google/gemini-4-neon` | `x86_64` | `advised` | FAIL (arith_need_compare) | 6 | — | — | $1.34 | — | not_run |
| `json_str_valid` | `google/gemini-4-neon` | `x86_64` | `blind` | FAIL (prover_timeout) | 4 | — | — | $1.15 | — | not_run |
| `json_str_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `advised` | FAIL (calling_syntax_error) | 8 | — | — | $0.24 | — | not_run |
| `json_str_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `blind` | FAIL (prover_timeout) | 8 | — | — | $0.28 | — | not_run |
| `json_str_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `advised` | PASS (R5, best R5) | 8 | 1.17 -> **1.17** | 6 B | $0.26 | shown | NATIVE_PASS 681/681 |
| `json_str_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `blind` | PASS (R7, best R7) | 8 | 1.45 -> **1.45** | 6 B | $0.33 | shown | NATIVE_PASS 681/681 |
| `json_str_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | `advised` | PASS (R4, best R4) | 8 | 0.93 -> **0.93** | 14 B | $1.61 | shown | NATIVE_PASS 681/681 |
| `json_str_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | `blind` | PASS (R2, best R2) | 8 | 2.33 -> **2.33** | 6 B | $1.87 | shown | NATIVE_PASS 681/681 |
| `json_str_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | `advised` | PASS (R2, best R7) | 8 | 1.61 -> **1.48** | 7 B | $1.72 | shown | NATIVE_PASS 681/681 |
| `json_str_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | `blind` | PASS (R2, best R2) | 8 | 1.50 -> **1.50** | 6 B | $1.75 | shown | NATIVE_PASS 681/681 |
| `json_str_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.27 | — | not_run |
| `json_str_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `blind` | PASS (R4, best R4) | 8 | 1.75 -> **1.75** | 6 B | $0.28 | shown | NATIVE_PASS 681/681 |
| `json_str_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `advised` | PASS (R2, best R2) | 4 | 2.33 -> **2.33** | 6 B | $0.51 | shown | NATIVE_PASS 681/681 |
| `json_str_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `blind` | FAIL (output_token_limit) | 2 | — | — | $0.42 | — | not_run |

## Failing Round Breakdown

Each row counts failing rounds across all cells by root-cause category.

| Failure category | Failing rounds |
| --- | --- |
| `arith_need_compare` | 40 |
| `arith_need_entail` | 39 |
| `prover_timeout` | 33 |
| `other` | 13 |
| `kept_reg_refusal` | 8 |
| `output_token_limit` | 4 |
| `calling_syntax_error` | 3 |
| `compile_or_parse_error` | 3 |
| `place_error` | 2 |
| `trace_refusal` | 1 |
