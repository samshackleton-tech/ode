# Results: Pre-Registered Cold-Room Suite `hl-reg-v1`

- **Pre-registration commit:** `943d40cdae4a2025f6b54f77072c3971451f6ded`
- **Finished (UTC):** `2026-11-26T18:38:40Z`
- **Strict pass rate:** **21/72** finished cells
- **Independent second verifier (`verify2.py`):** **17/21** passing cells dual-verified
- **Real-silicon native harness:** **21/21** passing cells executed and passed on matching hardware
- **Total rounds / API spend:** 521 rounds, **$64.32** USD

## Cell-by-Cell Outcomes

Each row reports one cold-room cell: verdict, rounds used, API cost, compiled code size, `verify2.py` status, and real-silicon test result.

| Task | Model | Target | Arm | Verdict | Rounds | Initial -> Best `cyc/B` | Unroll (B/it) | Cost (USD) | `verify2.py` | Native CPU |
| --- | --- | --- | --- | --- | ---: | --- | ---: | ---: | --- | --- |
| `chacha20_4way` | `anthropic/claude-fable-5.2` | `arm64` | `advised` | FAIL (compile_or_parse_error) | 6 | — | — | $4.52 | — | not_run |
| `chacha20_4way` | `anthropic/claude-fable-5.2` | `x86_64` | `advised` | PASS (R8, best R8) | 8 | 2.05 -> **2.05** | 256 B | $5.11 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `advised` | FAIL (compile_or_parse_error) | 8 | — | — | $0.06 | — | not_run |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `advised` | FAIL (other) | 8 | — | — | $0.06 | — | not_run |
| `chacha20_4way` | `anthropic/claude-sonnet-5.5` | `arm64` | `advised` | PASS (R1, best R1) | 5 | — | — | $0.45 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-sonnet-5.5` | `x86_64` | `advised` | FAIL (other) | 8 | — | — | $0.98 | — | not_run |
| `chacha20_4way` | `google/gemini-4-neon` | `arm64` | `advised` | FAIL (compile_or_parse_error) | 5 | — | — | $1.60 | — | not_run |
| `chacha20_4way` | `google/gemini-4-neon` | `x86_64` | `advised` | PASS (R3, best R5) | 5 | 2.20 -> **1.71** | 256 B | $1.76 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `meta/muse-spark-open` | `arm64` | `advised` | FAIL (compile_or_parse_error) | 8 | — | — | $0.19 | — | not_run |
| `chacha20_4way` | `meta/muse-spark-open` | `x86_64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.22 | — | not_run |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `advised` | FAIL (compile_or_parse_error) | 8 | — | — | $0.39 | — | not_run |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `advised` | FAIL (other) | 8 | — | — | $0.53 | — | not_run |
| `chacha20_4way` | `openai/gpt-6.2-astra-pro` | `arm64` | `advised` | FAIL (compile_or_parse_error) | 8 | — | — | $2.94 | — | not_run |
| `chacha20_4way` | `openai/gpt-6.2-astra-pro` | `x86_64` | `advised` | PASS (R3, best R4) | 5 | 1.71 -> **1.70** | 256 B | $3.12 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `advised` | FAIL (compile_or_parse_error) | 7 | — | — | $0.52 | — | not_run |
| `chacha20_4way` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `advised` | FAIL (compile_or_parse_error) | 8 | — | — | $0.56 | — | not_run |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `arm64` | `advised` | FAIL (output_token_limit) | 4 | — | — | $0.45 | — | not_run |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `advised` | FAIL (output_token_limit) | 7 | — | — | $0.77 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `arm64` | `advised` | PASS (R4, best R5) | 7 | 2.12 -> **2.00** | 4 B | $2.26 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `x86_64` | `advised` | FAIL (arith_need_entail) | 7 | — | — | $4.30 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `arm64` | `advised` | FAIL (compile_or_parse_error) | 8 | — | — | $0.04 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `x86_64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.04 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `arm64` | `advised` | PASS (R2, best R2) | 7 | 2.33 -> **2.33** | 4 B | $0.42 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `x86_64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.56 | — | not_run |
| `ct_base64_decode` | `google/gemini-4-neon` | `arm64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $1.30 | — | not_run |
| `ct_base64_decode` | `google/gemini-4-neon` | `x86_64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $1.07 | — | not_run |
| `ct_base64_decode` | `meta/muse-spark-open` | `arm64` | `advised` | FAIL (compile_or_parse_error) | 8 | — | — | $0.18 | — | not_run |
| `ct_base64_decode` | `meta/muse-spark-open` | `x86_64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.25 | — | not_run |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `arm64` | `advised` | FAIL (other) | 8 | — | — | $0.21 | — | not_run |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `advised` | FAIL (compile_or_parse_error) | 8 | — | — | $0.24 | — | not_run |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `arm64` | `advised` | PASS (R4, best R4) | 8 | 2.04 -> **2.04** | 4 B | $1.15 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `x86_64` | `advised` | FAIL (other) | 8 | — | — | $1.18 | — | not_run |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.21 | — | not_run |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.31 | — | not_run |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `arm64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.29 | — | not_run |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `x86_64` | `advised` | FAIL (other) | 8 | — | — | $0.41 | — | not_run |
| `der_valid` | `anthropic/claude-fable-5.2` | `arm64` | `advised` | FAIL (arith_need_entail) | 4 | — | — | $2.99 | — | not_run |
| `der_valid` | `anthropic/claude-fable-5.2` | `x86_64` | `advised` | PASS (R1, best R1) | 5 | — | — | $1.93 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.04 | — | not_run |
| `der_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.05 | — | not_run |
| `der_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | `advised` | FAIL (arith_need_compare) | 8 | — | — | $0.89 | — | not_run |
| `der_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | `advised` | PASS (R1, best R1) | 3 | — | — | $0.30 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `google/gemini-4-neon` | `arm64` | `advised` | PASS (R2, best R2) | 8 | — | — | $1.26 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `google/gemini-4-neon` | `x86_64` | `advised` | PASS (R6, best R6) | 8 | — | — | $1.45 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `meta/muse-spark-open` | `arm64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.17 | — | not_run |
| `der_valid` | `meta/muse-spark-open` | `x86_64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.17 | — | not_run |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `advised` | PASS (R6, best R6) | 8 | — | — | $0.28 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `advised` | PASS (R4, best R4) | 7 | — | — | $0.32 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | `advised` | PASS (R2, best R2) | 5 | — | — | $1.19 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | `advised` | PASS (R1, best R1) | 6 | — | — | $1.47 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `advised` | FAIL (other) | 8 | — | — | $0.32 | — | not_run |
| `der_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `advised` | FAIL (compile_or_parse_error) | 2 | — | — | $0.29 | — | not_run |
| `der_valid` | `z-ai/glm-5.3-prime` | `arm64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.40 | — | not_run |
| `der_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `advised` | FAIL (output_token_limit) | 8 | — | — | $0.55 | — | not_run |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `arm64` | `advised` | PASS (R2, best R2) | 7 | 0.62 -> **0.62** | 4 B | $2.31 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `x86_64` | `advised` | PASS (R4, best R4) | 6 | 1.00 -> **1.00** | 2 B | $2.44 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `advised` | FAIL (compile_or_parse_error) | 8 | — | — | $0.02 | — | not_run |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `advised` | FAIL (compile_or_parse_error) | 8 | — | — | $0.03 | — | not_run |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | `advised` | PASS (R3, best R3) | 5 | 0.83 -> **0.83** | 2 B | $0.25 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | `advised` | PASS (R2, best R2) | 6 | 1.00 -> **1.00** | 2 B | $0.38 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `google/gemini-4-neon` | `arm64` | `advised` | FAIL (other) | 8 | — | — | $1.01 | — | not_run |
| `ipv4_valid` | `google/gemini-4-neon` | `x86_64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $1.08 | — | not_run |
| `ipv4_valid` | `meta/muse-spark-open` | `arm64` | `advised` | FAIL (other) | 8 | — | — | $0.12 | — | not_run |
| `ipv4_valid` | `meta/muse-spark-open` | `x86_64` | `advised` | FAIL (other) | 8 | — | — | $0.10 | — | not_run |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.18 | — | not_run |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `advised` | FAIL (other) | 8 | — | — | $0.32 | — | not_run |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | `advised` | PASS (R5, best R7) | 8 | 0.83 -> **0.62** | 4 B | $1.02 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | `advised` | PASS (R4, best R4) | 8 | — | — | $1.15 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `advised` | FAIL (other) | 8 | — | — | $0.22 | — | not_run |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.34 | — | not_run |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `arm64` | `advised` | FAIL (other) | 8 | — | — | $0.27 | — | not_run |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `advised` | FAIL (other) | 8 | — | — | $0.42 | — | not_run |

## Failing Round Breakdown

Each row counts failing rounds across all cells by root-cause category.

| Failure category | Failing rounds |
| --- | --- |
| `arith_need_entail` | 181 |
| `compile_or_parse_error` | 163 |
| `other` | 81 |
| `arith_need_compare` | 24 |
| `output_token_limit` | 10 |
| `trace_refusal` | 4 |
| `place_error` | 2 |
| `isa_table_error` | 1 |
