# Results: Pre-Registered Cold-Room Suite `hl-reg-v3`

- **Pre-registration commit:** `ceb5c60042fb29b4eef207a094421da24c0a0058`
- **Finished (UTC):** `2026-11-26T22:51:43Z`
- **Strict pass rate:** **37/72** finished cells
- **Independent second verifier (`verify2.py`):** **19/37** passing cells dual-verified
- **Real-silicon native harness:** **37/37** passing cells executed and passed on matching hardware
- **Total rounds / API spend:** 502 rounds, **$61.69** USD

## Cell-by-Cell Outcomes

Each row reports one cold-room cell: verdict, rounds used, API cost, compiled code size, `verify2.py` status, and real-silicon test result.

| Task | Model | Target | Arm | Verdict | Rounds | Initial -> Best `cyc/B` | Unroll (B/it) | Cost (USD) | `verify2.py` | Native CPU |
| --- | --- | --- | --- | --- | ---: | --- | ---: | ---: | --- | --- |
| `chacha20_4way` | `anthropic/claude-fable-5.2` | `arm64` | `advised` | PASS (R1, best R2) | 3 | 2.48 -> **2.34** | 256 B | $1.16 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-fable-5.2` | `x86_64` | `advised` | PASS (R1, best R2) | 3 | 1.72 -> **1.70** | 256 B | $1.68 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `advised` | PASS (R4, best R5) | 6 | 2.41 -> **2.41** | 256 B | $0.04 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `advised` | FAIL (other) | 8 | — | — | $0.06 | — | not_run |
| `chacha20_4way` | `anthropic/claude-sonnet-5.5` | `arm64` | `advised` | PASS (R1, best R3) | 3 | 7.58 -> **2.48** | 256 B | $0.21 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-sonnet-5.5` | `x86_64` | `advised` | PASS (R5, best R5) | 7 | 1.94 -> **1.94** | 256 B | $0.88 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `google/gemini-4-neon` | `arm64` | `advised` | PASS (R2, best R3) | 4 | 2.41 -> **2.41** | 256 B | $0.90 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `google/gemini-4-neon` | `x86_64` | `advised` | PASS (R1, best R3) | 3 | 1.81 -> **1.71** | 256 B | $1.22 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `meta/muse-spark-open` | `arm64` | `advised` | PASS (R1, best R3) | 4 | 2.41 -> **2.41** | 256 B | $0.13 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `meta/muse-spark-open` | `x86_64` | `advised` | PASS (R3, best R3) | 6 | 6.71 -> **6.71** | 256 B | $0.21 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `advised` | PASS (R1, best R1) | 4 | 2.41 -> **2.41** | 256 B | $0.39 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `advised` | PASS (R3, best R4) | 8 | 5.89 -> **3.48** | 256 B | $0.84 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `openai/gpt-6.2-astra-pro` | `arm64` | `advised` | PASS (R2, best R4) | 4 | 2.48 -> **2.39** | 256 B | $1.98 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `openai/gpt-6.2-astra-pro` | `x86_64` | `advised` | PASS (R1, best R3) | 4 | 1.72 -> **1.70** | 256 B | $2.08 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `advised` | PASS (R8, best R8) | 8 | 7.58 -> **7.58** | 256 B | $0.55 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `advised` | PASS (R7, best R8) | 8 | 4.81 -> **4.42** | 256 B | $0.67 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `arm64` | `advised` | PASS (R1, best R3) | 3 | 2.48 -> **2.34** | 256 B | $0.27 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `advised` | PASS (R5, best R8) | 8 | 2.36 -> **2.34** | 256 B | $1.05 | — | NATIVE_PASS 98/98 |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `arm64` | `advised` | PASS (R3, best R5) | 5 | 2.04 -> **2.00** | 4 B | $1.49 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `x86_64` | `advised` | PASS (R3, best R3) | 7 | 2.50 -> **2.50** | 4 B | $2.51 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `arm64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.04 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `x86_64` | `advised` | FAIL (other) | 8 | — | — | $0.04 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `arm64` | `advised` | PASS (R2, best R2) | 5 | 2.33 -> **2.33** | 4 B | $0.28 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `x86_64` | `advised` | FAIL (other) | 8 | — | — | $0.60 | — | not_run |
| `ct_base64_decode` | `google/gemini-4-neon` | `arm64` | `advised` | PASS (R5, best R5) | 8 | 1.96 -> **1.96** | 4 B | $2.08 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `google/gemini-4-neon` | `x86_64` | `advised` | FAIL (other) | 8 | — | — | $1.69 | — | not_run |
| `ct_base64_decode` | `meta/muse-spark-open` | `arm64` | `advised` | FAIL (other) | 8 | — | — | $0.29 | — | not_run |
| `ct_base64_decode` | `meta/muse-spark-open` | `x86_64` | `advised` | FAIL (other) | 8 | — | — | $0.15 | — | not_run |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `arm64` | `advised` | FAIL (other) | 8 | — | — | $0.26 | — | not_run |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `advised` | FAIL (compile_or_parse_error) | 8 | — | — | $0.21 | — | not_run |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `arm64` | `advised` | PASS (R7, best R7) | 8 | 2.00 -> **2.00** | 4 B | $2.13 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `x86_64` | `advised` | PASS (R2, best R4) | 6 | 2.50 -> **2.25** | 4 B | $1.89 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `advised` | FAIL (other) | 8 | — | — | $0.44 | — | not_run |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `advised` | FAIL (other) | 8 | — | — | $0.43 | — | not_run |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `arm64` | `advised` | FAIL (arith_need_compare) | 8 | — | — | $0.25 | — | not_run |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `x86_64` | `advised` | FAIL (other) | 8 | — | — | $0.26 | — | not_run |
| `der_valid` | `anthropic/claude-fable-5.2` | `arm64` | `advised` | PASS (R2, best R2) | 5 | — | — | $1.99 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-fable-5.2` | `x86_64` | `advised` | PASS (R1, best R1) | 5 | — | — | $1.96 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.05 | — | not_run |
| `der_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.06 | — | not_run |
| `der_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | `advised` | FAIL (other) | 8 | — | — | $0.73 | — | not_run |
| `der_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $1.00 | — | not_run |
| `der_valid` | `google/gemini-4-neon` | `arm64` | `advised` | PASS (R5, best R5) | 8 | — | — | $1.96 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `google/gemini-4-neon` | `x86_64` | `advised` | PASS (R4, best R4) | 8 | — | — | $1.43 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `meta/muse-spark-open` | `arm64` | `advised` | PASS (R3, best R3) | 5 | — | — | $0.09 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `meta/muse-spark-open` | `x86_64` | `advised` | FAIL (compile_or_parse_error) | 8 | — | — | $0.15 | — | not_run |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.36 | — | not_run |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `advised` | FAIL (other) | 8 | — | — | $0.27 | — | not_run |
| `der_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | `advised` | PASS (R5, best R5) | 8 | — | — | $2.87 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | `advised` | PASS (R2, best R2) | 7 | — | — | $2.53 | refused | NATIVE_PASS 257/257 |
| `der_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `advised` | FAIL (other) | 8 | — | — | $0.44 | — | not_run |
| `der_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.44 | — | not_run |
| `der_valid` | `z-ai/glm-5.3-prime` | `arm64` | `advised` | FAIL (output_token_limit) | 8 | — | — | $0.65 | — | not_run |
| `der_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `advised` | FAIL (other) | 8 | — | — | $0.29 | — | not_run |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `arm64` | `advised` | PASS (R1, best R2) | 8 | 0.83 -> **0.54** | 4 B | $2.54 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `x86_64` | `advised` | PASS (R2, best R2) | 7 | 1.00 -> **1.00** | 2 B | $2.36 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.03 | — | not_run |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.03 | — | not_run |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | `advised` | FAIL (other) | 8 | — | — | $0.47 | — | not_run |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | `advised` | PASS (R1, best R1) | 5 | 1.00 -> **1.00** | 2 B | $0.31 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `google/gemini-4-neon` | `arm64` | `advised` | FAIL (arith_need_compare) | 8 | — | — | $1.45 | — | not_run |
| `ipv4_valid` | `google/gemini-4-neon` | `x86_64` | `advised` | FAIL (spec_need_open) | 8 | — | — | $1.71 | — | not_run |
| `ipv4_valid` | `meta/muse-spark-open` | `arm64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.09 | — | not_run |
| `ipv4_valid` | `meta/muse-spark-open` | `x86_64` | `advised` | FAIL (other) | 8 | — | — | $0.11 | — | not_run |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `advised` | FAIL (spec_need_open) | 8 | — | — | $0.25 | — | not_run |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `advised` | FAIL (spec_need_open) | 8 | — | — | $0.20 | — | not_run |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | `advised` | PASS (R1, best R4) | 7 | 0.54 -> **0.54** | 4 B | $1.88 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | `advised` | PASS (R8, best R8) | 8 | — | — | $2.64 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `advised` | PASS (R5, best R5) | 8 | — | — | $0.33 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `advised` | PASS (R6, best R6) | 8 | — | — | $0.36 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `arm64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.16 | — | not_run |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.12 | — | not_run |

## Failing Round Breakdown

Each row counts failing rounds across all cells by root-cause category.

| Failure category | Failing rounds |
| --- | --- |
| `other` | 176 |
| `arith_need_entail` | 109 |
| `compile_or_parse_error` | 46 |
| `spec_need_open` | 30 |
| `arith_need_compare` | 22 |
| `output_token_limit` | 13 |
| `trace_refusal` | 9 |
| `place_error` | 3 |
