# Results: Pre-Registered Cold-Room Suite `hl-reg-v2`

- **Pre-registration commit:** `eb00b06269e47f67c836ee20ea8c3519cf317d43`
- **Finished (UTC):** `2026-11-26T20:44:55Z`
- **Strict pass rate:** **34/72** finished cells
- **Independent second verifier (`verify2.py`):** **23/34** passing cells dual-verified
- **Real-silicon native harness:** **34/34** passing cells executed and passed on matching hardware
- **Total rounds / API spend:** 509 rounds, **$66.49** USD

## Cell-by-Cell Outcomes

Each row reports one cold-room cell: verdict, rounds used, API cost, compiled code size, `verify2.py` status, and real-silicon test result.

| Task | Model | Target | Arm | Verdict | Rounds | Initial -> Best `cyc/B` | Unroll (B/it) | Cost (USD) | `verify2.py` | Native CPU |
| --- | --- | --- | --- | --- | ---: | --- | ---: | ---: | --- | --- |
| `chacha20_4way` | `anthropic/claude-fable-5.2` | `arm64` | `advised` | PASS (R3, best R4) | 5 | 2.48 -> **2.34** | 256 B | $5.60 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-fable-5.2` | `x86_64` | `advised` | PASS (R4, best R6) | 6 | 3.58 -> **1.70** | 256 B | $3.85 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `advised` | PASS (R6, best R7) | 8 | 7.61 -> **2.48** | 256 B | $0.05 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `advised` | FAIL (other) | 8 | — | — | $0.06 | — | not_run |
| `chacha20_4way` | `anthropic/claude-sonnet-5.5` | `arm64` | `advised` | PASS (R2, best R3) | 4 | 7.61 -> **2.48** | 256 B | $0.27 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-sonnet-5.5` | `x86_64` | `advised` | PASS (R4, best R5) | 6 | 5.89 -> **3.58** | 256 B | $0.48 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `google/gemini-4-neon` | `arm64` | `advised` | PASS (R3, best R6) | 6 | 2.48 -> **2.33** | 256 B | $1.78 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `google/gemini-4-neon` | `x86_64` | `advised` | PASS (R4, best R4) | 5 | 1.72 -> **1.72** | 256 B | $1.79 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `meta/muse-spark-open` | `arm64` | `advised` | FAIL (compile_or_parse_error) | 8 | — | — | $0.27 | — | not_run |
| `chacha20_4way` | `meta/muse-spark-open` | `x86_64` | `advised` | FAIL (other) | 8 | — | — | $0.22 | — | not_run |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `advised` | PASS (R4, best R4) | 8 | 2.48 -> **2.48** | 256 B | $0.50 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `advised` | FAIL (compile_or_parse_error) | 8 | — | — | $0.48 | — | not_run |
| `chacha20_4way` | `openai/gpt-6.2-astra-pro` | `arm64` | `advised` | PASS (R2, best R6) | 6 | 2.34 -> **2.33** | 256 B | $3.29 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `openai/gpt-6.2-astra-pro` | `x86_64` | `advised` | PASS (R5, best R5) | 7 | 1.72 -> **1.72** | 256 B | $4.34 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `advised` | FAIL (other) | 8 | — | — | $0.40 | — | not_run |
| `chacha20_4way` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `advised` | FAIL (other) | 6 | — | — | $0.93 | — | not_run |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `arm64` | `advised` | PASS (R3, best R4) | 5 | 7.61 -> **2.48** | 256 B | $0.36 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `advised` | FAIL (output_token_limit) | 2 | — | — | $0.35 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `arm64` | `advised` | PASS (R2, best R2) | 6 | 2.00 -> **2.00** | 4 B | $1.89 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `x86_64` | `advised` | PASS (R3, best R3) | 6 | 2.50 -> **2.50** | 4 B | $2.21 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `arm64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.03 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `x86_64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.04 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `arm64` | `advised` | PASS (R2, best R2) | 4 | 2.04 -> **2.04** | 4 B | $0.21 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `x86_64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.60 | — | not_run |
| `ct_base64_decode` | `google/gemini-4-neon` | `arm64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $1.12 | — | not_run |
| `ct_base64_decode` | `google/gemini-4-neon` | `x86_64` | `advised` | FAIL (other) | 6 | — | — | $1.20 | — | not_run |
| `ct_base64_decode` | `meta/muse-spark-open` | `arm64` | `advised` | PASS (R5, best R5) | 8 | 2.38 -> **2.38** | 4 B | $0.15 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `meta/muse-spark-open` | `x86_64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.15 | — | not_run |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `arm64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.21 | — | not_run |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.23 | — | not_run |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `arm64` | `advised` | PASS (R3, best R7) | 7 | 2.04 -> **1.83** | 4 B | $1.69 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `x86_64` | `advised` | PASS (R2, best R5) | 8 | 2.50 -> **2.25** | 4 B | $2.36 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `advised` | PASS (R5, best R5) | 8 | 2.38 -> **2.38** | 4 B | $0.26 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `advised` | FAIL (prover_timeout) | 8 | — | — | $0.28 | — | not_run |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `arm64` | `advised` | PASS (R6, best R6) | 8 | 2.33 -> **2.33** | 4 B | $0.39 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `x86_64` | `advised` | FAIL (prover_timeout) | 8 | — | — | $0.33 | — | not_run |
| `der_valid` | `anthropic/claude-fable-5.2` | `arm64` | `advised` | PASS (R2, best R2) | 5 | — | — | $1.98 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-fable-5.2` | `x86_64` | `advised` | PASS (R4, best R4) | 7 | — | — | $3.75 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.04 | — | not_run |
| `der_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `advised` | FAIL (prover_timeout) | 8 | — | — | $0.05 | — | not_run |
| `der_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | `advised` | PASS (R1, best R1) | 3 | — | — | $0.28 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | `advised` | FAIL (arith_need_compare) | 8 | — | — | $0.94 | — | not_run |
| `der_valid` | `google/gemini-4-neon` | `arm64` | `advised` | PASS (R6, best R6) | 8 | — | — | $1.21 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `google/gemini-4-neon` | `x86_64` | `advised` | PASS (R4, best R4) | 8 | — | — | $1.09 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `meta/muse-spark-open` | `arm64` | `advised` | FAIL (compile_or_parse_error) | 8 | — | — | $0.14 | — | not_run |
| `der_valid` | `meta/muse-spark-open` | `x86_64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.16 | — | not_run |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.28 | — | not_run |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `advised` | FAIL (prover_timeout) | 8 | — | — | $0.28 | — | not_run |
| `der_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | `advised` | PASS (R5, best R5) | 8 | — | — | $2.96 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | `advised` | PASS (R3, best R3) | 7 | — | — | $2.64 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `advised` | PASS (R5, best R5) | 7 | — | — | $0.19 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.36 | — | not_run |
| `der_valid` | `z-ai/glm-5.3-prime` | `arm64` | `advised` | FAIL (output_token_limit) | 8 | — | — | $0.44 | — | not_run |
| `der_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `advised` | FAIL (trace_refusal) | 8 | — | — | $0.24 | — | not_run |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `arm64` | `advised` | PASS (R1, best R2) | 3 | 1.00 -> **0.62** | 4 B | $0.87 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `x86_64` | `advised` | PASS (R3, best R4) | 6 | 1.00 -> **0.75** | 4 B | $1.82 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `advised` | FAIL (prover_timeout) | 8 | — | — | $0.03 | — | not_run |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `advised` | FAIL (compile_or_parse_error) | 8 | — | — | $0.03 | — | not_run |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | `advised` | FAIL (prover_timeout) | 8 | — | — | $0.42 | — | not_run |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | `advised` | PASS (R1, best R1) | 4 | 1.00 -> **1.00** | 2 B | $0.25 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `google/gemini-4-neon` | `arm64` | `advised` | FAIL (prover_timeout) | 7 | — | — | $1.33 | — | not_run |
| `ipv4_valid` | `google/gemini-4-neon` | `x86_64` | `advised` | FAIL (other) | 8 | — | — | $1.36 | — | not_run |
| `ipv4_valid` | `meta/muse-spark-open` | `arm64` | `advised` | FAIL (compile_or_parse_error) | 8 | — | — | $0.25 | — | not_run |
| `ipv4_valid` | `meta/muse-spark-open` | `x86_64` | `advised` | FAIL (place_error) | 8 | — | — | $0.10 | — | not_run |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `advised` | FAIL (compile_or_parse_error) | 8 | — | — | $0.22 | — | not_run |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `advised` | FAIL (other) | 8 | — | — | $0.18 | — | not_run |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | `advised` | PASS (R1, best R3) | 5 | 0.62 -> **0.54** | 4 B | $1.26 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | `advised` | PASS (R4, best R4) | 8 | — | — | $2.13 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `advised` | PASS (R4, best R4) | 8 | — | — | $0.19 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `advised` | FAIL (other) | 8 | — | — | $0.21 | — | not_run |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `arm64` | `advised` | FAIL (other) | 8 | — | — | $0.21 | — | not_run |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `advised` | PASS (R5, best R5) | 8 | — | — | $0.28 | shown | NATIVE_PASS 607/607 |

## Failing Round Breakdown

Each row counts failing rounds across all cells by root-cause category.

| Failure category | Failing rounds |
| --- | --- |
| `other` | 99 |
| `arith_need_entail` | 93 |
| `compile_or_parse_error` | 93 |
| `prover_timeout` | 80 |
| `arith_need_compare` | 23 |
| `spec_need_open` | 13 |
| `isa_table_error` | 6 |
| `trace_refusal` | 6 |
| `output_token_limit` | 4 |
| `place_error` | 3 |

## Before vs. After Comparison (`hl-reg-v1` -> `hl-reg-v2`)

The first table compares totals over the 72 cells that both runs have (the same task, model, target, and arm); each cell was run once in each run, so a difference in one cell may be chance. The second table sets each such cell of the two runs side by side.

| Metric (over the 72 shared cells) | `hl-reg-v1` | `hl-reg-v2` | Delta |
| --- | --- | --- | --- |
| Strict passes | 21/72 | 34/72 | +13 |
| Total rounds | 521 | 509 | -12 |
| Total API spend (USD) | $64.32 | $66.49 | $+2.17 |
| Failing rounds: `arith_need_compare` | 24 | 23 | -1 |
| Failing rounds: `arith_need_entail` | 181 | 93 | -88 |
| Failing rounds: `compile_or_parse_error` | 163 | 93 | -70 |
| Failing rounds: `isa_table_error` | 1 | 6 | +5 |
| Failing rounds: `other` | 81 | 99 | +18 |
| Failing rounds: `output_token_limit` | 10 | 4 | -6 |
| Failing rounds: `place_error` | 2 | 3 | +1 |
| Failing rounds: `prover_timeout` | 0 | 80 | +80 |
| Failing rounds: `spec_need_open` | 0 | 13 | +13 |
| Failing rounds: `trace_refusal` | 4 | 6 | +2 |

| Task | Model | Target | Arm | `hl-reg-v1` | `hl-reg-v2` |
| --- | --- | --- | --- | --- | --- |
| `chacha20_4way` | `anthropic/claude-fable-5.2` | `arm64` | `advised` | FAIL ($4.52) | PASS (R3, $5.60) |
| `chacha20_4way` | `anthropic/claude-fable-5.2` | `x86_64` | `advised` | PASS (R8, $5.11) | PASS (R4, $3.85) |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `advised` | FAIL ($0.06) | PASS (R6, $0.05) |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `advised` | FAIL ($0.06) | FAIL ($0.06) |
| `chacha20_4way` | `anthropic/claude-sonnet-5.5` | `arm64` | `advised` | PASS (R1, $0.45) | PASS (R2, $0.27) |
| `chacha20_4way` | `anthropic/claude-sonnet-5.5` | `x86_64` | `advised` | FAIL ($0.98) | PASS (R4, $0.48) |
| `chacha20_4way` | `google/gemini-4-neon` | `arm64` | `advised` | FAIL ($1.60) | PASS (R3, $1.78) |
| `chacha20_4way` | `google/gemini-4-neon` | `x86_64` | `advised` | PASS (R3, $1.76) | PASS (R4, $1.79) |
| `chacha20_4way` | `meta/muse-spark-open` | `arm64` | `advised` | FAIL ($0.19) | FAIL ($0.27) |
| `chacha20_4way` | `meta/muse-spark-open` | `x86_64` | `advised` | FAIL ($0.22) | FAIL ($0.22) |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `advised` | FAIL ($0.39) | PASS (R4, $0.50) |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `advised` | FAIL ($0.53) | FAIL ($0.48) |
| `chacha20_4way` | `openai/gpt-6.2-astra-pro` | `arm64` | `advised` | FAIL ($2.94) | PASS (R2, $3.29) |
| `chacha20_4way` | `openai/gpt-6.2-astra-pro` | `x86_64` | `advised` | PASS (R3, $3.12) | PASS (R5, $4.34) |
| `chacha20_4way` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `advised` | FAIL ($0.52) | FAIL ($0.40) |
| `chacha20_4way` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `advised` | FAIL ($0.56) | FAIL ($0.93) |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `arm64` | `advised` | FAIL ($0.45) | PASS (R3, $0.36) |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `advised` | FAIL ($0.77) | FAIL ($0.35) |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `arm64` | `advised` | PASS (R4, $2.26) | PASS (R2, $1.89) |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `x86_64` | `advised` | FAIL ($4.30) | PASS (R3, $2.21) |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `arm64` | `advised` | FAIL ($0.04) | FAIL ($0.03) |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `x86_64` | `advised` | FAIL ($0.04) | FAIL ($0.04) |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `arm64` | `advised` | PASS (R2, $0.42) | PASS (R2, $0.21) |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `x86_64` | `advised` | FAIL ($0.56) | FAIL ($0.60) |
| `ct_base64_decode` | `google/gemini-4-neon` | `arm64` | `advised` | FAIL ($1.30) | FAIL ($1.12) |
| `ct_base64_decode` | `google/gemini-4-neon` | `x86_64` | `advised` | FAIL ($1.07) | FAIL ($1.20) |
| `ct_base64_decode` | `meta/muse-spark-open` | `arm64` | `advised` | FAIL ($0.18) | PASS (R5, $0.15) |
| `ct_base64_decode` | `meta/muse-spark-open` | `x86_64` | `advised` | FAIL ($0.25) | FAIL ($0.15) |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `arm64` | `advised` | FAIL ($0.21) | FAIL ($0.21) |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `advised` | FAIL ($0.24) | FAIL ($0.23) |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `arm64` | `advised` | PASS (R4, $1.15) | PASS (R3, $1.69) |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `x86_64` | `advised` | FAIL ($1.18) | PASS (R2, $2.36) |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `advised` | FAIL ($0.21) | PASS (R5, $0.26) |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `advised` | FAIL ($0.31) | FAIL ($0.28) |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `arm64` | `advised` | FAIL ($0.29) | PASS (R6, $0.39) |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `x86_64` | `advised` | FAIL ($0.41) | FAIL ($0.33) |
| `der_valid` | `anthropic/claude-fable-5.2` | `arm64` | `advised` | FAIL ($2.99) | PASS (R2, $1.98) |
| `der_valid` | `anthropic/claude-fable-5.2` | `x86_64` | `advised` | PASS (R1, $1.93) | PASS (R4, $3.75) |
| `der_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `advised` | FAIL ($0.04) | FAIL ($0.04) |
| `der_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `advised` | FAIL ($0.05) | FAIL ($0.05) |
| `der_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | `advised` | FAIL ($0.89) | PASS (R1, $0.28) |
| `der_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | `advised` | PASS (R1, $0.30) | FAIL ($0.94) |
| `der_valid` | `google/gemini-4-neon` | `arm64` | `advised` | PASS (R2, $1.26) | PASS (R6, $1.21) |
| `der_valid` | `google/gemini-4-neon` | `x86_64` | `advised` | PASS (R6, $1.45) | PASS (R4, $1.09) |
| `der_valid` | `meta/muse-spark-open` | `arm64` | `advised` | FAIL ($0.17) | FAIL ($0.14) |
| `der_valid` | `meta/muse-spark-open` | `x86_64` | `advised` | FAIL ($0.17) | FAIL ($0.16) |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `advised` | PASS (R6, $0.28) | FAIL ($0.28) |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `advised` | PASS (R4, $0.32) | FAIL ($0.28) |
| `der_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | `advised` | PASS (R2, $1.19) | PASS (R5, $2.96) |
| `der_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | `advised` | PASS (R1, $1.47) | PASS (R3, $2.64) |
| `der_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `advised` | FAIL ($0.32) | PASS (R5, $0.19) |
| `der_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `advised` | FAIL ($0.29) | FAIL ($0.36) |
| `der_valid` | `z-ai/glm-5.3-prime` | `arm64` | `advised` | FAIL ($0.40) | FAIL ($0.44) |
| `der_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `advised` | FAIL ($0.55) | FAIL ($0.24) |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `arm64` | `advised` | PASS (R2, $2.31) | PASS (R1, $0.87) |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `x86_64` | `advised` | PASS (R4, $2.44) | PASS (R3, $1.82) |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `advised` | FAIL ($0.02) | FAIL ($0.03) |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `advised` | FAIL ($0.03) | FAIL ($0.03) |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | `advised` | PASS (R3, $0.25) | FAIL ($0.42) |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | `advised` | PASS (R2, $0.38) | PASS (R1, $0.25) |
| `ipv4_valid` | `google/gemini-4-neon` | `arm64` | `advised` | FAIL ($1.01) | FAIL ($1.33) |
| `ipv4_valid` | `google/gemini-4-neon` | `x86_64` | `advised` | FAIL ($1.08) | FAIL ($1.36) |
| `ipv4_valid` | `meta/muse-spark-open` | `arm64` | `advised` | FAIL ($0.12) | FAIL ($0.25) |
| `ipv4_valid` | `meta/muse-spark-open` | `x86_64` | `advised` | FAIL ($0.10) | FAIL ($0.10) |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `advised` | FAIL ($0.18) | FAIL ($0.22) |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `advised` | FAIL ($0.32) | FAIL ($0.18) |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | `advised` | PASS (R5, $1.02) | PASS (R1, $1.26) |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | `advised` | PASS (R4, $1.15) | PASS (R4, $2.13) |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `advised` | FAIL ($0.22) | PASS (R4, $0.19) |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `advised` | FAIL ($0.34) | FAIL ($0.21) |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `arm64` | `advised` | FAIL ($0.27) | FAIL ($0.21) |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `advised` | FAIL ($0.42) | PASS (R5, $0.28) |
