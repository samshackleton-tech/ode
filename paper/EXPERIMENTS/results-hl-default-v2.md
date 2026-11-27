# Results: Pre-Registered Cold-Room Suite `hl-default-v2`

- **Pre-registration commit:** `8ea6ec5c7df49de99aa445f05efb8bd4d625610b`
- **Finished (UTC):** `2026-11-27T16:08:16Z`
- **Strict pass rate:** **32/80** finished cells
- **Independent second verifier (`verify2.py`):** **16/32** passing cells dual-verified
- **Real-silicon native harness:** **32/32** passing cells executed and passed on matching hardware
- **Total rounds / API spend:** 413 rounds, **$24.70** USD

## Cell-by-Cell Outcomes

Each row reports one cold-room cell: verdict, rounds used, API cost, compiled code size, `verify2.py` status, and real-silicon test result.

| Task | Model | Target | Arm | Verdict | Rounds | Initial -> Best `cyc/B` | Unroll (B/it) | Cost (USD) | `verify2.py` | Native CPU |
| --- | --- | --- | --- | --- | ---: | --- | ---: | ---: | --- | --- |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.06 | — | not_run |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.05 | — | not_run |
| `blake3_compress1` | `google/gemini-4-neon` | `arm64` | `ode` | PASS (R2, best R2) | 2 | 5.47 -> **5.47** | 64 B | $0.54 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `google/gemini-4-neon` | `x86_64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.60 | — | not_run |
| `blake3_compress1` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.24 | — | not_run |
| `blake3_compress1` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.23 | — | not_run |
| `blake3_compress1` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.39 | — | not_run |
| `blake3_compress1` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R2, best R2) | 2 | 4.98 -> **4.98** | 64 B | $0.19 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.20 | — | not_run |
| `blake3_compress1` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (output_token_limit) | 7 | — | — | $0.47 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.02 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.05 | — | not_run |
| `blake3_compress_4way` | `google/gemini-4-neon` | `arm64` | `ode` | PASS (R6, best R6) | 6 | 3.45 -> **3.45** | 256 B | $1.65 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `google/gemini-4-neon` | `x86_64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.60 | — | not_run |
| `blake3_compress_4way` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.32 | — | not_run |
| `blake3_compress_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.19 | — | not_run |
| `blake3_compress_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.36 | — | not_run |
| `blake3_compress_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R3, best R3) | 3 | 1.63 -> **1.63** | 256 B | $0.28 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.37 | — | not_run |
| `blake3_compress_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.20 | — | not_run |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R1, best R1) | 1 | 7.58 -> **7.58** | 256 B | $0.00 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | PASS (R2, best R2) | 2 | 5.89 -> **5.89** | 256 B | $0.01 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `google/gemini-4-neon` | `arm64` | `ode` | PASS (R1, best R1) | 1 | 2.63 -> **2.63** | 256 B | $0.27 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `google/gemini-4-neon` | `x86_64` | `ode` | PASS (R2, best R2) | 2 | 2.04 -> **2.04** | 256 B | $0.58 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.17 | — | not_run |
| `chacha20_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.19 | — | not_run |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R5, best R5) | 5 | 2.41 -> **2.41** | 256 B | $0.20 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R4, best R4) | 4 | 5.89 -> **5.89** | 256 B | $0.29 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R1, best R1) | 1 | 7.58 -> **7.58** | 256 B | $0.04 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (output_token_limit) | 7 | — | — | $0.46 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.03 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.03 | — | not_run |
| `ct_base64_decode` | `google/gemini-4-neon` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.94 | — | not_run |
| `ct_base64_decode` | `google/gemini-4-neon` | `x86_64` | `ode` | PASS (R5, best R5) | 5 | 2.25 -> **2.25** | 4 B | $0.89 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.11 | — | not_run |
| `ct_base64_decode` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.12 | — | not_run |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.15 | — | not_run |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.14 | — | not_run |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.26 | — | not_run |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R2, best R2) | 2 | 3.00 -> **3.00** | 4 B | $0.07 | shown | NATIVE_PASS 333/333 |
| `der_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.04 | — | not_run |
| `der_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.04 | — | not_run |
| `der_valid` | `google/gemini-4-neon` | `arm64` | `ode` | PASS (R5, best R5) | 5 | — | — | $0.83 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `google/gemini-4-neon` | `x86_64` | `ode` | PASS (R3, best R3) | 3 | — | — | $0.56 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.12 | — | not_run |
| `der_valid` | `meta/muse-spark-open` | `x86_64` | `ode` | PASS (R6, best R6) | 6 | — | — | $0.13 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.23 | — | not_run |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R5, best R5) | 5 | — | — | $0.18 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.36 | — | not_run |
| `der_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R5, best R5) | 5 | — | — | $0.18 | shown | NATIVE_PASS 257/257 |
| `ebpf` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.04 | — | not_run |
| `ebpf` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.04 | — | not_run |
| `ebpf` | `google/gemini-4-neon` | `arm64` | `ode` | PASS (R2, best R2) | 2 | 0.05 -> **0.05** | 406 B | $0.34 | shown | NATIVE_PASS 7/7 |
| `ebpf` | `google/gemini-4-neon` | `x86_64` | `ode` | FAIL (output_token_limit) | 7 | — | — | $0.89 | — | not_run |
| `ebpf` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.15 | — | not_run |
| `ebpf` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (place_error) | 7 | — | — | $0.15 | — | not_run |
| `ebpf` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (arith_need_compare) | 7 | — | — | $0.19 | — | not_run |
| `ebpf` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (arith_need_compare) | 7 | — | — | $0.25 | — | not_run |
| `ebpf` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.26 | — | not_run |
| `ebpf` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (arith_need_compare) | 7 | — | — | $0.18 | — | not_run |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R1, best R1) | 1 | 1.00 -> **1.00** | 2 B | $0.00 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | PASS (R1, best R1) | 1 | 1.00 -> **1.00** | 2 B | $0.00 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `google/gemini-4-neon` | `arm64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $1.08 | — | not_run |
| `ipv4_valid` | `google/gemini-4-neon` | `x86_64` | `ode` | FAIL (spec_need_open) | 7 | — | — | $0.99 | — | not_run |
| `ipv4_valid` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R1, best R1) | 1 | 0.83 -> **0.83** | 2 B | $0.03 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `meta/muse-spark-open` | `x86_64` | `ode` | PASS (R3, best R3) | 3 | 1.00 -> **1.00** | 2 B | $0.06 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R6, best R6) | 6 | — | — | $0.17 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R6, best R6) | 6 | 1.00 -> **1.00** | 2 B | $0.16 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R5, best R5) | 5 | — | — | $0.25 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R1, best R1) | 1 | 1.00 -> **1.00** | 2 B | $0.03 | shown | NATIVE_PASS 607/607 |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.04 | — | not_run |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | PASS (R1, best R1) | 1 | 4.81 -> **4.81** | 256 B | $0.01 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `google/gemini-4-neon` | `arm64` | `ode` | PASS (R7, best R7) | 7 | 0.03 -> **0.03** | 256 B | $1.71 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `google/gemini-4-neon` | `x86_64` | `ode` | PASS (R6, best R6) | 6 | 1.05 -> **1.05** | 256 B | $1.45 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.11 | — | not_run |
| `sha256_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.19 | — | not_run |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R4, best R4) | 4 | 1.02 -> **1.02** | 256 B | $0.47 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R4, best R4) | 4 | — | — | $0.19 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.20 | — | not_run |
| `sha256_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (output_token_limit) | 6 | — | — | $0.42 | — | not_run |

## Failing Round Breakdown

Each row counts failing rounds across all cells by root-cause category.

| Failure category | Failing rounds |
| --- | --- |
| `compile_or_parse_error` | 131 |
| `other` | 111 |
| `arith_need_entail` | 68 |
| `output_token_limit` | 31 |
| `arith_need_compare` | 17 |
| `spec_need_open` | 11 |
| `isa_table_error` | 5 |
| `place_error` | 4 |
| `contract_id_mismatch` | 2 |
| `trace_refusal` | 1 |

## Before vs. After Comparison (`hl-default-v1` -> `hl-default-v2`)

The first table compares totals over the 80 cells that both runs have (the same task, model, target, and arm); each cell was run once in each run, so a difference in one cell may be chance. The second table sets each such cell of the two runs side by side.

| Metric (over the 80 shared cells) | `hl-default-v1` | `hl-default-v2` | Delta |
| --- | --- | --- | --- |
| Strict passes | 28/80 | 32/80 | +4 |
| Total rounds | 538 | 413 | -125 |
| Total API spend (USD) | $35.76 | $24.70 | $-11.06 |
| Failing rounds: `arith_need_compare` | 46 | 17 | -29 |
| Failing rounds: `arith_need_entail` | 92 | 68 | -24 |
| Failing rounds: `compile_or_parse_error` | 158 | 131 | -27 |
| Failing rounds: `contract_id_mismatch` | 0 | 2 | +2 |
| Failing rounds: `isa_table_error` | 5 | 5 | +0 |
| Failing rounds: `other` | 153 | 111 | -42 |
| Failing rounds: `output_token_limit` | 13 | 31 | +18 |
| Failing rounds: `place_error` | 0 | 4 | +4 |
| Failing rounds: `spec_need_open` | 18 | 11 | -7 |
| Failing rounds: `trace_refusal` | 1 | 1 | +0 |

| Task | Model | Target | Arm | `hl-default-v1` | `hl-default-v2` |
| --- | --- | --- | --- | --- | --- |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.07) | FAIL ($0.06) |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.09) | FAIL ($0.05) |
| `blake3_compress1` | `google/gemini-4-neon` | `arm64` | `ode` | PASS (R1, $0.94) | PASS (R2, $0.54) |
| `blake3_compress1` | `google/gemini-4-neon` | `x86_64` | `ode` | PASS (R1, $0.90) | FAIL ($0.60) |
| `blake3_compress1` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL ($0.25) | FAIL ($0.24) |
| `blake3_compress1` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.27) | FAIL ($0.23) |
| `blake3_compress1` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL ($0.47) | FAIL ($0.39) |
| `blake3_compress1` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL ($0.45) | PASS (R2, $0.19) |
| `blake3_compress1` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.36) | FAIL ($0.20) |
| `blake3_compress1` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.51) | FAIL ($0.47) |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.08) | FAIL ($0.02) |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.07) | FAIL ($0.05) |
| `blake3_compress_4way` | `google/gemini-4-neon` | `arm64` | `ode` | PASS (R5, $2.48) | PASS (R6, $1.65) |
| `blake3_compress_4way` | `google/gemini-4-neon` | `x86_64` | `ode` | PASS (R2, $1.51) | FAIL ($0.60) |
| `blake3_compress_4way` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL ($0.29) | FAIL ($0.32) |
| `blake3_compress_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.45) | FAIL ($0.19) |
| `blake3_compress_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL ($0.59) | FAIL ($0.36) |
| `blake3_compress_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R5, $0.77) | PASS (R3, $0.28) |
| `blake3_compress_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($1.02) | FAIL ($0.37) |
| `blake3_compress_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.68) | FAIL ($0.20) |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R3, $0.03) | PASS (R1, $0.00) |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.04) | PASS (R2, $0.01) |
| `chacha20_4way` | `google/gemini-4-neon` | `arm64` | `ode` | PASS (R1, $0.64) | PASS (R1, $0.27) |
| `chacha20_4way` | `google/gemini-4-neon` | `x86_64` | `ode` | PASS (R1, $0.92) | PASS (R2, $0.58) |
| `chacha20_4way` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R6, $0.16) | FAIL ($0.17) |
| `chacha20_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.50) | FAIL ($0.19) |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R1, $0.15) | PASS (R5, $0.20) |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R6, $0.40) | PASS (R4, $0.29) |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R1, $0.23) | PASS (R1, $0.04) |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.37) | FAIL ($0.46) |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.03) | FAIL ($0.03) |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.04) | FAIL ($0.03) |
| `ct_base64_decode` | `google/gemini-4-neon` | `arm64` | `ode` | FAIL ($1.61) | FAIL ($0.94) |
| `ct_base64_decode` | `google/gemini-4-neon` | `x86_64` | `ode` | FAIL ($1.05) | PASS (R5, $0.89) |
| `ct_base64_decode` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL ($0.13) | FAIL ($0.11) |
| `ct_base64_decode` | `meta/muse-spark-open` | `x86_64` | `ode` | PASS (R2, $0.09) | FAIL ($0.12) |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL ($0.16) | FAIL ($0.15) |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL ($0.20) | FAIL ($0.14) |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.25) | FAIL ($0.26) |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R2, $0.12) | PASS (R2, $0.07) |
| `der_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.04) | FAIL ($0.04) |
| `der_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.06) | FAIL ($0.04) |
| `der_valid` | `google/gemini-4-neon` | `arm64` | `ode` | PASS (R6, $0.69) | PASS (R5, $0.83) |
| `der_valid` | `google/gemini-4-neon` | `x86_64` | `ode` | PASS (R7, $1.14) | PASS (R3, $0.56) |
| `der_valid` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL ($0.18) | FAIL ($0.12) |
| `der_valid` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.16) | PASS (R6, $0.13) |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R7, $0.33) | FAIL ($0.23) |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R3, $0.11) | PASS (R5, $0.18) |
| `der_valid` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R7, $0.22) | FAIL ($0.36) |
| `der_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.31) | PASS (R5, $0.18) |
| `ebpf` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.04) | FAIL ($0.04) |
| `ebpf` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.05) | FAIL ($0.04) |
| `ebpf` | `google/gemini-4-neon` | `arm64` | `ode` | PASS (R2, $0.61) | PASS (R2, $0.34) |
| `ebpf` | `google/gemini-4-neon` | `x86_64` | `ode` | FAIL ($1.26) | FAIL ($0.89) |
| `ebpf` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL ($0.18) | FAIL ($0.15) |
| `ebpf` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.16) | FAIL ($0.15) |
| `ebpf` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL ($0.23) | FAIL ($0.19) |
| `ebpf` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL ($0.24) | FAIL ($0.25) |
| `ebpf` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.47) | FAIL ($0.26) |
| `ebpf` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.43) | FAIL ($0.18) |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R2, $0.01) | PASS (R1, $0.00) |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | PASS (R2, $0.01) | PASS (R1, $0.00) |
| `ipv4_valid` | `google/gemini-4-neon` | `arm64` | `ode` | FAIL ($1.33) | FAIL ($1.08) |
| `ipv4_valid` | `google/gemini-4-neon` | `x86_64` | `ode` | FAIL ($1.22) | FAIL ($0.99) |
| `ipv4_valid` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R4, $0.07) | PASS (R1, $0.03) |
| `ipv4_valid` | `meta/muse-spark-open` | `x86_64` | `ode` | PASS (R4, $0.09) | PASS (R3, $0.06) |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL ($0.16) | PASS (R6, $0.17) |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL ($0.17) | PASS (R6, $0.16) |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R7, $0.21) | PASS (R5, $0.25) |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R2, $0.14) | PASS (R1, $0.03) |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.06) | FAIL ($0.04) |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.05) | PASS (R1, $0.01) |
| `sha256_4way` | `google/gemini-4-neon` | `arm64` | `ode` | PASS (R2, $1.34) | PASS (R7, $1.71) |
| `sha256_4way` | `google/gemini-4-neon` | `x86_64` | `ode` | PASS (R1, $1.57) | PASS (R6, $1.45) |
| `sha256_4way` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL ($0.21) | FAIL ($0.11) |
| `sha256_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.27) | FAIL ($0.19) |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL ($0.39) | PASS (R4, $0.47) |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL ($0.41) | PASS (R4, $0.19) |
| `sha256_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.96) | FAIL ($0.20) |
| `sha256_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.80) | FAIL ($0.42) |
