# Results: Pre-Registered Cold-Room Suite `hl-default-v3`

- **Pre-registration commit:** `701dd25027082270897005be25600d455177d267`
- **Finished (UTC):** `2026-11-27T19:43:16Z`
- **Strict pass rate:** **17/64** finished cells
- **Independent second verifier (`verify2.py`):** **10/17** passing cells dual-verified
- **Real-silicon native harness:** **17/17** passing cells executed and passed on matching hardware
- **Total rounds / API spend:** 354 rounds, **$13.61** USD

## Cell-by-Cell Outcomes

Each row reports one cold-room cell: verdict, rounds used, API cost, compiled code size, `verify2.py` status, and real-silicon test result.

| Task | Model | Target | Arm | Verdict | Rounds | Initial -> Best `cyc/B` | Unroll (B/it) | Cost (USD) | `verify2.py` | Native CPU |
| --- | --- | --- | --- | --- | ---: | --- | ---: | ---: | --- | --- |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.04 | — | not_run |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.07 | — | not_run |
| `blake3_compress1` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.16 | — | not_run |
| `blake3_compress1` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.25 | — | not_run |
| `blake3_compress1` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R2, best R2) | 2 | — | — | $0.41 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.93 | — | not_run |
| `blake3_compress1` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.20 | — | not_run |
| `blake3_compress1` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.37 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.05 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.05 | — | not_run |
| `blake3_compress_4way` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.19 | — | not_run |
| `blake3_compress_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.17 | — | not_run |
| `blake3_compress_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.72 | — | not_run |
| `blake3_compress_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.94 | — | not_run |
| `blake3_compress_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.20 | — | not_run |
| `blake3_compress_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.20 | — | not_run |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R3, best R3) | 3 | 2.41 -> **2.41** | 256 B | $0.02 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.04 | — | not_run |
| `chacha20_4way` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R4, best R4) | 4 | 2.42 -> **2.42** | 256 B | $0.11 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.43 | — | not_run |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R5, best R5) | 5 | 8.23 -> **8.23** | 256 B | $0.39 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R2, best R2) | 2 | 2.07 -> **2.07** | 256 B | $0.24 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R1, best R1) | 1 | 4.58 -> **4.58** | 256 B | $0.05 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.20 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.03 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.03 | — | not_run |
| `ct_base64_decode` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R6, best R6) | 6 | 2.71 -> **2.71** | 4 B | $0.11 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.21 | — | not_run |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.21 | — | not_run |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.29 | — | not_run |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R3, best R3) | 3 | 2.33 -> **2.33** | 4 B | $0.09 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.24 | — | not_run |
| `der_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.04 | — | not_run |
| `der_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (spec_need_open) | 7 | — | — | $0.04 | — | not_run |
| `der_valid` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.15 | — | not_run |
| `der_valid` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.15 | — | not_run |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R4, best R4) | 4 | — | — | $0.39 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.48 | — | not_run |
| `der_valid` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (spec_need_open) | 7 | — | — | $0.25 | — | not_run |
| `der_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (output_token_limit) | 7 | — | — | $0.33 | — | not_run |
| `ebpf` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (arith_need_compare) | 7 | — | — | $0.04 | — | not_run |
| `ebpf` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.04 | — | not_run |
| `ebpf` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (arith_need_compare) | 7 | — | — | $0.16 | — | not_run |
| `ebpf` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.16 | — | not_run |
| `ebpf` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (arith_need_compare) | 7 | — | — | $0.38 | — | not_run |
| `ebpf` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (arith_need_compare) | 7 | — | — | $0.33 | — | not_run |
| `ebpf` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.21 | — | not_run |
| `ebpf` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.22 | — | not_run |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R2, best R2) | 2 | 1.00 -> **1.00** | 2 B | $0.01 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | PASS (R2, best R2) | 2 | 1.00 -> **1.00** | 2 B | $0.01 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R1, best R1) | 1 | 0.92 -> **0.92** | 2 B | $0.04 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `meta/muse-spark-open` | `x86_64` | `ode` | PASS (R5, best R5) | 5 | 1.00 -> **1.00** | 2 B | $0.10 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.29 | — | not_run |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R7, best R7) | 7 | 1.50 -> **1.50** | 2 B | $0.25 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R3, best R3) | 3 | 0.92 -> **0.92** | 2 B | $0.05 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R2, best R2) | 2 | 1.00 -> **1.00** | 2 B | $0.04 | shown | NATIVE_PASS 607/607 |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R3, best R3) | 3 | 1.05 -> **1.05** | 256 B | $0.03 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.04 | — | not_run |
| `sha256_4way` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.24 | — | not_run |
| `sha256_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.14 | — | not_run |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.50 | — | not_run |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (contract_id_mismatch) | 7 | — | — | $0.47 | — | not_run |
| `sha256_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.20 | — | not_run |
| `sha256_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.20 | — | not_run |

## Failing Round Breakdown

Each row counts failing rounds across all cells by root-cause category.

| Failure category | Failing rounds |
| --- | --- |
| `compile_or_parse_error` | 126 |
| `other` | 111 |
| `arith_need_entail` | 48 |
| `output_token_limit` | 21 |
| `arith_need_compare` | 16 |
| `spec_need_open` | 7 |
| `contract_id_mismatch` | 5 |
| `trace_refusal` | 2 |
| `place_error` | 1 |

## Before vs. After Comparison (`hl-default-v2` -> `hl-default-v3`)

The first table compares totals over the 64 cells that both runs have (the same task, model, target, and arm); each cell was run once in each run, so a difference in one cell may be chance. The second table sets each such cell of the two runs side by side.

| Metric (over the 64 shared cells) | `hl-default-v2` | `hl-default-v3` | Delta |
| --- | --- | --- | --- |
| Strict passes | 22/64 | 17/64 | -5 |
| Total rounds | 342 | 354 | +12 |
| Total API spend (USD) | $10.77 | $13.61 | $+2.84 |
| Failing rounds: `arith_need_compare` | 15 | 16 | +1 |
| Failing rounds: `arith_need_entail` | 49 | 48 | -1 |
| Failing rounds: `compile_or_parse_error` | 121 | 126 | +5 |
| Failing rounds: `contract_id_mismatch` | 2 | 5 | +3 |
| Failing rounds: `isa_table_error` | 5 | 0 | -5 |
| Failing rounds: `other` | 96 | 111 | +15 |
| Failing rounds: `output_token_limit` | 18 | 21 | +3 |
| Failing rounds: `place_error` | 3 | 1 | -2 |
| Failing rounds: `spec_need_open` | 10 | 7 | -3 |
| Failing rounds: `trace_refusal` | 1 | 2 | +1 |

| Task | Model | Target | Arm | `hl-default-v2` | `hl-default-v3` |
| --- | --- | --- | --- | --- | --- |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.06) | FAIL ($0.04) |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.05) | FAIL ($0.07) |
| `blake3_compress1` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL ($0.24) | FAIL ($0.16) |
| `blake3_compress1` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.23) | FAIL ($0.25) |
| `blake3_compress1` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL ($0.39) | PASS (R2, $0.41) |
| `blake3_compress1` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R2, $0.19) | FAIL ($0.93) |
| `blake3_compress1` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.20) | FAIL ($0.20) |
| `blake3_compress1` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.47) | FAIL ($0.37) |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.02) | FAIL ($0.05) |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.05) | FAIL ($0.05) |
| `blake3_compress_4way` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL ($0.32) | FAIL ($0.19) |
| `blake3_compress_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.19) | FAIL ($0.17) |
| `blake3_compress_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL ($0.36) | FAIL ($0.72) |
| `blake3_compress_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R3, $0.28) | FAIL ($0.94) |
| `blake3_compress_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.37) | FAIL ($0.20) |
| `blake3_compress_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.20) | FAIL ($0.20) |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R1, $0.00) | PASS (R3, $0.02) |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | PASS (R2, $0.01) | FAIL ($0.04) |
| `chacha20_4way` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL ($0.17) | PASS (R4, $0.11) |
| `chacha20_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.19) | FAIL ($0.43) |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R5, $0.20) | PASS (R5, $0.39) |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R4, $0.29) | PASS (R2, $0.24) |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R1, $0.04) | PASS (R1, $0.05) |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.46) | FAIL ($0.20) |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.03) | FAIL ($0.03) |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.03) | FAIL ($0.03) |
| `ct_base64_decode` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL ($0.11) | PASS (R6, $0.11) |
| `ct_base64_decode` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.12) | FAIL ($0.21) |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL ($0.15) | FAIL ($0.21) |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL ($0.14) | FAIL ($0.29) |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.26) | PASS (R3, $0.09) |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R2, $0.07) | FAIL ($0.24) |
| `der_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.04) | FAIL ($0.04) |
| `der_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.04) | FAIL ($0.04) |
| `der_valid` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL ($0.12) | FAIL ($0.15) |
| `der_valid` | `meta/muse-spark-open` | `x86_64` | `ode` | PASS (R6, $0.13) | FAIL ($0.15) |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL ($0.23) | PASS (R4, $0.39) |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R5, $0.18) | FAIL ($0.48) |
| `der_valid` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.36) | FAIL ($0.25) |
| `der_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R5, $0.18) | FAIL ($0.33) |
| `ebpf` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.04) | FAIL ($0.04) |
| `ebpf` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.04) | FAIL ($0.04) |
| `ebpf` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL ($0.15) | FAIL ($0.16) |
| `ebpf` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.15) | FAIL ($0.16) |
| `ebpf` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL ($0.19) | FAIL ($0.38) |
| `ebpf` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL ($0.25) | FAIL ($0.33) |
| `ebpf` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.26) | FAIL ($0.21) |
| `ebpf` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.18) | FAIL ($0.22) |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R1, $0.00) | PASS (R2, $0.01) |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | PASS (R1, $0.00) | PASS (R2, $0.01) |
| `ipv4_valid` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R1, $0.03) | PASS (R1, $0.04) |
| `ipv4_valid` | `meta/muse-spark-open` | `x86_64` | `ode` | PASS (R3, $0.06) | PASS (R5, $0.10) |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R6, $0.17) | FAIL ($0.29) |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R6, $0.16) | PASS (R7, $0.25) |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R5, $0.25) | PASS (R3, $0.05) |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R1, $0.03) | PASS (R2, $0.04) |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.04) | PASS (R3, $0.03) |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | PASS (R1, $0.01) | FAIL ($0.04) |
| `sha256_4way` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL ($0.11) | FAIL ($0.24) |
| `sha256_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.19) | FAIL ($0.14) |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R4, $0.47) | FAIL ($0.50) |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R4, $0.19) | FAIL ($0.47) |
| `sha256_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.20) | FAIL ($0.20) |
| `sha256_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.42) | FAIL ($0.20) |
