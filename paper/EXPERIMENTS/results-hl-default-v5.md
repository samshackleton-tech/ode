# Results: Pre-Registered Cold-Room Suite `hl-default-v5`

- **Pre-registration commit:** `9d593275cf04145673d218d29cd4416917649b44`
- **Finished (UTC):** `2026-11-27T20:34:17Z`
- **Strict pass rate:** **21/64** finished cells
- **Independent second verifier (`verify2.py`):** **12/21** passing cells dual-verified
- **Real-silicon native harness:** **21/21** passing cells executed and passed on matching hardware
- **Total rounds / API spend:** 349 rounds, **$12.10** USD

## Cell-by-Cell Outcomes

Each row reports one cold-room cell: verdict, rounds used, API cost, compiled code size, `verify2.py` status, and real-silicon test result.

| Task | Model | Target | Arm | Verdict | Rounds | Initial -> Best `cyc/B` | Unroll (B/it) | Cost (USD) | `verify2.py` | Native CPU |
| --- | --- | --- | --- | --- | ---: | --- | ---: | ---: | --- | --- |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.04 | — | not_run |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.05 | — | not_run |
| `blake3_compress1` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.26 | — | not_run |
| `blake3_compress1` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.24 | — | not_run |
| `blake3_compress1` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.77 | — | not_run |
| `blake3_compress1` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R7, best R7) | 7 | 5.14 -> **5.14** | 64 B | $0.48 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.18 | — | not_run |
| `blake3_compress1` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.31 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.06 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.06 | — | not_run |
| `blake3_compress_4way` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R7, best R7) | 7 | 1.95 -> **1.95** | 256 B | $0.31 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.20 | — | not_run |
| `blake3_compress_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.66 | — | not_run |
| `blake3_compress_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $1.08 | — | not_run |
| `blake3_compress_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.43 | — | not_run |
| `blake3_compress_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.19 | — | not_run |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R1, best R1) | 1 | 2.41 -> **2.41** | 256 B | $0.01 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | PASS (R3, best R3) | 3 | 11.34 -> **11.34** | 256 B | $0.02 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R4, best R4) | 4 | 2.41 -> **2.41** | 256 B | $0.13 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.20 | — | not_run |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R2, best R2) | 2 | 2.48 -> **2.48** | 256 B | $0.16 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R6, best R6) | 6 | 5.89 -> **5.89** | 256 B | $0.25 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R1, best R1) | 1 | 2.50 -> **2.50** | 256 B | $0.03 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.18 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.03 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.03 | — | not_run |
| `ct_base64_decode` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R4, best R4) | 4 | 2.67 -> **2.67** | 4 B | $0.07 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.15 | — | not_run |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.15 | — | not_run |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (trace_refusal) | 7 | — | — | $0.15 | — | not_run |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.10 | — | not_run |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R4, best R4) | 4 | 2.75 -> **2.75** | 4 B | $0.11 | shown | NATIVE_PASS 333/333 |
| `der_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.04 | — | not_run |
| `der_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.04 | — | not_run |
| `der_valid` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.17 | — | not_run |
| `der_valid` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (arith_need_compare) | 7 | — | — | $0.15 | — | not_run |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R2, best R2) | 2 | — | — | $0.08 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.38 | — | not_run |
| `der_valid` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (spec_need_open) | 7 | — | — | $0.23 | — | not_run |
| `der_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R4, best R4) | 4 | — | — | $0.12 | shown | NATIVE_PASS 257/257 |
| `ebpf` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.04 | — | not_run |
| `ebpf` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.05 | — | not_run |
| `ebpf` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.16 | — | not_run |
| `ebpf` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (place_error) | 7 | — | — | $0.15 | — | not_run |
| `ebpf` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R4, best R4) | 4 | 0.05 -> **0.05** | 654 B | $0.16 | shown | NATIVE_PASS 7/7 |
| `ebpf` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.22 | — | not_run |
| `ebpf` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (arith_need_compare) | 7 | — | — | $0.15 | — | not_run |
| `ebpf` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.31 | — | not_run |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R2, best R2) | 2 | 1.00 -> **1.00** | 2 B | $0.01 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | PASS (R1, best R1) | 1 | 1.00 -> **1.00** | 2 B | $0.00 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R1, best R1) | 1 | 0.83 -> **0.83** | 2 B | $0.03 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `meta/muse-spark-open` | `x86_64` | `ode` | PASS (R3, best R3) | 3 | 1.00 -> **1.00** | 2 B | $0.06 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R4, best R4) | 4 | 0.42 -> **0.42** | 8 B | $0.13 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (spec_need_open) | 7 | — | — | $0.18 | — | not_run |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R7, best R7) | 7 | 0.92 -> **0.92** | 2 B | $0.12 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R3, best R3) | 3 | 1.00 -> **1.00** | 2 B | $0.03 | shown | NATIVE_PASS 607/607 |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.05 | — | not_run |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.04 | — | not_run |
| `sha256_4way` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.31 | — | not_run |
| `sha256_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.13 | — | not_run |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R3, best R3) | 3 | 1.02 -> **1.02** | 256 B | $0.49 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.61 | — | not_run |
| `sha256_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.18 | — | not_run |
| `sha256_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.18 | — | not_run |

## Failing Round Breakdown

Each row counts failing rounds across all cells by root-cause category.

| Failure category | Failing rounds |
| --- | --- |
| `compile_or_parse_error` | 122 |
| `other` | 112 |
| `arith_need_entail` | 48 |
| `output_token_limit` | 21 |
| `arith_need_compare` | 11 |
| `spec_need_open` | 6 |
| `trace_refusal` | 4 |
| `contract_id_mismatch` | 2 |
| `place_error` | 2 |

## Before vs. After Comparison (`hl-default-v4` -> `hl-default-v5`)

The first table compares totals over the 64 cells that both runs have (the same task, model, target, and arm); each cell was run once in each run, so a difference in one cell may be chance. The second table sets each such cell of the two runs side by side.

| Metric (over the 64 shared cells) | `hl-default-v4` | `hl-default-v5` | Delta |
| --- | --- | --- | --- |
| Strict passes | 21/64 | 21/64 | +0 |
| Total rounds | 340 | 349 | +9 |
| Total API spend (USD) | $13.22 | $12.10 | $-1.12 |
| Failing rounds: `arith_need_compare` | 15 | 11 | -4 |
| Failing rounds: `arith_need_entail` | 51 | 48 | -3 |
| Failing rounds: `compile_or_parse_error` | 119 | 122 | +3 |
| Failing rounds: `contract_id_mismatch` | 1 | 2 | +1 |
| Failing rounds: `isa_table_error` | 1 | 0 | -1 |
| Failing rounds: `other` | 103 | 112 | +9 |
| Failing rounds: `output_token_limit` | 18 | 21 | +3 |
| Failing rounds: `place_error` | 1 | 2 | +1 |
| Failing rounds: `spec_need_open` | 8 | 6 | -2 |
| Failing rounds: `trace_refusal` | 2 | 4 | +2 |

| Task | Model | Target | Arm | `hl-default-v4` | `hl-default-v5` |
| --- | --- | --- | --- | --- | --- |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.05) | FAIL ($0.04) |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.05) | FAIL ($0.05) |
| `blake3_compress1` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL ($0.26) | FAIL ($0.26) |
| `blake3_compress1` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.22) | FAIL ($0.24) |
| `blake3_compress1` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R5, $0.66) | FAIL ($0.77) |
| `blake3_compress1` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL ($0.71) | PASS (R7, $0.48) |
| `blake3_compress1` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.18) | FAIL ($0.18) |
| `blake3_compress1` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.18) | FAIL ($0.31) |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.06) | FAIL ($0.06) |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.06) | FAIL ($0.06) |
| `blake3_compress_4way` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R5, $0.20) | PASS (R7, $0.31) |
| `blake3_compress_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.28) | FAIL ($0.20) |
| `blake3_compress_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R1, $0.19) | FAIL ($0.66) |
| `blake3_compress_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL ($0.64) | FAIL ($1.08) |
| `blake3_compress_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.18) | FAIL ($0.43) |
| `blake3_compress_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.19) | FAIL ($0.19) |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R1, $0.01) | PASS (R1, $0.01) |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.04) | PASS (R3, $0.02) |
| `chacha20_4way` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R3, $0.08) | PASS (R4, $0.13) |
| `chacha20_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.26) | FAIL ($0.20) |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R1, $0.15) | PASS (R2, $0.16) |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R4, $0.32) | PASS (R6, $0.25) |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R1, $0.03) | PASS (R1, $0.03) |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.18) | FAIL ($0.18) |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.03) | FAIL ($0.03) |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | PASS (R4, $0.02) | FAIL ($0.03) |
| `ct_base64_decode` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R7, $0.12) | PASS (R4, $0.07) |
| `ct_base64_decode` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.11) | FAIL ($0.15) |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL ($0.33) | FAIL ($0.15) |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL ($0.24) | FAIL ($0.15) |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R7, $0.24) | FAIL ($0.10) |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.31) | PASS (R4, $0.11) |
| `der_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.04) | FAIL ($0.04) |
| `der_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.04) | FAIL ($0.04) |
| `der_valid` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R5, $0.11) | FAIL ($0.17) |
| `der_valid` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.16) | FAIL ($0.15) |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R3, $0.25) | PASS (R2, $0.08) |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL ($0.58) | FAIL ($0.38) |
| `der_valid` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.22) | FAIL ($0.23) |
| `der_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.24) | PASS (R4, $0.12) |
| `ebpf` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.04) | FAIL ($0.04) |
| `ebpf` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.04) | FAIL ($0.05) |
| `ebpf` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL ($0.14) | FAIL ($0.16) |
| `ebpf` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.19) | FAIL ($0.15) |
| `ebpf` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL ($0.35) | PASS (R4, $0.16) |
| `ebpf` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL ($0.30) | FAIL ($0.22) |
| `ebpf` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.21) | FAIL ($0.15) |
| `ebpf` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.27) | FAIL ($0.31) |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R3, $0.01) | PASS (R2, $0.01) |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | PASS (R2, $0.01) | PASS (R1, $0.00) |
| `ipv4_valid` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R1, $0.03) | PASS (R1, $0.03) |
| `ipv4_valid` | `meta/muse-spark-open` | `x86_64` | `ode` | PASS (R4, $0.07) | PASS (R3, $0.06) |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL ($0.30) | PASS (R4, $0.13) |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R4, $0.21) | FAIL ($0.18) |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R1, $0.04) | PASS (R7, $0.12) |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R2, $0.02) | PASS (R3, $0.03) |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.05) | FAIL ($0.05) |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.04) | FAIL ($0.04) |
| `sha256_4way` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL ($0.24) | FAIL ($0.31) |
| `sha256_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.14) | FAIL ($0.13) |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL ($1.31) | PASS (R3, $0.49) |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R5, $0.41) | FAIL ($0.61) |
| `sha256_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.18) | FAIL ($0.18) |
| `sha256_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.41) | FAIL ($0.18) |
