# Results: Pre-Registered Cold-Room Suite `hl-default-v6`

- **Pre-registration commit:** `8023bccb702cb5ecdd364912c44253f6be1e88a7`
- **Finished (UTC):** `2026-11-27T21:12:54Z`
- **Strict pass rate:** **22/64** finished cells
- **Independent second verifier (`verify2.py`):** **12/22** passing cells dual-verified
- **Real-silicon native harness:** **21/22** passing cells executed and passed on matching hardware
- **Total rounds / API spend:** 352 rounds, **$12.16** USD

## Cell-by-Cell Outcomes

Each row reports one cold-room cell: verdict, rounds used, API cost, compiled code size, `verify2.py` status, and real-silicon test result.

| Task | Model | Target | Arm | Verdict | Rounds | Initial -> Best `cyc/B` | Unroll (B/it) | Cost (USD) | `verify2.py` | Native CPU |
| --- | --- | --- | --- | --- | ---: | --- | ---: | ---: | --- | --- |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R4, best R4) | 4 | 6.25 -> **6.25** | 64 B | $0.03 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.04 | — | not_run |
| `blake3_compress1` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.15 | — | not_run |
| `blake3_compress1` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.18 | — | not_run |
| `blake3_compress1` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.43 | — | not_run |
| `blake3_compress1` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.57 | — | not_run |
| `blake3_compress1` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.18 | — | not_run |
| `blake3_compress1` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.18 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.05 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.05 | — | not_run |
| `blake3_compress_4way` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R7, best R7) | 7 | 1.96 -> **1.96** | 256 B | $0.32 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.39 | — | not_run |
| `blake3_compress_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R7, best R7) | 7 | 1.94 -> **1.94** | 256 B | $0.53 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.72 | — | not_run |
| `blake3_compress_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.58 | — | not_run |
| `blake3_compress_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (output_token_limit) | 4 | — | — | $0.34 | — | not_run |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R2, best R2) | 2 | 2.43 -> **2.43** | 256 B | $0.01 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.05 | — | not_run |
| `chacha20_4way` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.20 | — | not_run |
| `chacha20_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.23 | — | not_run |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R4, best R4) | 4 | 2.41 -> **2.41** | 256 B | $0.19 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R4, best R4) | 4 | 1.99 -> **1.99** | 256 B | $0.44 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R3, best R3) | 3 | 2.52 -> **2.52** | 256 B | $0.14 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.18 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.03 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.03 | — | not_run |
| `ct_base64_decode` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.14 | — | not_run |
| `ct_base64_decode` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.14 | — | not_run |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.14 | — | not_run |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.43 | — | not_run |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.20 | — | not_run |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.21 | — | not_run |
| `der_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R2, best R2) | 2 | — | — | $0.01 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.04 | — | not_run |
| `der_valid` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R6, best R6) | 6 | — | — | $0.14 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.16 | — | not_run |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R1, best R1) | 1 | — | — | $0.06 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.19 | — | not_run |
| `der_valid` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R6, best R6) | 6 | — | — | $0.20 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R7, best R7) | 7 | — | — | $0.24 | shown | NATIVE_PASS 257/257 |
| `ebpf` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.04 | — | not_run |
| `ebpf` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (arith_need_compare) | 7 | — | — | $0.05 | — | not_run |
| `ebpf` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (arith_need_compare) | 7 | — | — | $0.17 | — | not_run |
| `ebpf` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.15 | — | not_run |
| `ebpf` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.32 | — | not_run |
| `ebpf` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.34 | — | not_run |
| `ebpf` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.22 | — | not_run |
| `ebpf` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.33 | — | not_run |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R2, best R2) | 2 | 0.92 -> **0.92** | 2 B | $0.01 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | PASS (R2, best R2) | 2 | 1.00 -> **1.00** | 2 B | $0.01 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R7, best R7) | 7 | 0.83 -> **0.83** | 2 B | $0.18 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `meta/muse-spark-open` | `x86_64` | `ode` | PASS (R3, best R3) | 3 | 1.00 -> **1.00** | 2 B | $0.05 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (spec_need_open) | 7 | — | — | $0.18 | — | not_run |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R2, best R2) | 2 | 0.75 -> **0.75** | 4 B | $0.09 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R1, best R1) | 1 | 1.17 -> **1.17** | 2 B | $0.04 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R2, best R2) | 2 | 1.00 -> **1.00** | 2 B | $0.03 | shown | NATIVE_PASS 607/607 |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R2, best R2) | 2 | 1.05 -> **1.05** | 256 B | $0.02 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.04 | — | not_run |
| `sha256_4way` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.45 | — | not_run |
| `sha256_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.18 | — | not_run |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R1, best R1) | 1 | — | — | $0.09 | — | fail |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R1, best R1) | 1 | 4.81 -> **4.81** | 256 B | $0.08 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.24 | — | not_run |
| `sha256_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.32 | — | not_run |

## Failing Round Breakdown

Each row counts failing rounds across all cells by root-cause category.

| Failure category | Failing rounds |
| --- | --- |
| `compile_or_parse_error` | 139 |
| `other` | 100 |
| `arith_need_entail` | 47 |
| `output_token_limit` | 16 |
| `arith_need_compare` | 11 |
| `spec_need_open` | 10 |
| `contract_id_mismatch` | 3 |
| `place_error` | 3 |
| `trace_refusal` | 1 |

## Before vs. After Comparison (`hl-default-v5` -> `hl-default-v6`)

The first table compares totals over the 64 cells that both runs have (the same task, model, target, and arm); each cell was run once in each run, so a difference in one cell may be chance. The second table sets each such cell of the two runs side by side.

| Metric (over the 64 shared cells) | `hl-default-v5` | `hl-default-v6` | Delta |
| --- | --- | --- | --- |
| Strict passes | 21/64 | 22/64 | +1 |
| Total rounds | 349 | 352 | +3 |
| Total API spend (USD) | $12.10 | $12.16 | $+0.06 |
| Failing rounds: `arith_need_compare` | 11 | 11 | +0 |
| Failing rounds: `arith_need_entail` | 48 | 47 | -1 |
| Failing rounds: `compile_or_parse_error` | 122 | 139 | +17 |
| Failing rounds: `contract_id_mismatch` | 2 | 3 | +1 |
| Failing rounds: `other` | 112 | 100 | -12 |
| Failing rounds: `output_token_limit` | 21 | 16 | -5 |
| Failing rounds: `place_error` | 2 | 3 | +1 |
| Failing rounds: `spec_need_open` | 6 | 10 | +4 |
| Failing rounds: `trace_refusal` | 4 | 1 | -3 |

| Task | Model | Target | Arm | `hl-default-v5` | `hl-default-v6` |
| --- | --- | --- | --- | --- | --- |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.04) | PASS (R4, $0.03) |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.05) | FAIL ($0.04) |
| `blake3_compress1` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL ($0.26) | FAIL ($0.15) |
| `blake3_compress1` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.24) | FAIL ($0.18) |
| `blake3_compress1` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL ($0.77) | FAIL ($0.43) |
| `blake3_compress1` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R7, $0.48) | FAIL ($0.57) |
| `blake3_compress1` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.18) | FAIL ($0.18) |
| `blake3_compress1` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.31) | FAIL ($0.18) |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.06) | FAIL ($0.05) |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.06) | FAIL ($0.05) |
| `blake3_compress_4way` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R7, $0.31) | PASS (R7, $0.32) |
| `blake3_compress_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.20) | FAIL ($0.39) |
| `blake3_compress_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL ($0.66) | PASS (R7, $0.53) |
| `blake3_compress_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL ($1.08) | FAIL ($0.72) |
| `blake3_compress_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.43) | FAIL ($0.58) |
| `blake3_compress_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.19) | FAIL ($0.34) |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R1, $0.01) | PASS (R2, $0.01) |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | PASS (R3, $0.02) | FAIL ($0.05) |
| `chacha20_4way` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R4, $0.13) | FAIL ($0.20) |
| `chacha20_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.20) | FAIL ($0.23) |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R2, $0.16) | PASS (R4, $0.19) |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R6, $0.25) | PASS (R4, $0.44) |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R1, $0.03) | PASS (R3, $0.14) |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.18) | FAIL ($0.18) |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.03) | FAIL ($0.03) |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.03) | FAIL ($0.03) |
| `ct_base64_decode` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R4, $0.07) | FAIL ($0.14) |
| `ct_base64_decode` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.15) | FAIL ($0.14) |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL ($0.15) | FAIL ($0.14) |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL ($0.15) | FAIL ($0.43) |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.10) | FAIL ($0.20) |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R4, $0.11) | FAIL ($0.21) |
| `der_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.04) | PASS (R2, $0.01) |
| `der_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.04) | FAIL ($0.04) |
| `der_valid` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL ($0.17) | PASS (R6, $0.14) |
| `der_valid` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.15) | FAIL ($0.16) |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R2, $0.08) | PASS (R1, $0.06) |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL ($0.38) | FAIL ($0.19) |
| `der_valid` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.23) | PASS (R6, $0.20) |
| `der_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R4, $0.12) | PASS (R7, $0.24) |
| `ebpf` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.04) | FAIL ($0.04) |
| `ebpf` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.05) | FAIL ($0.05) |
| `ebpf` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL ($0.16) | FAIL ($0.17) |
| `ebpf` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.15) | FAIL ($0.15) |
| `ebpf` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R4, $0.16) | FAIL ($0.32) |
| `ebpf` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL ($0.22) | FAIL ($0.34) |
| `ebpf` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.15) | FAIL ($0.22) |
| `ebpf` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.31) | FAIL ($0.33) |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R2, $0.01) | PASS (R2, $0.01) |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | PASS (R1, $0.00) | PASS (R2, $0.01) |
| `ipv4_valid` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R1, $0.03) | PASS (R7, $0.18) |
| `ipv4_valid` | `meta/muse-spark-open` | `x86_64` | `ode` | PASS (R3, $0.06) | PASS (R3, $0.05) |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R4, $0.13) | FAIL ($0.18) |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL ($0.18) | PASS (R2, $0.09) |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R7, $0.12) | PASS (R1, $0.04) |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R3, $0.03) | PASS (R2, $0.03) |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.05) | PASS (R2, $0.02) |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.04) | FAIL ($0.04) |
| `sha256_4way` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL ($0.31) | FAIL ($0.45) |
| `sha256_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.13) | FAIL ($0.18) |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R3, $0.49) | PASS (R1, $0.09) |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL ($0.61) | PASS (R1, $0.08) |
| `sha256_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.18) | FAIL ($0.24) |
| `sha256_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.18) | FAIL ($0.32) |
