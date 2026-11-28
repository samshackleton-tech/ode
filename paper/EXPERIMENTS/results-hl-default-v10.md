# Results: Pre-Registered Cold-Room Suite `hl-default-v10`

- **Pre-registration commit:** `6a40713b2fcf40b972f1a55c7db36847fd2cc51b`
- **Finished (UTC):** `2026-11-28T05:12:18Z`
- **Strict pass rate:** **25/64** finished cells
- **Independent second verifier (`verify2.py`):** **11/25** passing cells dual-verified
- **Real-silicon native harness:** **25/25** passing cells executed and passed on matching hardware
- **Total rounds / API spend:** 330 rounds, **$9.70** USD

## Cell-by-Cell Outcomes

Each row reports one cold-room cell: verdict, rounds used, API cost, compiled code size, `verify2.py` status, and real-silicon test result.

| Task | Model | Target | Arm | Verdict | Rounds | Initial -> Best `cyc/B` | Unroll (B/it) | Cost (USD) | `verify2.py` | Native CPU |
| --- | --- | --- | --- | --- | ---: | --- | ---: | ---: | --- | --- |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.05 | — | not_run |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.06 | — | not_run |
| `blake3_compress1` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.16 | — | not_run |
| `blake3_compress1` | `meta/muse-spark-open` | `x86_64` | `ode` | PASS (R4, best R4) | 4 | 5.01 -> **5.01** | 64 B | $0.16 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R2, best R2) | 2 | 6.11 -> **6.11** | 64 B | $0.23 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.36 | — | not_run |
| `blake3_compress1` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.19 | — | not_run |
| `blake3_compress1` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.20 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R3, best R3) | 3 | 1.93 -> **1.93** | 256 B | $0.03 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.06 | — | not_run |
| `blake3_compress_4way` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R2, best R2) | 2 | 2.00 -> **2.00** | 256 B | $0.08 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.34 | — | not_run |
| `blake3_compress_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R2, best R2) | 2 | 1.93 -> **1.93** | 256 B | $0.14 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.73 | — | not_run |
| `blake3_compress_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R6, best R6) | 6 | 1.94 -> **1.94** | 256 B | $0.43 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.20 | — | not_run |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R1, best R1) | 1 | 2.41 -> **2.41** | 256 B | $0.01 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.04 | — | not_run |
| `chacha20_4way` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R2, best R2) | 2 | 2.42 -> **2.42** | 256 B | $0.06 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.13 | — | not_run |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R2, best R2) | 2 | 2.41 -> **2.41** | 256 B | $0.09 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R4, best R4) | 4 | 3.52 -> **3.52** | 256 B | $0.16 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R3, best R3) | 3 | 2.52 -> **2.52** | 256 B | $0.17 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.29 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.03 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.03 | — | not_run |
| `ct_base64_decode` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.10 | — | not_run |
| `ct_base64_decode` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.13 | — | not_run |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.18 | — | not_run |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (trace_refusal) | 7 | — | — | $0.27 | — | not_run |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.16 | — | not_run |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R4, best R4) | 4 | 3.00 -> **3.00** | 4 B | $0.10 | shown | NATIVE_PASS 333/333 |
| `der_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.04 | — | not_run |
| `der_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (place_error) | 7 | — | — | $0.04 | — | not_run |
| `der_valid` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.12 | — | not_run |
| `der_valid` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (place_error) | 7 | — | — | $0.12 | — | not_run |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R6, best R6) | 6 | — | — | $0.19 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R7, best R7) | 7 | — | — | $0.26 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R5, best R5) | 5 | — | — | $0.14 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.28 | — | not_run |
| `ebpf` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.04 | — | not_run |
| `ebpf` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.04 | — | not_run |
| `ebpf` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (arith_need_compare) | 7 | — | — | $0.11 | — | not_run |
| `ebpf` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (arith_need_compare) | 7 | — | — | $0.14 | — | not_run |
| `ebpf` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.20 | — | not_run |
| `ebpf` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.22 | — | not_run |
| `ebpf` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (output_token_limit) | 7 | — | — | $0.48 | — | not_run |
| `ebpf` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.31 | — | not_run |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R3, best R3) | 3 | 0.92 -> **0.92** | 2 B | $0.01 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | PASS (R3, best R3) | 3 | 1.00 -> **1.00** | 2 B | $0.01 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R1, best R1) | 1 | 0.83 -> **0.83** | 2 B | $0.03 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `meta/muse-spark-open` | `x86_64` | `ode` | PASS (R4, best R4) | 4 | 1.00 -> **1.00** | 2 B | $0.07 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.22 | — | not_run |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R1, best R1) | 1 | 1.00 -> **1.00** | 2 B | $0.06 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R3, best R3) | 3 | 1.00 -> **1.00** | 2 B | $0.04 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R2, best R2) | 2 | 1.00 -> **1.00** | 2 B | $0.04 | shown | NATIVE_PASS 607/607 |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.04 | — | not_run |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.04 | — | not_run |
| `sha256_4way` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R6, best R6) | 6 | 4.24 -> **4.24** | 256 B | $0.13 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.23 | — | not_run |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R1, best R1) | 1 | — | — | $0.09 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R5, best R5) | 5 | — | — | $0.20 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.19 | — | not_run |
| `sha256_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.20 | — | not_run |

## Failing Round Breakdown

Each row counts failing rounds across all cells by root-cause category.

| Failure category | Failing rounds |
| --- | --- |
| `compile_or_parse_error` | 113 |
| `other` | 86 |
| `arith_need_entail` | 56 |
| `output_token_limit` | 19 |
| `arith_need_compare` | 14 |
| `spec_need_open` | 7 |
| `place_error` | 5 |
| `trace_refusal` | 3 |
| `contract_id_mismatch` | 2 |

## Before vs. After Comparison (`hl-default-v9` -> `hl-default-v10`)

The first table compares totals over the 64 cells that both runs have (the same task, model, target, and arm); each cell was run once in each run, so a difference in one cell may be chance. The second table sets each such cell of the two runs side by side.

| Metric (over the 64 shared cells) | `hl-default-v9` | `hl-default-v10` | Delta |
| --- | --- | --- | --- |
| Strict passes | 25/64 | 25/64 | +0 |
| Total rounds | 350 | 330 | -20 |
| Total API spend (USD) | $10.38 | $9.70 | $-0.68 |
| Failing rounds: `arith_need_compare` | 17 | 14 | -3 |
| Failing rounds: `arith_need_entail` | 53 | 56 | +3 |
| Failing rounds: `compile_or_parse_error` | 124 | 113 | -11 |
| Failing rounds: `contract_id_mismatch` | 6 | 2 | -4 |
| Failing rounds: `other` | 90 | 86 | -4 |
| Failing rounds: `output_token_limit` | 22 | 19 | -3 |
| Failing rounds: `place_error` | 2 | 5 | +3 |
| Failing rounds: `spec_need_open` | 11 | 7 | -4 |
| Failing rounds: `trace_refusal` | 0 | 3 | +3 |

| Task | Model | Target | Arm | `hl-default-v9` | `hl-default-v10` |
| --- | --- | --- | --- | --- | --- |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.05) | FAIL ($0.05) |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.05) | FAIL ($0.06) |
| `blake3_compress1` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R4, $0.19) | FAIL ($0.16) |
| `blake3_compress1` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.19) | PASS (R4, $0.16) |
| `blake3_compress1` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL ($0.40) | PASS (R2, $0.23) |
| `blake3_compress1` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL ($0.31) | FAIL ($0.36) |
| `blake3_compress1` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.20) | FAIL ($0.19) |
| `blake3_compress1` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.21) | FAIL ($0.20) |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R7, $0.06) | PASS (R3, $0.03) |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.07) | FAIL ($0.06) |
| `blake3_compress_4way` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R2, $0.09) | PASS (R2, $0.08) |
| `blake3_compress_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.21) | FAIL ($0.34) |
| `blake3_compress_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R7, $0.34) | PASS (R2, $0.14) |
| `blake3_compress_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL ($0.55) | FAIL ($0.73) |
| `blake3_compress_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.20) | PASS (R6, $0.43) |
| `blake3_compress_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.21) | FAIL ($0.20) |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R3, $0.02) | PASS (R1, $0.01) |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.04) | FAIL ($0.04) |
| `chacha20_4way` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R2, $0.06) | PASS (R2, $0.06) |
| `chacha20_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.26) | FAIL ($0.13) |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL ($0.31) | PASS (R2, $0.09) |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R4, $0.23) | PASS (R4, $0.16) |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.49) | PASS (R3, $0.17) |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.21) | FAIL ($0.29) |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R3, $0.01) | FAIL ($0.03) |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.03) | FAIL ($0.03) |
| `ct_base64_decode` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL ($0.11) | FAIL ($0.10) |
| `ct_base64_decode` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.10) | FAIL ($0.13) |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R6, $0.12) | FAIL ($0.18) |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL ($0.20) | FAIL ($0.27) |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R4, $0.08) | FAIL ($0.16) |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R6, $0.17) | PASS (R4, $0.10) |
| `der_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R7, $0.04) | FAIL ($0.04) |
| `der_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.04) | FAIL ($0.04) |
| `der_valid` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL ($0.13) | FAIL ($0.12) |
| `der_valid` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.12) | FAIL ($0.12) |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R3, $0.11) | PASS (R6, $0.19) |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R5, $0.17) | PASS (R7, $0.26) |
| `der_valid` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R5, $0.24) | PASS (R5, $0.14) |
| `der_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.24) | FAIL ($0.28) |
| `ebpf` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.04) | FAIL ($0.04) |
| `ebpf` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.04) | FAIL ($0.04) |
| `ebpf` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL ($0.18) | FAIL ($0.11) |
| `ebpf` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.15) | FAIL ($0.14) |
| `ebpf` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R7, $0.19) | FAIL ($0.20) |
| `ebpf` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL ($0.19) | FAIL ($0.22) |
| `ebpf` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.24) | FAIL ($0.48) |
| `ebpf` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.34) | FAIL ($0.31) |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R1, $0.00) | PASS (R3, $0.01) |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | PASS (R2, $0.01) | PASS (R3, $0.01) |
| `ipv4_valid` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R1, $0.03) | PASS (R1, $0.03) |
| `ipv4_valid` | `meta/muse-spark-open` | `x86_64` | `ode` | PASS (R2, $0.05) | PASS (R4, $0.07) |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL ($0.17) | FAIL ($0.22) |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R7, $0.19) | PASS (R1, $0.06) |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R5, $0.09) | PASS (R3, $0.04) |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R6, $0.12) | PASS (R2, $0.04) |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R3, $0.03) | FAIL ($0.04) |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.03) | FAIL ($0.04) |
| `sha256_4way` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL ($0.17) | PASS (R6, $0.13) |
| `sha256_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.16) | FAIL ($0.23) |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL ($0.27) | PASS (R1, $0.09) |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R6, $0.27) | PASS (R5, $0.20) |
| `sha256_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.20) | FAIL ($0.19) |
| `sha256_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.35) | FAIL ($0.20) |
