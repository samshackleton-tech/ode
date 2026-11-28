# Results: Pre-Registered Cold-Room Suite `hl-default-v11`

- **Pre-registration commit:** `8391d6458a1c3a1e0d352e8132aad4b3d4264461`
- **Finished (UTC):** `2026-11-28T05:36:03Z`
- **Strict pass rate:** **27/64** finished cells
- **Independent second verifier (`verify2.py`):** **14/27** passing cells dual-verified
- **Real-silicon native harness:** **27/27** passing cells executed and passed on matching hardware
- **Total rounds / API spend:** 337 rounds, **$13.48** USD

## Cell-by-Cell Outcomes

Each row reports one cold-room cell: verdict, rounds used, API cost, compiled code size, `verify2.py` status, and real-silicon test result.

| Task | Model | Target | Arm | Verdict | Rounds | Initial -> Best `cyc/B` | Unroll (B/it) | Cost (USD) | `verify2.py` | Native CPU |
| --- | --- | --- | --- | --- | ---: | --- | ---: | ---: | --- | --- |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.05 | — | not_run |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.05 | — | not_run |
| `blake3_compress1` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R4, best R4) | 4 | 6.35 -> **6.35** | 64 B | $0.11 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.26 | — | not_run |
| `blake3_compress1` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.65 | — | not_run |
| `blake3_compress1` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.68 | — | not_run |
| `blake3_compress1` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.19 | — | not_run |
| `blake3_compress1` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.20 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R7, best R7) | 7 | 1.93 -> **1.93** | 256 B | $0.06 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.06 | — | not_run |
| `blake3_compress_4way` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R3, best R3) | 3 | 2.51 -> **2.51** | 256 B | $0.08 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.26 | — | not_run |
| `blake3_compress_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R2, best R2) | 2 | 1.94 -> **1.94** | 256 B | $0.25 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.91 | — | not_run |
| `blake3_compress_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.51 | — | not_run |
| `blake3_compress_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (output_token_limit) | 4 | — | — | $0.36 | — | not_run |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R1, best R1) | 1 | 7.58 -> **7.58** | 256 B | $0.00 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (output_token_limit) | 7 | — | — | $0.04 | — | not_run |
| `chacha20_4way` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R3, best R3) | 3 | 2.41 -> **2.41** | 256 B | $0.07 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.32 | — | not_run |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R1, best R1) | 1 | 2.41 -> **2.41** | 256 B | $0.12 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R3, best R3) | 3 | 5.89 -> **5.89** | 256 B | $0.29 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R2, best R2) | 2 | 7.58 -> **7.58** | 256 B | $0.07 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R4, best R4) | 4 | 4.51 -> **4.51** | 256 B | $0.30 | — | NATIVE_PASS 98/98 |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R3, best R3) | 3 | 2.33 -> **2.33** | 4 B | $0.01 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.03 | — | not_run |
| `ct_base64_decode` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.12 | — | not_run |
| `ct_base64_decode` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.11 | — | not_run |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R4, best R4) | 4 | 1.23 -> **1.23** | 8 B | $0.19 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.25 | — | not_run |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.16 | — | not_run |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R5, best R5) | 5 | 2.75 -> **2.75** | 4 B | $0.14 | shown | NATIVE_PASS 333/333 |
| `der_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R4, best R4) | 4 | — | — | $0.02 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.04 | — | not_run |
| `der_valid` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R7, best R7) | 7 | — | — | $0.14 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (trace_refusal) | 7 | — | — | $0.13 | — | not_run |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R2, best R2) | 2 | — | — | $0.18 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R4, best R4) | 4 | — | — | $0.25 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (output_token_limit) | 7 | — | — | $0.32 | — | not_run |
| `der_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.26 | — | not_run |
| `ebpf` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (arith_need_compare) | 7 | — | — | $0.04 | — | not_run |
| `ebpf` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.04 | — | not_run |
| `ebpf` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (arith_need_compare) | 7 | — | — | $0.15 | — | not_run |
| `ebpf` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (arith_need_compare) | 7 | — | — | $0.15 | — | not_run |
| `ebpf` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (spec_need_open) | 7 | — | — | $0.30 | — | not_run |
| `ebpf` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.33 | — | not_run |
| `ebpf` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.37 | — | not_run |
| `ebpf` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.28 | — | not_run |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R3, best R3) | 3 | 0.92 -> **0.92** | 2 B | $0.01 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | PASS (R2, best R2) | 2 | 1.00 -> **1.00** | 2 B | $0.01 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R1, best R1) | 1 | 0.83 -> **0.83** | 2 B | $0.03 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `meta/muse-spark-open` | `x86_64` | `ode` | PASS (R2, best R2) | 2 | 1.00 -> **1.00** | 2 B | $0.04 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R4, best R4) | 4 | 0.42 -> **0.42** | 8 B | $0.21 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.29 | — | not_run |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R4, best R4) | 4 | 0.40 -> **0.40** | 8 B | $0.07 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R2, best R2) | 2 | 1.00 -> **1.00** | 2 B | $0.04 | shown | NATIVE_PASS 607/607 |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R3, best R3) | 3 | 1.05 -> **1.05** | 256 B | $0.02 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.03 | — | not_run |
| `sha256_4way` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.16 | — | not_run |
| `sha256_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.15 | — | not_run |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.92 | — | not_run |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.88 | — | not_run |
| `sha256_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R6, best R6) | 6 | 4.51 -> **4.51** | 256 B | $0.37 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R5, best R5) | 5 | 4.32 -> **4.32** | 256 B | $0.27 | — | NATIVE_PASS 264/264 |

## Failing Round Breakdown

Each row counts failing rounds across all cells by root-cause category.

| Failure category | Failing rounds |
| --- | --- |
| `compile_or_parse_error` | 108 |
| `other` | 98 |
| `arith_need_entail` | 52 |
| `output_token_limit` | 22 |
| `arith_need_compare` | 19 |
| `spec_need_open` | 6 |
| `contract_id_mismatch` | 2 |
| `trace_refusal` | 2 |
| `place_error` | 1 |

## Before vs. After Comparison (`hl-default-v10` -> `hl-default-v11`)

The first table compares totals over the 64 cells that both runs have (the same task, model, target, and arm); each cell was run once in each run, so a difference in one cell may be chance. The second table sets each such cell of the two runs side by side.

| Metric (over the 64 shared cells) | `hl-default-v10` | `hl-default-v11` | Delta |
| --- | --- | --- | --- |
| Strict passes | 25/64 | 27/64 | +2 |
| Total rounds | 330 | 337 | +7 |
| Total API spend (USD) | $9.70 | $13.48 | $+3.78 |
| Failing rounds: `arith_need_compare` | 14 | 19 | +5 |
| Failing rounds: `arith_need_entail` | 56 | 52 | -4 |
| Failing rounds: `compile_or_parse_error` | 113 | 108 | -5 |
| Failing rounds: `contract_id_mismatch` | 2 | 2 | +0 |
| Failing rounds: `other` | 86 | 98 | +12 |
| Failing rounds: `output_token_limit` | 19 | 22 | +3 |
| Failing rounds: `place_error` | 5 | 1 | -4 |
| Failing rounds: `spec_need_open` | 7 | 6 | -1 |
| Failing rounds: `trace_refusal` | 3 | 2 | -1 |

| Task | Model | Target | Arm | `hl-default-v10` | `hl-default-v11` |
| --- | --- | --- | --- | --- | --- |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.05) | FAIL ($0.05) |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.06) | FAIL ($0.05) |
| `blake3_compress1` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL ($0.16) | PASS (R4, $0.11) |
| `blake3_compress1` | `meta/muse-spark-open` | `x86_64` | `ode` | PASS (R4, $0.16) | FAIL ($0.26) |
| `blake3_compress1` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R2, $0.23) | FAIL ($0.65) |
| `blake3_compress1` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL ($0.36) | FAIL ($0.68) |
| `blake3_compress1` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.19) | FAIL ($0.19) |
| `blake3_compress1` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.20) | FAIL ($0.20) |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R3, $0.03) | PASS (R7, $0.06) |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.06) | FAIL ($0.06) |
| `blake3_compress_4way` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R2, $0.08) | PASS (R3, $0.08) |
| `blake3_compress_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.34) | FAIL ($0.26) |
| `blake3_compress_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R2, $0.14) | PASS (R2, $0.25) |
| `blake3_compress_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL ($0.73) | FAIL ($0.91) |
| `blake3_compress_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R6, $0.43) | FAIL ($0.51) |
| `blake3_compress_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.20) | FAIL ($0.36) |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R1, $0.01) | PASS (R1, $0.00) |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.04) | FAIL ($0.04) |
| `chacha20_4way` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R2, $0.06) | PASS (R3, $0.07) |
| `chacha20_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.13) | FAIL ($0.32) |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R2, $0.09) | PASS (R1, $0.12) |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R4, $0.16) | PASS (R3, $0.29) |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R3, $0.17) | PASS (R2, $0.07) |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.29) | PASS (R4, $0.30) |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.03) | PASS (R3, $0.01) |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.03) | FAIL ($0.03) |
| `ct_base64_decode` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL ($0.10) | FAIL ($0.12) |
| `ct_base64_decode` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.13) | FAIL ($0.11) |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL ($0.18) | PASS (R4, $0.19) |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL ($0.27) | FAIL ($0.25) |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.16) | FAIL ($0.16) |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R4, $0.10) | PASS (R5, $0.14) |
| `der_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.04) | PASS (R4, $0.02) |
| `der_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.04) | FAIL ($0.04) |
| `der_valid` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL ($0.12) | PASS (R7, $0.14) |
| `der_valid` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.12) | FAIL ($0.13) |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R6, $0.19) | PASS (R2, $0.18) |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R7, $0.26) | PASS (R4, $0.25) |
| `der_valid` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R5, $0.14) | FAIL ($0.32) |
| `der_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.28) | FAIL ($0.26) |
| `ebpf` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.04) | FAIL ($0.04) |
| `ebpf` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.04) | FAIL ($0.04) |
| `ebpf` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL ($0.11) | FAIL ($0.15) |
| `ebpf` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.14) | FAIL ($0.15) |
| `ebpf` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL ($0.20) | FAIL ($0.30) |
| `ebpf` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL ($0.22) | FAIL ($0.33) |
| `ebpf` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.48) | FAIL ($0.37) |
| `ebpf` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.31) | FAIL ($0.28) |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R3, $0.01) | PASS (R3, $0.01) |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | PASS (R3, $0.01) | PASS (R2, $0.01) |
| `ipv4_valid` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R1, $0.03) | PASS (R1, $0.03) |
| `ipv4_valid` | `meta/muse-spark-open` | `x86_64` | `ode` | PASS (R4, $0.07) | PASS (R2, $0.04) |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL ($0.22) | PASS (R4, $0.21) |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R1, $0.06) | FAIL ($0.29) |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R3, $0.04) | PASS (R4, $0.07) |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R2, $0.04) | PASS (R2, $0.04) |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.04) | PASS (R3, $0.02) |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.04) | FAIL ($0.03) |
| `sha256_4way` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R6, $0.13) | FAIL ($0.16) |
| `sha256_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.23) | FAIL ($0.15) |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R1, $0.09) | FAIL ($0.92) |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R5, $0.20) | FAIL ($0.88) |
| `sha256_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.19) | PASS (R6, $0.37) |
| `sha256_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.20) | PASS (R5, $0.27) |
