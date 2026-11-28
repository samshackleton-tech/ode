# Results: Pre-Registered Cold-Room Suite `hl-default-v9`

- **Pre-registration commit:** `c061cfff43971a0d69d69daa2dd7da2093aff865`
- **Finished (UTC):** `2026-11-28T04:44:38Z`
- **Strict pass rate:** **25/64** finished cells
- **Independent second verifier (`verify2.py`):** **16/25** passing cells dual-verified
- **Real-silicon native harness:** **25/25** passing cells executed and passed on matching hardware
- **Total rounds / API spend:** 350 rounds, **$10.38** USD

## Cell-by-Cell Outcomes

Each row reports one cold-room cell: verdict, rounds used, API cost, compiled code size, `verify2.py` status, and real-silicon test result.

| Task | Model | Target | Arm | Verdict | Rounds | Initial -> Best `cyc/B` | Unroll (B/it) | Cost (USD) | `verify2.py` | Native CPU |
| --- | --- | --- | --- | --- | ---: | --- | ---: | ---: | --- | --- |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.05 | — | not_run |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.05 | — | not_run |
| `blake3_compress1` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R4, best R4) | 4 | 6.42 -> **6.42** | 64 B | $0.19 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.19 | — | not_run |
| `blake3_compress1` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.40 | — | not_run |
| `blake3_compress1` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.31 | — | not_run |
| `blake3_compress1` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.20 | — | not_run |
| `blake3_compress1` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.21 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R7, best R7) | 7 | 2.01 -> **2.01** | 256 B | $0.06 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.07 | — | not_run |
| `blake3_compress_4way` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R2, best R2) | 2 | 1.97 -> **1.97** | 256 B | $0.09 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.21 | — | not_run |
| `blake3_compress_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R7, best R7) | 7 | 1.93 -> **1.93** | 256 B | $0.34 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.55 | — | not_run |
| `blake3_compress_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.20 | — | not_run |
| `blake3_compress_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.21 | — | not_run |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R3, best R3) | 3 | 2.41 -> **2.41** | 256 B | $0.02 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.04 | — | not_run |
| `chacha20_4way` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R2, best R2) | 2 | 2.41 -> **2.41** | 256 B | $0.06 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.26 | — | not_run |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.31 | — | not_run |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R4, best R4) | 4 | 5.89 -> **5.89** | 256 B | $0.23 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (output_token_limit) | 6 | — | — | $0.49 | — | not_run |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.21 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R3, best R3) | 3 | 2.33 -> **2.33** | 4 B | $0.01 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.03 | — | not_run |
| `ct_base64_decode` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.11 | — | not_run |
| `ct_base64_decode` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.10 | — | not_run |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R6, best R6) | 6 | 2.33 -> **2.33** | 4 B | $0.12 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.20 | — | not_run |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R4, best R4) | 4 | 1.27 -> **1.27** | 8 B | $0.08 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R6, best R6) | 6 | 3.00 -> **3.00** | 4 B | $0.17 | shown | NATIVE_PASS 333/333 |
| `der_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R7, best R7) | 7 | — | — | $0.04 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.04 | — | not_run |
| `der_valid` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.13 | — | not_run |
| `der_valid` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.12 | — | not_run |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R3, best R3) | 3 | — | — | $0.11 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R5, best R5) | 5 | — | — | $0.17 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R5, best R5) | 5 | — | — | $0.24 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.24 | — | not_run |
| `ebpf` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (arith_need_compare) | 7 | — | — | $0.04 | — | not_run |
| `ebpf` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.04 | — | not_run |
| `ebpf` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (arith_need_compare) | 7 | — | — | $0.18 | — | not_run |
| `ebpf` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.15 | — | not_run |
| `ebpf` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R7, best R7) | 7 | 0.06 -> **0.06** | 351 B | $0.19 | shown | NATIVE_PASS 7/7 |
| `ebpf` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (arith_need_compare) | 7 | — | — | $0.19 | — | not_run |
| `ebpf` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (arith_need_compare) | 7 | — | — | $0.24 | — | not_run |
| `ebpf` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.34 | — | not_run |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R1, best R1) | 1 | 0.92 -> **0.92** | 2 B | $0.00 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | PASS (R2, best R2) | 2 | 1.00 -> **1.00** | 2 B | $0.01 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R1, best R1) | 1 | 0.83 -> **0.83** | 2 B | $0.03 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `meta/muse-spark-open` | `x86_64` | `ode` | PASS (R2, best R2) | 2 | 1.00 -> **1.00** | 2 B | $0.05 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.17 | — | not_run |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R7, best R7) | 7 | 1.25 -> **1.25** | 4 B | $0.19 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R5, best R5) | 5 | — | — | $0.09 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R6, best R6) | 6 | 1.50 -> **1.50** | 2 B | $0.12 | shown | NATIVE_PASS 607/607 |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R3, best R3) | 3 | 1.05 -> **1.05** | 256 B | $0.03 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.03 | — | not_run |
| `sha256_4way` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.17 | — | not_run |
| `sha256_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.16 | — | not_run |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.27 | — | not_run |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R6, best R6) | 6 | — | — | $0.27 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.20 | — | not_run |
| `sha256_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.35 | — | not_run |

## Failing Round Breakdown

Each row counts failing rounds across all cells by root-cause category.

| Failure category | Failing rounds |
| --- | --- |
| `compile_or_parse_error` | 124 |
| `other` | 90 |
| `arith_need_entail` | 53 |
| `output_token_limit` | 22 |
| `arith_need_compare` | 17 |
| `spec_need_open` | 11 |
| `contract_id_mismatch` | 6 |
| `place_error` | 2 |

## Before vs. After Comparison (`hl-default-v8` -> `hl-default-v9`)

The first table compares totals over the 64 cells that both runs have (the same task, model, target, and arm); each cell was run once in each run, so a difference in one cell may be chance. The second table sets each such cell of the two runs side by side.

| Metric (over the 64 shared cells) | `hl-default-v8` | `hl-default-v9` | Delta |
| --- | --- | --- | --- |
| Strict passes | 22/64 | 25/64 | +3 |
| Total rounds | 351 | 350 | -1 |
| Total API spend (USD) | $12.53 | $10.38 | $-2.15 |
| Failing rounds: `arith_need_compare` | 18 | 17 | -1 |
| Failing rounds: `arith_need_entail` | 59 | 53 | -6 |
| Failing rounds: `compile_or_parse_error` | 119 | 124 | +5 |
| Failing rounds: `contract_id_mismatch` | 5 | 6 | +1 |
| Failing rounds: `other` | 96 | 90 | -6 |
| Failing rounds: `output_token_limit` | 24 | 22 | -2 |
| Failing rounds: `place_error` | 2 | 2 | +0 |
| Failing rounds: `spec_need_open` | 5 | 11 | +6 |
| Failing rounds: `trace_refusal` | 1 | 0 | -1 |

| Task | Model | Target | Arm | `hl-default-v8` | `hl-default-v9` |
| --- | --- | --- | --- | --- | --- |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.04) | FAIL ($0.05) |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.05) | FAIL ($0.05) |
| `blake3_compress1` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL ($0.14) | PASS (R4, $0.19) |
| `blake3_compress1` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.24) | FAIL ($0.19) |
| `blake3_compress1` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R7, $0.43) | FAIL ($0.40) |
| `blake3_compress1` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL ($0.36) | FAIL ($0.31) |
| `blake3_compress1` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.18) | FAIL ($0.20) |
| `blake3_compress1` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.20) | FAIL ($0.21) |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R3, $0.02) | PASS (R7, $0.06) |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.05) | FAIL ($0.07) |
| `blake3_compress_4way` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R3, $0.12) | PASS (R2, $0.09) |
| `blake3_compress_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.18) | FAIL ($0.21) |
| `blake3_compress_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL ($0.47) | PASS (R7, $0.34) |
| `blake3_compress_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL ($0.68) | FAIL ($0.55) |
| `blake3_compress_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.35) | FAIL ($0.20) |
| `blake3_compress_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.19) | FAIL ($0.21) |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R1, $0.01) | PASS (R3, $0.02) |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.05) | FAIL ($0.04) |
| `chacha20_4way` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R4, $0.10) | PASS (R2, $0.06) |
| `chacha20_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.28) | FAIL ($0.26) |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R5, $0.22) | FAIL ($0.31) |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R3, $0.26) | PASS (R4, $0.23) |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R1, $0.05) | FAIL ($0.49) |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.20) | FAIL ($0.21) |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.03) | PASS (R3, $0.01) |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.03) | FAIL ($0.03) |
| `ct_base64_decode` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL ($0.14) | FAIL ($0.11) |
| `ct_base64_decode` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.11) | FAIL ($0.10) |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL ($0.96) | PASS (R6, $0.12) |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL ($0.34) | FAIL ($0.20) |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.20) | PASS (R4, $0.08) |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R6, $0.16) | PASS (R6, $0.17) |
| `der_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R5, $0.03) | PASS (R7, $0.04) |
| `der_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.04) | FAIL ($0.04) |
| `der_valid` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R5, $0.09) | FAIL ($0.13) |
| `der_valid` | `meta/muse-spark-open` | `x86_64` | `ode` | PASS (R4, $0.09) | FAIL ($0.12) |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R7, $0.49) | PASS (R3, $0.11) |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R5, $0.37) | PASS (R5, $0.17) |
| `der_valid` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.27) | PASS (R5, $0.24) |
| `der_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.35) | FAIL ($0.24) |
| `ebpf` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.04) | FAIL ($0.04) |
| `ebpf` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.04) | FAIL ($0.04) |
| `ebpf` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL ($0.14) | FAIL ($0.18) |
| `ebpf` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.15) | FAIL ($0.15) |
| `ebpf` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL ($0.19) | PASS (R7, $0.19) |
| `ebpf` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL ($0.21) | FAIL ($0.19) |
| `ebpf` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.51) | FAIL ($0.24) |
| `ebpf` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.27) | FAIL ($0.34) |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.02) | PASS (R1, $0.00) |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | PASS (R2, $0.01) | PASS (R2, $0.01) |
| `ipv4_valid` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R2, $0.03) | PASS (R1, $0.03) |
| `ipv4_valid` | `meta/muse-spark-open` | `x86_64` | `ode` | PASS (R3, $0.05) | PASS (R2, $0.05) |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R5, $0.25) | FAIL ($0.17) |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R4, $0.23) | PASS (R7, $0.19) |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R6, $0.17) | PASS (R5, $0.09) |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R2, $0.02) | PASS (R6, $0.12) |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL ($0.05) | PASS (R3, $0.03) |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL ($0.05) | FAIL ($0.03) |
| `sha256_4way` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL ($0.13) | FAIL ($0.17) |
| `sha256_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL ($0.14) | FAIL ($0.16) |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R4, $0.51) | FAIL ($0.27) |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL ($0.40) | PASS (R6, $0.27) |
| `sha256_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL ($0.18) | FAIL ($0.20) |
| `sha256_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL ($0.18) | FAIL ($0.35) |
