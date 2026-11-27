# Results: Pre-Registered Cold-Room Suite `hl-default-v7`

- **Pre-registration commit:** `033aa7c9f9e40e6d6481d82ed7707f2b8faa1e63`
- **Finished (UTC):** `2026-11-27T22:34:15Z`
- **Strict pass rate:** **23/64** finished cells
- **Independent second verifier (`verify2.py`):** **14/23** passing cells dual-verified
- **Real-silicon native harness:** **23/23** passing cells executed and passed on matching hardware
- **Total rounds / API spend:** 353 rounds, **$13.71** USD

## Cell-by-Cell Outcomes

Each row reports one cold-room cell: verdict, rounds used, API cost, compiled code size, `verify2.py` status, and real-silicon test result.

| Task | Model | Target | Arm | Verdict | Rounds | Initial -> Best `cyc/B` | Unroll (B/it) | Cost (USD) | `verify2.py` | Native CPU |
| --- | --- | --- | --- | --- | ---: | --- | ---: | ---: | --- | --- |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R5, best R5) | 5 | 6.28 -> **6.28** | 64 B | $0.04 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.06 | — | not_run |
| `blake3_compress1` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.17 | — | not_run |
| `blake3_compress1` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.14 | — | not_run |
| `blake3_compress1` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.56 | — | not_run |
| `blake3_compress1` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.49 | — | not_run |
| `blake3_compress1` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.18 | — | not_run |
| `blake3_compress1` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (contract_id_mismatch) | 7 | — | — | $0.55 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.06 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.06 | — | not_run |
| `blake3_compress_4way` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R6, best R6) | 6 | 1.99 -> **1.99** | 256 B | $0.21 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.45 | — | not_run |
| `blake3_compress_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.89 | — | not_run |
| `blake3_compress_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.87 | — | not_run |
| `blake3_compress_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (output_token_limit) | 7 | — | — | $0.46 | — | not_run |
| `blake3_compress_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (output_token_limit) | 3 | — | — | $0.27 | — | not_run |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R1, best R1) | 1 | 2.41 -> **2.41** | 256 B | $0.01 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.04 | — | not_run |
| `chacha20_4way` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R4, best R4) | 4 | 2.41 -> **2.41** | 256 B | $0.09 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.25 | — | not_run |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R3, best R3) | 3 | 2.41 -> **2.41** | 256 B | $0.12 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R1, best R1) | 1 | 3.61 -> **3.61** | 256 B | $0.16 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R3, best R3) | 3 | 2.41 -> **2.41** | 256 B | $0.12 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.18 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.03 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | PASS (R4, best R4) | 4 | 3.00 -> **3.00** | 4 B | $0.02 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.10 | — | not_run |
| `ct_base64_decode` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.13 | — | not_run |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.74 | — | not_run |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R4, best R4) | 4 | 3.00 -> **3.00** | 4 B | $0.10 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R7, best R7) | 7 | 1.27 -> **1.27** | 8 B | $0.12 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R5, best R5) | 5 | 2.75 -> **2.75** | 4 B | $0.15 | shown | NATIVE_PASS 333/333 |
| `der_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.04 | — | not_run |
| `der_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.04 | — | not_run |
| `der_valid` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.14 | — | not_run |
| `der_valid` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.15 | — | not_run |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R3, best R3) | 3 | — | — | $0.22 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.45 | — | not_run |
| `der_valid` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R4, best R4) | 4 | — | — | $0.13 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (output_token_limit) | 7 | — | — | $0.24 | — | not_run |
| `ebpf` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.03 | — | not_run |
| `ebpf` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.04 | — | not_run |
| `ebpf` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (arith_need_compare) | 7 | — | — | $0.13 | — | not_run |
| `ebpf` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.15 | — | not_run |
| `ebpf` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.21 | — | not_run |
| `ebpf` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.42 | — | not_run |
| `ebpf` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (arith_need_entail) | 7 | — | — | $0.24 | — | not_run |
| `ebpf` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.30 | — | not_run |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R2, best R2) | 2 | 1.00 -> **1.00** | 2 B | $0.01 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | PASS (R3, best R3) | 3 | 1.00 -> **1.00** | 2 B | $0.01 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R1, best R1) | 1 | 0.83 -> **0.83** | 2 B | $0.06 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `meta/muse-spark-open` | `x86_64` | `ode` | PASS (R7, best R7) | 7 | 1.00 -> **1.00** | 2 B | $0.13 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R2, best R2) | 2 | 0.42 -> **0.42** | 8 B | $0.24 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R3, best R3) | 3 | 0.75 -> **0.75** | 4 B | $0.17 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R5, best R5) | 5 | 1.00 -> **1.00** | 2 B | $0.12 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R2, best R2) | 2 | 1.00 -> **1.00** | 2 B | $0.04 | shown | NATIVE_PASS 607/607 |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R3, best R3) | 3 | 1.05 -> **1.05** | 256 B | $0.03 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.05 | — | not_run |
| `sha256_4way` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.15 | — | not_run |
| `sha256_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 7 | — | — | $0.48 | — | not_run |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (other) | 7 | — | — | $0.45 | — | not_run |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R4, best R4) | 4 | — | — | $0.18 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (output_token_limit) | 5 | — | — | $0.42 | — | not_run |
| `sha256_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (other) | 7 | — | — | $0.46 | — | not_run |

## Failing Round Breakdown

Each row counts failing rounds across all cells by root-cause category.

| Failure category | Failing rounds |
| --- | --- |
| `compile_or_parse_error` | 134 |
| `other` | 99 |
| `arith_need_entail` | 52 |
| `output_token_limit` | 21 |
| `arith_need_compare` | 9 |
| `spec_need_open` | 7 |
| `contract_id_mismatch` | 6 |
| `trace_refusal` | 2 |
