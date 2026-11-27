# Results: Pre-Registered Cold-Room Suite `hl-default-v1`

- **Pre-registration commit:** `ffa86871a73bb1882a7852199c956fcb7612c25d`
- **Finished (UTC):** `2026-11-27T05:31:19Z`
- **Strict pass rate:** **28/80** finished cells
- **Independent second verifier (`verify2.py`):** **13/28** passing cells dual-verified
- **Real-silicon native harness:** **28/28** passing cells executed and passed on matching hardware
- **Total rounds / API spend:** 538 rounds, **$35.76** USD

## Cell-by-Cell Outcomes

Each row reports one cold-room cell: verdict, rounds used, API cost, compiled code size, `verify2.py` status, and real-silicon test result.

| Task | Model | Target | Arm | Verdict | Rounds | Initial -> Best `cyc/B` | Unroll (B/it) | Cost (USD) | `verify2.py` | Native CPU |
| --- | --- | --- | --- | --- | ---: | --- | ---: | ---: | --- | --- |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (compile_or_parse_error) | 8 | — | — | $0.07 | — | not_run |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (other) | 8 | — | — | $0.09 | — | not_run |
| `blake3_compress1` | `google/gemini-4-neon` | `arm64` | `ode` | PASS (R1, best R3) | 3 | 5.47 -> **5.10** | 64 B | $0.94 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `google/gemini-4-neon` | `x86_64` | `ode` | PASS (R1, best R3) | 3 | 4.19 -> **4.16** | 64 B | $0.90 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (other) | 8 | — | — | $0.25 | — | not_run |
| `blake3_compress1` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (other) | 8 | — | — | $0.27 | — | not_run |
| `blake3_compress1` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (isa_table_error) | 8 | — | — | $0.47 | — | not_run |
| `blake3_compress1` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (other) | 8 | — | — | $0.45 | — | not_run |
| `blake3_compress1` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.36 | — | not_run |
| `blake3_compress1` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (other) | 8 | — | — | $0.51 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (other) | 8 | — | — | $0.08 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (other) | 8 | — | — | $0.07 | — | not_run |
| `blake3_compress_4way` | `google/gemini-4-neon` | `arm64` | `ode` | PASS (R5, best R5) | 7 | 3.47 -> **3.47** | 256 B | $2.48 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `google/gemini-4-neon` | `x86_64` | `ode` | PASS (R2, best R2) | 4 | 1.44 -> **1.44** | 256 B | $1.51 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (other) | 8 | — | — | $0.29 | — | not_run |
| `blake3_compress_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 8 | — | — | $0.45 | — | not_run |
| `blake3_compress_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (compile_or_parse_error) | 8 | — | — | $0.59 | — | not_run |
| `blake3_compress_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R5, best R5) | 7 | 1.66 -> **1.66** | 256 B | $0.77 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (output_token_limit) | 8 | — | — | $1.02 | — | not_run |
| `blake3_compress_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (output_token_limit) | 8 | — | — | $0.68 | — | not_run |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R3, best R3) | 5 | 2.41 -> **2.41** | 256 B | $0.03 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (other) | 8 | — | — | $0.04 | — | not_run |
| `chacha20_4way` | `google/gemini-4-neon` | `arm64` | `ode` | PASS (R1, best R2) | 3 | 2.41 -> **2.40** | 256 B | $0.64 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `google/gemini-4-neon` | `x86_64` | `ode` | PASS (R1, best R2) | 3 | 1.72 -> **1.70** | 256 B | $0.92 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R6, best R7) | 8 | 2.41 -> **2.41** | 256 B | $0.16 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (other) | 8 | — | — | $0.50 | — | not_run |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R1, best R2) | 3 | 2.41 -> **2.41** | 256 B | $0.15 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R6, best R6) | 8 | 5.89 -> **5.89** | 256 B | $0.40 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R1, best R1) | 3 | 2.52 -> **2.52** | 256 B | $0.23 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (output_token_limit) | 2 | — | — | $0.37 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (arith_need_entail) | 8 | — | — | $0.03 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (arith_need_entail) | 8 | — | — | $0.04 | — | not_run |
| `ct_base64_decode` | `google/gemini-4-neon` | `arm64` | `ode` | FAIL (other) | 8 | — | — | $1.61 | — | not_run |
| `ct_base64_decode` | `google/gemini-4-neon` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 8 | — | — | $1.05 | — | not_run |
| `ct_base64_decode` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (compile_or_parse_error) | 8 | — | — | $0.13 | — | not_run |
| `ct_base64_decode` | `meta/muse-spark-open` | `x86_64` | `ode` | PASS (R2, best R2) | 4 | 2.00 -> **2.00** | 4 B | $0.09 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (arith_need_entail) | 8 | — | — | $0.16 | — | not_run |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (other) | 8 | — | — | $0.20 | — | not_run |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (arith_need_entail) | 8 | — | — | $0.25 | — | not_run |
| `ct_base64_decode` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R2, best R2) | 4 | 2.75 -> **2.75** | 4 B | $0.12 | shown | NATIVE_PASS 333/333 |
| `der_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (arith_need_entail) | 8 | — | — | $0.04 | — | not_run |
| `der_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (other) | 8 | — | — | $0.06 | — | not_run |
| `der_valid` | `google/gemini-4-neon` | `arm64` | `ode` | PASS (R6, best R6) | 6 | — | — | $0.69 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `google/gemini-4-neon` | `x86_64` | `ode` | PASS (R7, best R7) | 7 | — | — | $1.14 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (trace_refusal) | 8 | — | — | $0.18 | — | not_run |
| `der_valid` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (other) | 8 | — | — | $0.16 | — | not_run |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | PASS (R7, best R7) | 7 | — | — | $0.33 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | PASS (R3, best R3) | 3 | — | — | $0.11 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R7, best R7) | 7 | — | — | $0.22 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (arith_need_entail) | 8 | — | — | $0.31 | — | not_run |
| `ebpf` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (arith_need_compare) | 8 | — | — | $0.04 | — | not_run |
| `ebpf` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (arith_need_compare) | 8 | — | — | $0.05 | — | not_run |
| `ebpf` | `google/gemini-4-neon` | `arm64` | `ode` | PASS (R2, best R2) | 4 | 0.05 -> **0.05** | 406 B | $0.61 | shown | NATIVE_PASS 7/7 |
| `ebpf` | `google/gemini-4-neon` | `x86_64` | `ode` | FAIL (other) | 8 | — | — | $1.26 | — | not_run |
| `ebpf` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (arith_need_entail) | 8 | — | — | $0.18 | — | not_run |
| `ebpf` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (arith_need_entail) | 8 | — | — | $0.16 | — | not_run |
| `ebpf` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (arith_need_entail) | 8 | — | — | $0.23 | — | not_run |
| `ebpf` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 8 | — | — | $0.24 | — | not_run |
| `ebpf` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (arith_need_compare) | 8 | — | — | $0.47 | — | not_run |
| `ebpf` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 8 | — | — | $0.43 | — | not_run |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | PASS (R2, best R2) | 4 | 1.00 -> **1.00** | 2 B | $0.01 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | PASS (R2, best R2) | 4 | 1.00 -> **1.00** | 2 B | $0.01 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `google/gemini-4-neon` | `arm64` | `ode` | FAIL (spec_need_open) | 8 | — | — | $1.33 | — | not_run |
| `ipv4_valid` | `google/gemini-4-neon` | `x86_64` | `ode` | FAIL (spec_need_open) | 8 | — | — | $1.22 | — | not_run |
| `ipv4_valid` | `meta/muse-spark-open` | `arm64` | `ode` | PASS (R4, best R4) | 4 | — | — | $0.07 | refused | NATIVE_PASS 607/607 |
| `ipv4_valid` | `meta/muse-spark-open` | `x86_64` | `ode` | PASS (R4, best R4) | 6 | 1.00 -> **1.00** | 2 B | $0.09 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (arith_need_compare) | 8 | — | — | $0.16 | — | not_run |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (arith_need_compare) | 8 | — | — | $0.17 | — | not_run |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | PASS (R7, best R7) | 8 | 0.44 -> **0.44** | 8 B | $0.21 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | PASS (R2, best R2) | 4 | 1.00 -> **1.00** | 2 B | $0.14 | shown | NATIVE_PASS 607/607 |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode` | FAIL (other) | 8 | — | — | $0.06 | — | not_run |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode` | FAIL (other) | 8 | — | — | $0.05 | — | not_run |
| `sha256_4way` | `google/gemini-4-neon` | `arm64` | `ode` | PASS (R2, best R4) | 4 | 1.02 -> **1.02** | 256 B | $1.34 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `google/gemini-4-neon` | `x86_64` | `ode` | PASS (R1, best R3) | 3 | 1.05 -> **1.03** | 256 B | $1.57 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `meta/muse-spark-open` | `arm64` | `ode` | FAIL (other) | 8 | — | — | $0.21 | — | not_run |
| `sha256_4way` | `meta/muse-spark-open` | `x86_64` | `ode` | FAIL (compile_or_parse_error) | 8 | — | — | $0.27 | — | not_run |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `ode` | FAIL (other) | 8 | — | — | $0.39 | — | not_run |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `ode` | FAIL (other) | 8 | — | — | $0.41 | — | not_run |
| `sha256_4way` | `z-ai/glm-5.3-prime` | `arm64` | `ode` | FAIL (other) | 8 | — | — | $0.96 | — | not_run |
| `sha256_4way` | `z-ai/glm-5.3-prime` | `x86_64` | `ode` | FAIL (output_token_limit) | 6 | — | — | $0.80 | — | not_run |

## Failing Round Breakdown

Each row counts failing rounds across all cells by root-cause category.

| Failure category | Failing rounds |
| --- | --- |
| `compile_or_parse_error` | 158 |
| `other` | 153 |
| `arith_need_entail` | 92 |
| `arith_need_compare` | 46 |
| `spec_need_open` | 18 |
| `output_token_limit` | 13 |
| `isa_table_error` | 5 |
| `trace_refusal` | 1 |
