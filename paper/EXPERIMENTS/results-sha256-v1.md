# Results: Pre-Registered Cold-Room Suite `sha256-v1`

- **Pre-registration commit:** `1c722390051318a5a14f22887dd23d81e7604d7e`
- **Finished (UTC):** `2026-11-26T09:41:14Z`
- **Strict pass rate:** **21/28** finished cells
- **Independent second verifier (`verify2.py`):** **0/21** passing cells dual-verified
- **Real-silicon native harness:** **21/21** passing cells executed and passed on matching hardware
- **Total rounds / API spend:** 186 rounds, **$55.55** USD

## Cell-by-Cell Outcomes

Each row reports one cold-room cell: verdict, rounds used, API cost, compiled code size, `verify2.py` status, and real-silicon test result.

| Task | Model | Target | Arm | Verdict | Rounds | Initial -> Best `cyc/B` | Unroll (B/it) | Cost (USD) | `verify2.py` | Native CPU |
| --- | --- | --- | --- | --- | ---: | --- | ---: | ---: | --- | --- |
| `sha256_4way` | `anthropic/claude-fable-5.2` | `arm64` | `advised` | PASS (R3, best R4) | 7 | 1.02 -> **1.01** | 256 B | $6.04 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `anthropic/claude-fable-5.2` | `arm64` | `blind` | PASS (R3, best R3) | 7 | 1.02 -> **1.02** | 256 B | $6.15 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `anthropic/claude-fable-5.2` | `x86_64` | `advised` | PASS (R1, best R1) | 5 | 0.98 -> **0.98** | 256 B | $5.97 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `anthropic/claude-fable-5.2` | `x86_64` | `blind` | PASS (R1, best R2) | 4 | 0.98 -> **0.91** | 256 B | $5.29 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `advised` | PASS (R5, best R5) | 8 | 1.05 -> **1.05** | 256 B | $0.07 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `blind` | PASS (R1, best R1) | 5 | 1.02 -> **1.02** | 256 B | $0.06 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `advised` | FAIL (compile_or_parse_error) | 7 | — | — | $0.15 | — | not_run |
| `sha256_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `blind` | FAIL (compile_or_parse_error) | 8 | — | — | $0.26 | — | not_run |
| `sha256_4way` | `anthropic/claude-sonnet-5.5` | `arm64` | `advised` | PASS (R1, best R3) | 6 | 1.05 -> **1.02** | 256 B | $1.05 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `anthropic/claude-sonnet-5.5` | `arm64` | `blind` | PASS (R1, best R2) | 6 | 1.05 -> **1.02** | 256 B | $1.10 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `anthropic/claude-sonnet-5.5` | `x86_64` | `advised` | PASS (R1, best R2) | 5 | 1.16 -> **0.98** | 256 B | $1.24 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `anthropic/claude-sonnet-5.5` | `x86_64` | `blind` | PASS (R2, best R3) | 6 | 1.17 -> **0.99** | 256 B | $1.35 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `google/gemini-4-neon` | `arm64` | `advised` | PASS (R3, best R5) | 5 | 1.02 -> **1.01** | 256 B | $1.54 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `google/gemini-4-neon` | `arm64` | `blind` | PASS (R3, best R7) | 7 | 1.02 -> **1.02** | 256 B | $1.93 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `google/gemini-4-neon` | `x86_64` | `advised` | PASS (R3, best R5) | 5 | 1.04 -> **0.91** | 256 B | $1.58 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `google/gemini-4-neon` | `x86_64` | `blind` | PASS (R2, best R3) | 4 | 0.98 -> **0.98** | 256 B | $1.69 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `advised` | PASS (R5, best R8) | 8 | 1.02 -> **1.02** | 256 B | $0.76 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `blind` | FAIL (calling_syntax_error) | 8 | — | — | $0.76 | — | not_run |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `advised` | FAIL (other) | 8 | — | — | $0.79 | — | not_run |
| `sha256_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `blind` | PASS (R3, best R6) | 8 | 1.16 -> **0.98** | 256 B | $1.21 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `openai/gpt-6.2-astra-pro` | `arm64` | `advised` | PASS (R3, best R5) | 7 | 1.02 -> **1.02** | 256 B | $2.68 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `openai/gpt-6.2-astra-pro` | `arm64` | `blind` | PASS (R3, best R3) | 8 | 1.02 -> **1.02** | 256 B | $4.50 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `openai/gpt-6.2-astra-pro` | `x86_64` | `advised` | PASS (R2, best R4) | 8 | 1.04 -> **0.91** | 256 B | $3.41 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `openai/gpt-6.2-astra-pro` | `x86_64` | `blind` | PASS (R2, best R4) | 6 | 1.04 -> **0.91** | 256 B | $2.84 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `advised` | FAIL (compile_or_parse_error) | 8 | — | — | $0.64 | — | not_run |
| `sha256_4way` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `blind` | PASS (R4, best R5) | 8 | 1.05 -> **1.02** | 256 B | $1.06 | — | NATIVE_PASS 264/264 |
| `sha256_4way` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `advised` | FAIL (other) | 8 | — | — | $0.57 | — | not_run |
| `sha256_4way` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `blind` | FAIL (other) | 6 | — | — | $0.88 | — | not_run |

## Failing Round Breakdown

Each row counts failing rounds across all cells by root-cause category.

| Failure category | Failing rounds |
| --- | --- |
| `other` | 55 |
| `compile_or_parse_error` | 24 |
| `arith_need_entail` | 9 |
| `isa_table_error` | 8 |
| `calling_syntax_error` | 1 |
| `kept_reg_refusal` | 1 |
| `output_token_limit` | 1 |
