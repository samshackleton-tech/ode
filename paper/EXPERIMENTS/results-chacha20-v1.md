# Results: Pre-Registered Cold-Room Suite `chacha20-v1`

- **Pre-registration commit:** `d6632d4418e035628d929989c3bac4b83931ec10`
- **Finished (UTC):** `2026-11-26T13:47:55Z`
- **Strict pass rate:** **24/28** finished cells
- **Independent second verifier (`verify2.py`):** **0/24** passing cells dual-verified
- **Real-silicon native harness:** **24/24** passing cells executed and passed on matching hardware
- **Total rounds / API spend:** 143 rounds, **$33.84** USD

## Cell-by-Cell Outcomes

Each row reports one cold-room cell: verdict, rounds used, API cost, compiled code size, `verify2.py` status, and real-silicon test result.

| Task | Model | Target | Arm | Verdict | Rounds | Initial -> Best `cyc/B` | Unroll (B/it) | Cost (USD) | `verify2.py` | Native CPU |
| --- | --- | --- | --- | --- | ---: | --- | ---: | ---: | --- | --- |
| `chacha20_4way` | `anthropic/claude-fable-5.2` | `arm64` | `advised` | PASS (R1, best R3) | 4 | 2.48 -> **2.41** | 256 B | $2.78 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-fable-5.2` | `arm64` | `blind` | PASS (R1, best R1) | 4 | 2.48 -> **2.48** | 256 B | $2.23 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-fable-5.2` | `x86_64` | `advised` | PASS (R1, best R2) | 4 | 1.71 -> **1.71** | 256 B | $3.23 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-fable-5.2` | `x86_64` | `blind` | PASS (R1, best R2) | 4 | 1.72 -> **1.70** | 256 B | $2.21 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `advised` | PASS (R3, best R3) | 6 | 2.41 -> **2.41** | 256 B | $0.06 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `blind` | PASS (R2, best R3) | 5 | 2.41 -> **2.41** | 256 B | $0.05 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `advised` | PASS (R7, best R7) | 8 | 2.07 -> **2.07** | 256 B | $0.10 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `blind` | PASS (R4, best R4) | 7 | 2.00 -> **2.00** | 256 B | $0.06 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-sonnet-5.5` | `arm64` | `advised` | PASS (R2, best R2) | 5 | 2.48 -> **2.48** | 256 B | $0.62 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-sonnet-5.5` | `arm64` | `blind` | PASS (R2, best R2) | 5 | 2.48 -> **2.48** | 256 B | $0.61 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-sonnet-5.5` | `x86_64` | `advised` | PASS (R1, best R1) | 4 | 1.94 -> **1.94** | 256 B | $0.57 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-sonnet-5.5` | `x86_64` | `blind` | PASS (R4, best R4) | 7 | 2.05 -> **2.05** | 256 B | $0.81 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `google/gemini-4-neon` | `arm64` | `advised` | PASS (R1, best R4) | 4 | 2.63 -> **2.40** | 256 B | $1.30 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `google/gemini-4-neon` | `arm64` | `blind` | PASS (R1, best R3) | 3 | 2.63 -> **2.40** | 256 B | $1.30 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `google/gemini-4-neon` | `x86_64` | `advised` | PASS (R1, best R4) | 4 | 1.71 -> **1.70** | 256 B | $1.50 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `google/gemini-4-neon` | `x86_64` | `blind` | PASS (R1, best R2) | 4 | 1.72 -> **1.70** | 256 B | $1.43 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `advised` | PASS (R1, best R3) | 3 | 2.63 -> **2.41** | 256 B | $0.62 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `arm64` | `blind` | PASS (R3, best R3) | 7 | 2.42 -> **2.42** | 256 B | $0.65 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `advised` | FAIL (other) | 8 | — | — | $0.41 | — | not_run |
| `chacha20_4way` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `blind` | PASS (R1, best R3) | 4 | 2.04 -> **2.02** | 256 B | $0.35 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `openai/gpt-6.2-astra-pro` | `arm64` | `advised` | PASS (R1, best R2) | 4 | 2.41 -> **2.34** | 256 B | $3.36 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `openai/gpt-6.2-astra-pro` | `arm64` | `blind` | PASS (R1, best R4) | 4 | 2.41 -> **2.41** | 256 B | $2.87 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `openai/gpt-6.2-astra-pro` | `x86_64` | `advised` | PASS (R1, best R5) | 5 | 1.72 -> **1.71** | 256 B | $1.82 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `openai/gpt-6.2-astra-pro` | `x86_64` | `blind` | PASS (R1, best R5) | 5 | 1.71 -> **1.70** | 256 B | $2.36 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `advised` | PASS (R7, best R8) | 8 | 7.58 -> **2.48** | 256 B | $0.57 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `blind` | FAIL (compile_or_parse_error) | 6 | — | — | $0.84 | — | not_run |
| `chacha20_4way` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `advised` | FAIL (compile_or_parse_error) | 3 | — | — | $0.54 | — | not_run |
| `chacha20_4way` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `blind` | FAIL (other) | 8 | — | — | $0.59 | — | not_run |

## Failing Round Breakdown

Each row counts failing rounds across all cells by root-cause category.

| Failure category | Failing rounds |
| --- | --- |
| `other` | 37 |
| `compile_or_parse_error` | 10 |
| `isa_table_error` | 3 |
| `output_token_limit` | 2 |
| `arith_need_entail` | 1 |
