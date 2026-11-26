# Results: Pre-Registered Cold-Room Suite `utf8-v1`

- **Pre-registration commit:** `f6cfa5e38e9c91142ac36ad7f8e49be860d5d8e5`
- **Finished (UTC):** `2026-11-26T14:11:22Z`
- **Strict pass rate:** **26/28** finished cells
- **Independent second verifier (`verify2.py`):** **22/26** passing cells dual-verified
- **Real-silicon native harness:** **26/26** passing cells executed and passed on matching hardware
- **Total rounds / API spend:** 186 rounds, **$22.57** USD

## Cell-by-Cell Outcomes

Each row reports one cold-room cell: verdict, rounds used, API cost, compiled code size, `verify2.py` status, and real-silicon test result.

| Task | Model | Target | Arm | Verdict | Rounds | Initial -> Best `cyc/B` | Unroll (B/it) | Cost (USD) | `verify2.py` | Native CPU |
| --- | --- | --- | --- | --- | ---: | --- | ---: | ---: | --- | --- |
| `utf8_valid` | `anthropic/claude-fable-5.2` | `arm64` | `advised` | PASS (R1, best R5) | 6 | 4.00 -> **0.62** | 8 B | $2.24 | shown | NATIVE_PASS 680/680 |
| `utf8_valid` | `anthropic/claude-fable-5.2` | `arm64` | `blind` | PASS (R1, best R2) | 6 | 4.00 -> **0.62** | 8 B | $2.12 | shown | NATIVE_PASS 680/680 |
| `utf8_valid` | `anthropic/claude-fable-5.2` | `x86_64` | `advised` | PASS (R1, best R6) | 6 | 2.67 -> **0.62** | 8 B | $2.44 | shown | NATIVE_PASS 680/680 |
| `utf8_valid` | `anthropic/claude-fable-5.2` | `x86_64` | `blind` | PASS (R1, best R4) | 6 | 2.67 -> **0.50** | 8 B | $2.01 | shown | NATIVE_PASS 680/680 |
| `utf8_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.04 | — | not_run |
| `utf8_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `blind` | PASS (R2, best R2) | 7 | 4.00 -> **4.00** | 1 B | $0.03 | shown | NATIVE_PASS 680/680 |
| `utf8_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `advised` | PASS (R2, best R3) | 5 | 2.67 -> **2.67** | 1 B | $0.03 | shown | NATIVE_PASS 680/680 |
| `utf8_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `blind` | FAIL (arith_need_entail) | 8 | — | — | $0.05 | — | not_run |
| `utf8_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | `advised` | PASS (R2, best R2) | 6 | 2.00 -> **2.00** | 4 B | $0.42 | shown | NATIVE_PASS 680/680 |
| `utf8_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | `blind` | PASS (R2, best R3) | 6 | 1.17 -> **0.88** | 4 B | $0.39 | shown | NATIVE_PASS 680/680 |
| `utf8_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | `advised` | PASS (R1, best R1) | 4 | 1.00 -> **1.00** | 1 B | $0.29 | shown | NATIVE_PASS 680/680 |
| `utf8_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | `blind` | PASS (R1, best R3) | 5 | 2.67 -> **0.50** | 8 B | $0.38 | shown | NATIVE_PASS 680/680 |
| `utf8_valid` | `google/gemini-4-neon` | `arm64` | `advised` | PASS (R1, best R4) | 8 | 1.17 -> **0.33** | 8 B | $1.12 | refused | NATIVE_PASS 680/680 |
| `utf8_valid` | `google/gemini-4-neon` | `arm64` | `blind` | PASS (R1, best R3) | 7 | 1.17 -> **0.33** | 8 B | $0.87 | refused | NATIVE_PASS 680/680 |
| `utf8_valid` | `google/gemini-4-neon` | `x86_64` | `advised` | PASS (R1, best R7) | 8 | 1.00 -> **0.44** | 16 B | $1.11 | refused | NATIVE_PASS 680/680 |
| `utf8_valid` | `google/gemini-4-neon` | `x86_64` | `blind` | PASS (R1, best R7) | 7 | 1.00 -> **0.75** | 4 B | $1.10 | shown | NATIVE_PASS 680/680 |
| `utf8_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `advised` | PASS (R1, best R4) | 8 | 4.00 -> **0.62** | 8 B | $0.22 | shown | NATIVE_PASS 680/680 |
| `utf8_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `blind` | PASS (R1, best R5) | 8 | 4.00 -> **0.69** | 8 B | $0.20 | shown | NATIVE_PASS 680/680 |
| `utf8_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `advised` | PASS (R1, best R1) | 8 | 2.67 -> **2.67** | 1 B | $0.39 | shown | NATIVE_PASS 680/680 |
| `utf8_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `blind` | PASS (R1, best R4) | 8 | 2.67 -> **0.50** | 8 B | $0.39 | refused | NATIVE_PASS 680/680 |
| `utf8_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | `advised` | PASS (R1, best R4) | 7 | 4.00 -> **1.17** | 1 B | $1.28 | shown | NATIVE_PASS 680/680 |
| `utf8_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | `blind` | PASS (R1, best R4) | 6 | 4.00 -> **0.62** | 8 B | $1.47 | shown | NATIVE_PASS 680/680 |
| `utf8_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | `advised` | PASS (R1, best R6) | 6 | 2.67 -> **0.62** | 8 B | $1.18 | shown | NATIVE_PASS 680/680 |
| `utf8_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | `blind` | PASS (R1, best R4) | 6 | 1.71 -> **0.50** | 8 B | $1.78 | shown | NATIVE_PASS 680/680 |
| `utf8_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `advised` | PASS (R1, best R4) | 6 | 4.00 -> **0.62** | 8 B | $0.20 | shown | NATIVE_PASS 680/680 |
| `utf8_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `blind` | PASS (R1, best R7) | 8 | 4.00 -> **1.17** | 1 B | $0.31 | shown | NATIVE_PASS 680/680 |
| `utf8_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `advised` | PASS (R1, best R5) | 5 | 2.67 -> **0.50** | 8 B | $0.20 | shown | NATIVE_PASS 680/680 |
| `utf8_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `blind` | PASS (R1, best R4) | 7 | 2.67 -> **0.50** | 8 B | $0.32 | shown | NATIVE_PASS 680/680 |

## Failing Round Breakdown

Each row counts failing rounds across all cells by root-cause category.

| Failure category | Failing rounds |
| --- | --- |
| `arith_need_entail` | 64 |
| `other` | 15 |
| `compile_or_parse_error` | 4 |
| `isa_table_error` | 3 |
| `prover_timeout` | 3 |
| `arith_need_compare` | 2 |
| `kept_reg_refusal` | 1 |
| `trace_refusal` | 1 |
