# Results: Pre-Registered Cold-Room Suite `ipv4-v1`

- **Pre-registration commit:** `9180eeaf91a444408580014f4c253a08cae05331`
- **Finished (UTC):** `2026-11-26T13:25:34Z`
- **Strict pass rate:** **14/28** finished cells
- **Independent second verifier (`verify2.py`):** **14/14** passing cells dual-verified
- **Real-silicon native harness:** **14/14** passing cells executed and passed on matching hardware
- **Total rounds / API spend:** 202 rounds, **$27.51** USD

## Cell-by-Cell Outcomes

Each row reports one cold-room cell: verdict, rounds used, API cost, compiled code size, `verify2.py` status, and real-silicon test result.

| Task | Model | Target | Arm | Verdict | Rounds | Initial -> Best `cyc/B` | Unroll (B/it) | Cost (USD) | `verify2.py` | Native CPU |
| --- | --- | --- | --- | --- | ---: | --- | ---: | ---: | --- | --- |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `arm64` | `advised` | PASS (R1, best R5) | 7 | 1.00 -> **0.50** | 4 B | $2.67 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `arm64` | `blind` | PASS (R2, best R4) | 6 | 0.67 -> **0.46** | 4 B | $2.04 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `x86_64` | `advised` | PASS (R1, best R1) | 6 | 0.75 -> **0.75** | 4 B | $2.47 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `x86_64` | `blind` | PASS (R1, best R1) | 7 | 0.75 -> **0.75** | 4 B | $3.71 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `advised` | FAIL (prover_timeout) | 8 | — | — | $0.04 | — | not_run |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `blind` | FAIL (prover_timeout) | 8 | — | — | $0.03 | — | not_run |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `advised` | FAIL (prover_timeout) | 8 | — | — | $0.04 | — | not_run |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `blind` | FAIL (arith_need_entail) | 8 | — | — | $0.04 | — | not_run |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | `advised` | FAIL (other) | 8 | — | — | $0.52 | — | not_run |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | `blind` | PASS (R2, best R3) | 6 | 0.67 -> **0.50** | 4 B | $0.35 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | `advised` | PASS (R2, best R2) | 6 | 1.00 -> **1.00** | 2 B | $0.41 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | `blind` | FAIL (kept_reg_refusal) | 8 | — | — | $0.94 | — | not_run |
| `ipv4_valid` | `google/gemini-4-neon` | `arm64` | `advised` | PASS (R4, best R4) | 5 | 0.95 -> **0.95** | 21 B | $1.15 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `google/gemini-4-neon` | `arm64` | `blind` | PASS (R6, best R6) | 7 | 0.95 -> **0.95** | 21 B | $1.24 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `google/gemini-4-neon` | `x86_64` | `advised` | FAIL (other) | 6 | — | — | $1.10 | — | not_run |
| `ipv4_valid` | `google/gemini-4-neon` | `x86_64` | `blind` | FAIL (other) | 8 | — | — | $1.14 | — | not_run |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `advised` | FAIL (other) | 8 | — | — | $0.29 | — | not_run |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `blind` | PASS (R4, best R4) | 8 | 0.50 -> **0.50** | 4 B | $0.21 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.27 | — | not_run |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `blind` | PASS (R4, best R4) | 5 | 0.75 -> **0.75** | 4 B | $0.45 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | `advised` | PASS (R1, best R6) | 6 | 0.46 -> **0.42** | 4 B | $1.36 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | `blind` | PASS (R1, best R4) | 8 | 0.42 -> **0.38** | 8 B | $1.92 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | `advised` | PASS (R1, best R4) | 7 | 0.75 -> **0.50** | 8 B | $1.74 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | `blind` | PASS (R1, best R1) | 8 | 0.75 -> **0.75** | 4 B | $2.24 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `advised` | FAIL (prover_timeout) | 8 | — | — | $0.36 | — | not_run |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `blind` | FAIL (prover_timeout) | 8 | — | — | $0.25 | — | not_run |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.24 | — | not_run |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `blind` | FAIL (arith_need_entail) | 8 | — | — | $0.31 | — | not_run |

## Failing Round Breakdown

Each row counts failing rounds across all cells by root-cause category.

| Failure category | Failing rounds |
| --- | --- |
| `arith_need_entail` | 53 |
| `prover_timeout` | 47 |
| `other` | 39 |
| `compile_or_parse_error` | 13 |
| `arith_need_compare` | 5 |
| `isa_table_error` | 1 |
| `kept_reg_refusal` | 1 |
| `output_token_limit` | 1 |
