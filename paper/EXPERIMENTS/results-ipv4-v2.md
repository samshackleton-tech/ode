# Results: Pre-Registered Cold-Room Suite `ipv4-v2`

- **Pre-registration commit:** `51fac777059c8a37f7bf679f467469ea107b3956`
- **Finished (UTC):** `2026-11-26T14:01:39Z`
- **Strict pass rate:** **18/28** finished cells
- **Independent second verifier (`verify2.py`):** **18/18** passing cells dual-verified
- **Real-silicon native harness:** **18/18** passing cells executed and passed on matching hardware
- **Total rounds / API spend:** 201 rounds, **$27.26** USD

## Cell-by-Cell Outcomes

Each row reports one cold-room cell: verdict, rounds used, API cost, compiled code size, `verify2.py` status, and real-silicon test result.

| Task | Model | Target | Arm | Verdict | Rounds | Initial -> Best `cyc/B` | Unroll (B/it) | Cost (USD) | `verify2.py` | Native CPU |
| --- | --- | --- | --- | --- | ---: | --- | ---: | ---: | --- | --- |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `arm64` | `advised` | PASS (R1, best R1) | 6 | 0.46 -> **0.46** | 4 B | $2.43 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `arm64` | `blind` | PASS (R1, best R5) | 7 | 0.67 -> **0.67** | 2 B | $3.16 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `x86_64` | `advised` | PASS (R1, best R1) | 8 | 0.75 -> **0.75** | 4 B | $3.11 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `x86_64` | `blind` | PASS (R1, best R1) | 7 | 0.75 -> **0.75** | 4 B | $3.01 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.04 | — | not_run |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `blind` | FAIL (prover_timeout) | 8 | — | — | $0.03 | — | not_run |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `advised` | PASS (R3, best R3) | 8 | 1.00 -> **1.00** | 2 B | $0.04 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `blind` | FAIL (arith_need_entail) | 8 | — | — | $0.04 | — | not_run |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | `advised` | PASS (R2, best R2) | 5 | 1.00 -> **1.00** | 2 B | $0.27 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | `blind` | PASS (R1, best R3) | 6 | 0.67 -> **0.50** | 4 B | $0.37 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | `advised` | PASS (R2, best R2) | 5 | 1.00 -> **1.00** | 2 B | $0.35 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | `blind` | PASS (R1, best R3) | 6 | 1.00 -> **0.75** | 4 B | $0.44 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `google/gemini-4-neon` | `arm64` | `advised` | PASS (R6, best R6) | 7 | 1.12 -> **1.12** | 17 B | $1.21 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `google/gemini-4-neon` | `arm64` | `blind` | PASS (R5, best R5) | 5 | 1.18 -> **1.18** | 17 B | $1.24 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `google/gemini-4-neon` | `x86_64` | `advised` | FAIL (prover_timeout) | 5 | — | — | $1.00 | — | not_run |
| `ipv4_valid` | `google/gemini-4-neon` | `x86_64` | `blind` | FAIL (prover_timeout) | 7 | — | — | $1.09 | — | not_run |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `advised` | FAIL (other) | 8 | — | — | $0.28 | — | not_run |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `blind` | PASS (R6, best R6) | 8 | 0.67 -> **0.67** | 2 B | $0.22 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `advised` | PASS (R6, best R6) | 8 | 1.00 -> **1.00** | 2 B | $0.24 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `blind` | FAIL (compile_or_parse_error) | 8 | — | — | $0.33 | — | not_run |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | `advised` | PASS (R2, best R8) | 8 | 0.46 -> **0.38** | 4 B | $1.65 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | `blind` | PASS (R1, best R1) | 8 | 0.46 -> **0.46** | 4 B | $1.99 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | `advised` | PASS (R1, best R7) | 7 | 0.75 -> **0.75** | 4 B | $1.60 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | `blind` | PASS (R1, best R5) | 8 | 0.75 -> **0.75** | 4 B | $1.93 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `advised` | PASS (R3, best R6) | 8 | 0.67 -> **0.50** | 4 B | $0.43 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `blind` | FAIL (arith_need_entail) | 8 | — | — | $0.24 | — | not_run |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.26 | — | not_run |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `blind` | FAIL (prover_timeout) | 8 | — | — | $0.25 | — | not_run |

## Failing Round Breakdown

Each row counts failing rounds across all cells by root-cause category.

| Failure category | Failing rounds |
| --- | --- |
| `arith_need_entail` | 51 |
| `prover_timeout` | 44 |
| `other` | 27 |
| `compile_or_parse_error` | 16 |
| `arith_need_compare` | 3 |
| `kept_reg_refusal` | 1 |
| `trace_refusal` | 1 |

## Before vs. After Comparison (`ipv4-v1` -> `ipv4-v2`)

The first table compares totals over the 28 cells that both runs have (the same task, model, target, and arm); each cell was run once in each run, so a difference in one cell may be chance. The second table sets each such cell of the two runs side by side.

| Metric (over the 28 shared cells) | `ipv4-v1` | `ipv4-v2` | Delta |
| --- | --- | --- | --- |
| Strict passes | 14/28 | 18/28 | +4 |
| Total rounds | 202 | 201 | -1 |
| Total API spend (USD) | $27.51 | $27.26 | $-0.25 |
| Failing rounds: `arith_need_compare` | 5 | 3 | -2 |
| Failing rounds: `arith_need_entail` | 53 | 51 | -2 |
| Failing rounds: `compile_or_parse_error` | 13 | 16 | +3 |
| Failing rounds: `isa_table_error` | 1 | 0 | -1 |
| Failing rounds: `kept_reg_refusal` | 1 | 1 | +0 |
| Failing rounds: `other` | 39 | 27 | -12 |
| Failing rounds: `output_token_limit` | 1 | 0 | -1 |
| Failing rounds: `prover_timeout` | 47 | 44 | -3 |
| Failing rounds: `trace_refusal` | 0 | 1 | +1 |

| Task | Model | Target | Arm | `ipv4-v1` | `ipv4-v2` |
| --- | --- | --- | --- | --- | --- |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `arm64` | `advised` | PASS (R1, $2.67) | PASS (R1, $2.43) |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `arm64` | `blind` | PASS (R2, $2.04) | PASS (R1, $3.16) |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `x86_64` | `advised` | PASS (R1, $2.47) | PASS (R1, $3.11) |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `x86_64` | `blind` | PASS (R1, $3.71) | PASS (R1, $3.01) |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `advised` | FAIL ($0.04) | FAIL ($0.04) |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `blind` | FAIL ($0.03) | FAIL ($0.03) |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `advised` | FAIL ($0.04) | PASS (R3, $0.04) |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `blind` | FAIL ($0.04) | FAIL ($0.04) |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | `advised` | FAIL ($0.52) | PASS (R2, $0.27) |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | `blind` | PASS (R2, $0.35) | PASS (R1, $0.37) |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | `advised` | PASS (R2, $0.41) | PASS (R2, $0.35) |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | `blind` | FAIL ($0.94) | PASS (R1, $0.44) |
| `ipv4_valid` | `google/gemini-4-neon` | `arm64` | `advised` | PASS (R4, $1.15) | PASS (R6, $1.21) |
| `ipv4_valid` | `google/gemini-4-neon` | `arm64` | `blind` | PASS (R6, $1.24) | PASS (R5, $1.24) |
| `ipv4_valid` | `google/gemini-4-neon` | `x86_64` | `advised` | FAIL ($1.10) | FAIL ($1.00) |
| `ipv4_valid` | `google/gemini-4-neon` | `x86_64` | `blind` | FAIL ($1.14) | FAIL ($1.09) |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `advised` | FAIL ($0.29) | FAIL ($0.28) |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `arm64` | `blind` | PASS (R4, $0.21) | PASS (R6, $0.22) |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `advised` | FAIL ($0.27) | PASS (R6, $0.24) |
| `ipv4_valid` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `blind` | PASS (R4, $0.45) | FAIL ($0.33) |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | `advised` | PASS (R1, $1.36) | PASS (R2, $1.65) |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | `blind` | PASS (R1, $1.92) | PASS (R1, $1.99) |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | `advised` | PASS (R1, $1.74) | PASS (R1, $1.60) |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | `blind` | PASS (R1, $2.24) | PASS (R1, $1.93) |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `advised` | FAIL ($0.36) | PASS (R3, $0.43) |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `blind` | FAIL ($0.25) | FAIL ($0.24) |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `advised` | FAIL ($0.24) | FAIL ($0.26) |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `blind` | FAIL ($0.31) | FAIL ($0.25) |
