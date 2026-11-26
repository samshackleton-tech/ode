# Results: Pre-Registered Cold-Room Suite `ct-b64-v1`

- **Pre-registration commit:** `947b67591ca53675e9f282c1024e2508d7e10534`
- **Finished (UTC):** `2026-11-26T11:50:58Z`
- **Strict pass rate:** **6/28** finished cells
- **Independent second verifier (`verify2.py`):** **0/6** passing cells dual-verified
- **Real-silicon native harness:** **6/6** passing cells executed and passed on matching hardware
- **Total rounds / API spend:** 202 rounds, **$33.33** USD

## Cell-by-Cell Outcomes

Each row reports one cold-room cell: verdict, rounds used, API cost, compiled code size, `verify2.py` status, and real-silicon test result.

| Task | Model | Target | Arm | Verdict | Rounds | Initial -> Best `cyc/B` | Unroll (B/it) | Cost (USD) | `verify2.py` | Native CPU |
| --- | --- | --- | --- | --- | ---: | --- | ---: | ---: | --- | --- |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `arm64` | `advised` | PASS (R5, best R5) | 7 | — | — | $3.37 | — | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `arm64` | `blind` | PASS (R5, best R7) | 7 | — | 4 B | $3.50 | — | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `x86_64` | `advised` | PASS (R3, best R5) | 6 | — | 4 B | $3.44 | — | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `x86_64` | `blind` | FAIL (prover_timeout) | 6 | — | — | $3.87 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `arm64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.04 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `arm64` | `blind` | FAIL (arith_need_entail) | 8 | — | — | $0.05 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `x86_64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $0.06 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `x86_64` | `blind` | FAIL (arith_need_entail) | 8 | — | — | $0.06 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `arm64` | `advised` | PASS (R8, best R8) | 8 | — | — | $0.67 | — | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `arm64` | `blind` | FAIL (arith_need_entail) | 8 | — | — | $0.74 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `x86_64` | `advised` | FAIL (prover_timeout) | 8 | — | — | $0.76 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `x86_64` | `blind` | FAIL (other) | 8 | — | — | $0.83 | — | not_run |
| `ct_base64_decode` | `google/gemini-4-neon` | `arm64` | `advised` | FAIL (arith_need_entail) | 4 | — | — | $1.39 | — | not_run |
| `ct_base64_decode` | `google/gemini-4-neon` | `arm64` | `blind` | FAIL (other) | 3 | — | — | $1.11 | — | not_run |
| `ct_base64_decode` | `google/gemini-4-neon` | `x86_64` | `advised` | FAIL (arith_need_entail) | 7 | — | — | $1.21 | — | not_run |
| `ct_base64_decode` | `google/gemini-4-neon` | `x86_64` | `blind` | FAIL (prover_timeout) | 7 | — | — | $1.33 | — | not_run |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `arm64` | `advised` | FAIL (kept_reg_refusal) | 8 | — | — | $0.24 | — | not_run |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `arm64` | `blind` | FAIL (other) | 8 | — | — | $0.31 | — | not_run |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `advised` | FAIL (other) | 8 | — | — | $0.53 | — | not_run |
| `ct_base64_decode` | `moonshotai/kimi-k3.1-pro` | `x86_64` | `blind` | FAIL (arith_need_entail) | 8 | — | — | $0.37 | — | not_run |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `arm64` | `advised` | PASS (R3, best R3) | 8 | — | — | $2.05 | — | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `arm64` | `blind` | PASS (R3, best R3) | 8 | — | — | $1.86 | — | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `x86_64` | `advised` | FAIL (arith_need_entail) | 8 | — | — | $1.58 | — | not_run |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `x86_64` | `blind` | FAIL (arith_need_entail) | 8 | — | — | $1.80 | — | not_run |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `advised` | FAIL (calling_syntax_error) | 8 | — | — | $0.47 | — | not_run |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `blind` | FAIL (arith_need_entail) | 8 | — | — | $0.28 | — | not_run |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `advised` | FAIL (compile_or_parse_error) | 6 | — | — | $0.69 | — | not_run |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `blind` | FAIL (output_token_limit) | 5 | — | — | $0.72 | — | not_run |

## Failing Round Breakdown

Each row counts failing rounds across all cells by root-cause category.

| Failure category | Failing rounds |
| --- | --- |
| `arith_need_entail` | 87 |
| `other` | 46 |
| `compile_or_parse_error` | 27 |
| `prover_timeout` | 18 |
| `output_token_limit` | 5 |
| `isa_table_error` | 3 |
| `calling_syntax_error` | 1 |
| `kept_reg_refusal` | 1 |
