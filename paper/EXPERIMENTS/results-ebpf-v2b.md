# Results: Pre-Registered Cold-Room Suite `ebpf-v2b`

- **Pre-registration commit:** `fa68451a8e4fa53807acd866cbb6a408da5aae9a`
- **Finished (UTC):** `2026-11-25T20:57:42Z`
- **Strict pass rate:** **5/8** cells
- **Independent second verifier (`verify2.py`):** **4/5** passing cells dual-verified
- **Real-silicon native harness:** **5/5** passing cells executed and passed on matching hardware
- **Total rounds / API spend:** 46 rounds, **$13.80** USD

## Cell-by-Cell Outcomes

Each row reports one cold-room cell: verdict, rounds used, API cost, compiled code size, `verify2.py` status, and real-silicon test result.

| Task | Model | Target | Verdict | Rounds | Cost (USD) | Code | `verify2.py` | Native CPU |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `ebpf` | `anthropic/claude-fable-5.2` | `arm64` | PASS (R7) | 7 | $3.96 | 6 fns / 199 insns / 844 B | shown | NATIVE_PASS 7/7 |
| `ebpf` | `anthropic/claude-fable-5.2` | `x86_64` | PASS (R3) | 3 | $1.99 | 5 fns / 189 insns / 677 B | shown | NATIVE_PASS 7/7 |
| `ebpf` | `anthropic/claude-sonnet-5.5` | `arm64` | FAIL (prover_timeout_120s) | 8 | $1.01 | — | — | not_run |
| `ebpf` | `anthropic/claude-sonnet-5.5` | `x86_64` | FAIL (arith_need_entail) | 8 | $0.91 | — | — | not_run |
| `ebpf` | `google/gemini-4-neon` | `arm64` | FAIL (compile_or_parse_error) | 8 | $2.01 | — | — | not_run |
| `ebpf` | `google/gemini-4-neon` | `x86_64` | PASS (R3) | 3 | $0.74 | 6 fns / 198 insns / 736 B | shown | NATIVE_PASS 7/7 |
| `ebpf` | `openai/gpt-6.2-astra-pro` | `arm64` | PASS (R2) | 2 | $0.72 | 6 fns / 174 insns / 728 B | shown | NATIVE_PASS 7/7 |
| `ebpf` | `openai/gpt-6.2-astra-pro` | `x86_64` | PASS (R7) | 7 | $2.46 | 7 fns / 201 insns / 738 B | refused | NATIVE_PASS 7/7 |

## Failing Round Breakdown

Each row counts failing rounds across all cells by root-cause category.

| Failure category | Failing rounds |
| --- | --- |
| `arith_need_entail` | 13 |
| `compile_or_parse_error` | 11 |
| `prover_timeout_120s` | 8 |
| `spec_need_open` | 6 |
| `kept_reg_refusal` | 2 |
| `other` | 1 |

## Before vs. After Comparison (`ebpf-v1` -> `ebpf-v2b`)

The first table compares aggregate suite metrics; the second compares each matching `(task, model, target)` cell.

| Metric | `ebpf-v1` | `ebpf-v2b` | Delta |
| --- | --- | --- | --- |
| Strict passes | 3/8 | 5/8 | +2 |
| Total rounds | 60 | 46 | -14 |
| Total API spend (USD) | $18.17 | $13.80 | $-4.38 |
| Failing rounds: `arith_need_entail` | 4 | 13 | +9 |
| Failing rounds: `compile_or_parse_error` | 22 | 11 | -11 |
| Failing rounds: `kept_reg_refusal` | 3 | 2 | -1 |
| Failing rounds: `other` | 6 | 1 | -5 |
| Failing rounds: `prover_timeout_120s` | 18 | 8 | -10 |
| Failing rounds: `spec_need_open` | 0 | 6 | +6 |
| Failing rounds: `trace_refusal` | 4 | 0 | -4 |

| Task | Model | Target | `ebpf-v1` | `ebpf-v2b` |
| --- | --- | --- | --- | --- |
| `ebpf` | `anthropic/claude-fable-5.2` | `arm64` | FAIL ($4.35) | PASS (R7, $3.96) |
| `ebpf` | `anthropic/claude-fable-5.2` | `x86_64` | FAIL ($4.56) | PASS (R3, $1.99) |
| `ebpf` | `anthropic/claude-sonnet-5.5` | `arm64` | FAIL ($0.74) | FAIL ($1.01) |
| `ebpf` | `anthropic/claude-sonnet-5.5` | `x86_64` | FAIL ($0.85) | FAIL ($0.91) |
| `ebpf` | `google/gemini-4-neon` | `arm64` | FAIL ($1.64) | FAIL ($2.01) |
| `ebpf` | `google/gemini-4-neon` | `x86_64` | PASS (R7, $1.30) | PASS (R3, $0.74) |
| `ebpf` | `openai/gpt-6.2-astra-pro` | `arm64` | PASS (R8, $2.85) | PASS (R2, $0.72) |
| `ebpf` | `openai/gpt-6.2-astra-pro` | `x86_64` | PASS (R5, $1.89) | PASS (R7, $2.46) |
