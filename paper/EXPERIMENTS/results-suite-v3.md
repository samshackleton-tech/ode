# Results: Pre-Registered Cold-Room Suite `suite-v3`

- **Pre-registration commit:** `bca36172332a0c9a2ffcee4009fba475a27a7c2e`
- **Finished (UTC):** `2026-11-25T22:21:08Z`
- **Strict pass rate:** **13/16** cells
- **Independent second verifier (`verify2.py`):** **9/13** passing cells dual-verified
- **Real-silicon native harness:** **13/13** passing cells executed and passed on matching hardware
- **Total rounds / API spend:** 42 rounds, **$12.41** USD

## Cell-by-Cell Outcomes

Each row reports one cold-room cell: verdict, rounds used, API cost, compiled code size, `verify2.py` status, and real-silicon test result.

| Task | Model | Target | Verdict | Rounds | Cost (USD) | Code | `verify2.py` | Native CPU |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `ct_eq` | `anthropic/claude-fable-5.2` | `arm64` | PASS (R1) | 1 | $0.13 | 1 fns / 20 insns / 80 B | refused | NATIVE_PASS 5/5 |
| `ct_eq` | `anthropic/claude-fable-5.2` | `x86_64` | PASS (R1) | 1 | $0.19 | 1 fns / 21 insns / 87 B | shown | NATIVE_PASS 5/5 |
| `ct_eq` | `anthropic/claude-sonnet-5.5` | `arm64` | PASS (R1) | 1 | $0.03 | 1 fns / 20 insns / 80 B | refused | NATIVE_PASS 5/5 |
| `ct_eq` | `anthropic/claude-sonnet-5.5` | `x86_64` | PASS (R1) | 1 | $0.05 | 1 fns / 21 insns / 85 B | shown | NATIVE_PASS 5/5 |
| `ct_eq` | `google/gemini-4-neon` | `arm64` | PASS (R1) | 1 | $0.07 | 1 fns / 20 insns / 80 B | refused | NATIVE_PASS 5/5 |
| `ct_eq` | `google/gemini-4-neon` | `x86_64` | PASS (R1) | 1 | $0.08 | 1 fns / 21 insns / 87 B | shown | NATIVE_PASS 5/5 |
| `ct_eq` | `openai/gpt-6.2-astra-pro` | `arm64` | PASS (R1) | 1 | $0.21 | 1 fns / 20 insns / 80 B | refused | NATIVE_PASS 5/5 |
| `ct_eq` | `openai/gpt-6.2-astra-pro` | `x86_64` | PASS (R1) | 1 | $0.27 | 1 fns / 21 insns / 87 B | shown | NATIVE_PASS 5/5 |
| `ebpf` | `anthropic/claude-fable-5.2` | `arm64` | PASS (R1) | 1 | $0.99 | 5 fns / 203 insns / 848 B | shown | NATIVE_PASS 7/7 |
| `ebpf` | `anthropic/claude-fable-5.2` | `x86_64` | PASS (R1) | 1 | $0.94 | 6 fns / 246 insns / 918 B | shown | NATIVE_PASS 7/7 |
| `ebpf` | `anthropic/claude-sonnet-5.5` | `arm64` | FAIL (arith_need_compare) | 8 | $0.98 | — | — | not_run |
| `ebpf` | `anthropic/claude-sonnet-5.5` | `x86_64` | FAIL (compile_or_parse_error) | 8 | $1.02 | — | — | not_run |
| `ebpf` | `google/gemini-4-neon` | `arm64` | FAIL (output_token_limit) | 8 | $3.96 | — | — | not_run |
| `ebpf` | `google/gemini-4-neon` | `x86_64` | PASS (R5) | 5 | $2.13 | 6 fns / 198 insns / 718 B | shown | NATIVE_PASS 7/7 |
| `ebpf` | `openai/gpt-6.2-astra-pro` | `arm64` | PASS (R2) | 2 | $0.78 | 6 fns / 178 insns / 740 B | shown | NATIVE_PASS 7/7 |
| `ebpf` | `openai/gpt-6.2-astra-pro` | `x86_64` | PASS (R1) | 1 | $0.57 | 6 fns / 188 insns / 677 B | shown | NATIVE_PASS 7/7 |

## Failing Round Breakdown

Each row counts failing rounds across all cells by root-cause category.

| Failure category | Failing rounds |
| --- | --- |
| `arith_need_compare` | 10 |
| `compile_or_parse_error` | 6 |
| `output_token_limit` | 6 |
| `prover_timeout_120s` | 6 |
| `kept_reg_refusal` | 1 |

## Before vs. After Comparison (`ebpf-v2b` -> `suite-v3`)

The first table compares totals over the 8 cells that both runs have (the same task, model and target); each cell was run once in each run, so a difference in one cell may be chance. The second table sets each such cell of the two runs side by side.

| Metric (over the 8 shared cells) | `ebpf-v2b` | `suite-v3` | Delta |
| --- | --- | --- | --- |
| Strict passes | 5/8 | 5/8 | +0 |
| Total rounds | 46 | 34 | -12 |
| Total API spend (USD) | $13.80 | $11.37 | $-2.43 |
| Failing rounds: `arith_need_compare` | 0 | 10 | +10 |
| Failing rounds: `arith_need_entail` | 13 | 0 | -13 |
| Failing rounds: `compile_or_parse_error` | 11 | 6 | -5 |
| Failing rounds: `kept_reg_refusal` | 2 | 1 | -1 |
| Failing rounds: `other` | 1 | 0 | -1 |
| Failing rounds: `output_token_limit` | 0 | 6 | +6 |
| Failing rounds: `prover_timeout_120s` | 8 | 6 | -2 |
| Failing rounds: `spec_need_open` | 6 | 0 | -6 |

| Task | Model | Target | `ebpf-v2b` | `suite-v3` |
| --- | --- | --- | --- | --- |
| `ct_eq` | `anthropic/claude-fable-5.2` | `arm64` | — | PASS (R1, $0.13) |
| `ct_eq` | `anthropic/claude-fable-5.2` | `x86_64` | — | PASS (R1, $0.19) |
| `ct_eq` | `anthropic/claude-sonnet-5.5` | `arm64` | — | PASS (R1, $0.03) |
| `ct_eq` | `anthropic/claude-sonnet-5.5` | `x86_64` | — | PASS (R1, $0.05) |
| `ct_eq` | `google/gemini-4-neon` | `arm64` | — | PASS (R1, $0.07) |
| `ct_eq` | `google/gemini-4-neon` | `x86_64` | — | PASS (R1, $0.08) |
| `ct_eq` | `openai/gpt-6.2-astra-pro` | `arm64` | — | PASS (R1, $0.21) |
| `ct_eq` | `openai/gpt-6.2-astra-pro` | `x86_64` | — | PASS (R1, $0.27) |
| `ebpf` | `anthropic/claude-fable-5.2` | `arm64` | PASS (R7, $3.96) | PASS (R1, $0.99) |
| `ebpf` | `anthropic/claude-fable-5.2` | `x86_64` | PASS (R3, $1.99) | PASS (R1, $0.94) |
| `ebpf` | `anthropic/claude-sonnet-5.5` | `arm64` | FAIL ($1.01) | FAIL ($0.98) |
| `ebpf` | `anthropic/claude-sonnet-5.5` | `x86_64` | FAIL ($0.91) | FAIL ($1.02) |
| `ebpf` | `google/gemini-4-neon` | `arm64` | FAIL ($2.01) | FAIL ($3.96) |
| `ebpf` | `google/gemini-4-neon` | `x86_64` | PASS (R3, $0.74) | PASS (R5, $2.13) |
| `ebpf` | `openai/gpt-6.2-astra-pro` | `arm64` | PASS (R2, $0.72) | PASS (R2, $0.78) |
| `ebpf` | `openai/gpt-6.2-astra-pro` | `x86_64` | PASS (R7, $2.46) | PASS (R1, $0.57) |

## Notes written after the run

1. **The eight `ct_eq` cells are not a test of writing such code.** The Quickstart that every model is given holds the complete solution of this task as its worked example. The eight passes at the first round show that the models can reproduce the example and that the tools accept it on both processors, and nothing more. This was found after the run was launched. A neighbouring task that the Quickstart does not hold was run separately (`results-ct-count-v1.md`).
2. **No cause can be read off the comparison with `ebpf-v2b`.** Two things changed between the two runs (the wording of the `need compare` refusal, and the output limit, from 16,000 to 32,000 tokens), each cell was run once in each run, and sixteen cells ran at once on one machine here against eight there, which can add prover timeouts. The same five of the eight `ebpf` cells pass in both runs.
3. **The rows `arith_need_entail` and `arith_need_compare` are one row under two names.** In `ebpf-v2b` a `need compare` refusal was counted as `arith_need_entail`; here it has its own name. Likewise a reply cut off by the output limit was counted as `compile_or_parse_error` there and is `output_token_limit` here.
4. **The new wording of `need compare` did not get `claude-sonnet-5.5` past it:** ten of its failing rounds here are that refusal.
5. **`verify2.py` "refused" on the four AArch64 `ct_eq` cells was a fault of `verify2.py`,** which numbered two of AArch64's registers otherwise than the proof format does. With that put right (commit `65938947`) it shows all thirteen passing bundles of this run.
