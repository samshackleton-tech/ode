# Results: Pre-Registered Cold-Room Suite `suite-v6`

- **Pre-registration commit:** `f549ad78cf86f6e24d1c1badeccf4143770df403`
- **Finished (UTC):** `2026-11-26T05:45:11Z`
- **Strict pass rate:** **12/16** finished cells
- **Independent second verifier (`verify2.py`):** **12/12** passing cells dual-verified
- **Real-silicon native harness:** **12/12** passing cells executed and passed on matching hardware
- **Total rounds / API spend:** 44 rounds, **$13.19** USD

## Cell-by-Cell Outcomes

Each row reports one cold-room cell: verdict, rounds used, API cost, compiled code size, `verify2.py` status, and real-silicon test result.

| Task | Model | Target | Verdict | Rounds | Cost (USD) | Code | `verify2.py` | Native CPU |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `ebpf` | `anthropic/claude-fable-5.2` | `arm64` | PASS (R1) | 1 | $0.90 | 6 fns / 193 insns / 820 B | shown | NATIVE_PASS 7/7 |
| `ebpf` | `anthropic/claude-fable-5.2` | `x86_64` | FAIL (output_token_limit) | 3 | $3.19 | — | — | not_run |
| `ebpf` | `anthropic/claude-sonnet-5.5` | `arm64` | FAIL (prover_timeout_120s) | 7 | $0.91 | — | — | not_run |
| `ebpf` | `anthropic/claude-sonnet-5.5` | `x86_64` | FAIL (prover_timeout_120s) | 7 | $0.87 | — | — | not_run |
| `ebpf` | `google/gemini-4-neon` | `arm64` | FAIL (prover_timeout_120s) | 4 | $1.64 | — | — | not_run |
| `ebpf` | `google/gemini-4-neon` | `x86_64` | PASS (R3) | 3 | $0.76 | 6 fns / 223 insns / 845 B | shown | NATIVE_PASS 7/7 |
| `ebpf` | `openai/gpt-6.2-astra-pro` | `arm64` | PASS (R3) | 3 | $1.22 | 6 fns / 183 insns / 768 B | shown | NATIVE_PASS 7/7 |
| `ebpf` | `openai/gpt-6.2-astra-pro` | `x86_64` | PASS (R4) | 4 | $1.71 | 7 fns / 192 insns / 702 B | shown | NATIVE_PASS 7/7 |
| `header_score` | `anthropic/claude-fable-5.2` | `arm64` | PASS (R1) | 1 | $0.26 | 1 fns / 67 insns / 268 B | shown | NATIVE_PASS 1021/1021 |
| `header_score` | `anthropic/claude-fable-5.2` | `x86_64` | PASS (R1) | 1 | $0.28 | 1 fns / 66 insns / 249 B | shown | NATIVE_PASS 1021/1021 |
| `header_score` | `anthropic/claude-sonnet-5.5` | `arm64` | PASS (R4) | 4 | $0.28 | 1 fns / 67 insns / 268 B | shown | NATIVE_PASS 1021/1021 |
| `header_score` | `anthropic/claude-sonnet-5.5` | `x86_64` | PASS (R2) | 2 | $0.17 | 1 fns / 82 insns / 297 B | shown | NATIVE_PASS 1021/1021 |
| `header_score` | `google/gemini-4-neon` | `arm64` | PASS (R1) | 1 | $0.15 | 1 fns / 67 insns / 268 B | shown | NATIVE_PASS 1021/1021 |
| `header_score` | `google/gemini-4-neon` | `x86_64` | PASS (R1) | 1 | $0.15 | 1 fns / 66 insns / 249 B | shown | NATIVE_PASS 1021/1021 |
| `header_score` | `openai/gpt-6.2-astra-pro` | `arm64` | PASS (R1) | 1 | $0.32 | 1 fns / 67 insns / 268 B | shown | NATIVE_PASS 1021/1021 |
| `header_score` | `openai/gpt-6.2-astra-pro` | `x86_64` | PASS (R1) | 1 | $0.39 | 1 fns / 66 insns / 249 B | shown | NATIVE_PASS 1021/1021 |

## Failing Round Breakdown

Each row counts failing rounds across all cells by root-cause category.

| Failure category | Failing rounds |
| --- | --- |
| `prover_timeout_120s` | 21 |
| `arith_need_entail` | 3 |
| `kept_reg_refusal` | 3 |
| `calling_syntax_error` | 1 |
| `compile_or_parse_error` | 1 |
| `other` | 1 |
| `output_token_limit` | 1 |
| `spec_need_open` | 1 |

## Notes written after the run

- **Comparison with `results-suite-v5.md`:** Strict passes rose from **11/16** (54 rounds, $13.83 USD) to **12/16** (44 rounds, $13.19 USD), with **12/12** passing cells dual-verified by `verify2.py` and **12/12** passing on matching native CPUs.
- **Zero-boilerplate `place { ... }` adoption:** **15/16** cells (and **12/12** passing cells) omitted `name x = reg` declarations inside `place { ... }`, writing `reg` aliases and 64-bit hardware registers directly in `fact` and `decreases`.
- **`header_score` reached 8/8 (100%):** In `suite-v5`, `claude-sonnet-5.5` failed both targets (`0/2`) with zero join points on `need below`. In `suite-v6`, with the new `need below` specification-condition and join-point hint, `claude-sonnet-5.5` inserted 16 zero-boilerplate join points and passed both `x86_64` (Round 2, $0.17) and `arm64` (Round 4, $0.28). All six other cells passed on Round 1.
- **`ebpf` outcomes (4/8 vs. 5/8 in `suite-v5`):** `claude-fable-5.2` on `arm64` dropped from Round 4 ($2.73, 220 insns) to **Round 1 ($0.90, 193 insns)**. Both `gpt-6.2-astra-pro` targets and `gemini-4-neon` on `x86_64` passed. The four failing `ebpf` cells all reached the 900 s cell wall-clock cap after repeated `prover_timeout_120s` rounds (21 of 32 failing rounds = 65.6%), and `claude-fable-5.2` on `x86_64` also hit one `output_token_limit` truncation on Round 3.
- **Causal attribution caveat:** `suite-v6` ran on `be0ddc9f` (which bundled zero-boilerplate `place`, the `need below`/`stack` diagnostics, and `verify2.py` completeness fixes, and predated the `190cac74` prover fast-fail change). The `header_score` jump (`6/8 -> 8/8`) and `15/16` boilerplate elimination match the targeted changes directly, while single-run LLM variance accounts for `ebpf` shifting between 5/8 and 4/8.

