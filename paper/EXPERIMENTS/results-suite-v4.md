# Results: Pre-Registered Cold-Room Suite `suite-v4`

- **Pre-registration commit:** `fa967904b8959fe1621bbecaf1f0d3293a379fa4`
- **Finished (UTC):** `2026-11-25T23:53:39Z`
- **Strict pass rate:** **11/16** finished cells
- **Independent second verifier (`verify2.py`):** **11/11** passing cells dual-verified
- **Real-silicon native harness:** **11/11** passing cells executed and passed on matching hardware
- **Total rounds / API spend:** 52 rounds, **$15.37** USD

## Cell-by-Cell Outcomes

Each row reports one cold-room cell: verdict, rounds used, API cost, compiled code size, `verify2.py` status, and real-silicon test result.

| Task | Model | Target | Verdict | Rounds | Cost (USD) | Code | `verify2.py` | Native CPU |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `ct_lt` | `anthropic/claude-fable-5.2` | `arm64` | PASS (R1) | 1 | $0.16 | 1 fns / 18 insns / 72 B | shown | NATIVE_PASS 9/9 |
| `ct_lt` | `anthropic/claude-fable-5.2` | `x86_64` | PASS (R1) | 1 | $0.20 | 1 fns / 19 insns / 65 B | shown | NATIVE_PASS 9/9 |
| `ct_lt` | `anthropic/claude-sonnet-5.5` | `arm64` | PASS (R2) | 2 | $0.08 | 1 fns / 19 insns / 76 B | shown | NATIVE_PASS 9/9 |
| `ct_lt` | `anthropic/claude-sonnet-5.5` | `x86_64` | PASS (R1) | 1 | $0.05 | 1 fns / 20 insns / 69 B | shown | NATIVE_PASS 9/9 |
| `ct_lt` | `google/gemini-4-neon` | `arm64` | PASS (R1) | 1 | $0.10 | 1 fns / 17 insns / 68 B | shown | NATIVE_PASS 9/9 |
| `ct_lt` | `google/gemini-4-neon` | `x86_64` | PASS (R1) | 1 | $0.11 | 1 fns / 19 insns / 65 B | shown | NATIVE_PASS 9/9 |
| `ct_lt` | `openai/gpt-6.2-astra-pro` | `arm64` | PASS (R1) | 1 | $0.20 | 1 fns / 17 insns / 68 B | shown | NATIVE_PASS 9/9 |
| `ct_lt` | `openai/gpt-6.2-astra-pro` | `x86_64` | PASS (R1) | 1 | $0.27 | 1 fns / 20 insns / 69 B | shown | NATIVE_PASS 9/9 |
| `ebpf` | `anthropic/claude-fable-5.2` | `arm64` | PASS (R5) | 5 | $3.08 | 6 fns / 198 insns / 832 B | shown | NATIVE_PASS 7/7 |
| `ebpf` | `anthropic/claude-fable-5.2` | `x86_64` | FAIL (arith_need_entail) | 8 | $5.00 | — | — | not_run |
| `ebpf` | `anthropic/claude-sonnet-5.5` | `arm64` | FAIL (kept_reg_refusal) | 8 | $0.86 | — | — | not_run |
| `ebpf` | `anthropic/claude-sonnet-5.5` | `x86_64` | FAIL (prover_timeout_120s) | 7 | $0.84 | — | — | not_run |
| `ebpf` | `google/gemini-4-neon` | `arm64` | FAIL (arith_need_compare) | 6 | $1.16 | — | — | not_run |
| `ebpf` | `google/gemini-4-neon` | `x86_64` | FAIL (output_token_limit) | 4 | $1.12 | — | — | not_run |
| `ebpf` | `openai/gpt-6.2-astra-pro` | `arm64` | PASS (R3) | 3 | $1.23 | 6 fns / 175 insns / 728 B | shown | NATIVE_PASS 7/7 |
| `ebpf` | `openai/gpt-6.2-astra-pro` | `x86_64` | PASS (R2) | 2 | $0.91 | 6 fns / 184 insns / 688 B | shown | NATIVE_PASS 7/7 |

## Failing Round Breakdown

Each row counts failing rounds across all cells by root-cause category.

| Failure category | Failing rounds |
| --- | --- |
| `prover_timeout_120s` | 15 |
| `arith_need_compare` | 8 |
| `output_token_limit` | 7 |
| `arith_need_entail` | 4 |
| `compile_or_parse_error` | 3 |
| `kept_reg_refusal` | 2 |
| `spec_need_open` | 2 |

## Before vs. After Comparison (`suite-v3` -> `suite-v4`)

The first table compares totals over the 8 cells that both runs have (the same task, model and target); each cell was run once in each run, so a difference in one cell may be chance. The second table sets each such cell of the two runs side by side.

| Metric (over the 8 shared cells) | `suite-v3` | `suite-v4` | Delta |
| --- | --- | --- | --- |
| Strict passes | 5/8 | 3/8 | -2 |
| Total rounds | 34 | 43 | +9 |
| Total API spend (USD) | $11.37 | $14.20 | $+2.83 |
| Failing rounds: `arith_need_compare` | 10 | 8 | -2 |
| Failing rounds: `arith_need_entail` | 0 | 4 | +4 |
| Failing rounds: `compile_or_parse_error` | 6 | 2 | -4 |
| Failing rounds: `kept_reg_refusal` | 1 | 2 | +1 |
| Failing rounds: `output_token_limit` | 6 | 7 | +1 |
| Failing rounds: `prover_timeout_120s` | 6 | 15 | +9 |
| Failing rounds: `spec_need_open` | 0 | 2 | +2 |

| Task | Model | Target | `suite-v3` | `suite-v4` |
| --- | --- | --- | --- | --- |
| `ct_lt` | `anthropic/claude-fable-5.2` | `arm64` | — | PASS (R1, $0.16) |
| `ct_lt` | `anthropic/claude-fable-5.2` | `x86_64` | — | PASS (R1, $0.20) |
| `ct_lt` | `anthropic/claude-sonnet-5.5` | `arm64` | — | PASS (R2, $0.08) |
| `ct_lt` | `anthropic/claude-sonnet-5.5` | `x86_64` | — | PASS (R1, $0.05) |
| `ct_lt` | `google/gemini-4-neon` | `arm64` | — | PASS (R1, $0.10) |
| `ct_lt` | `google/gemini-4-neon` | `x86_64` | — | PASS (R1, $0.11) |
| `ct_lt` | `openai/gpt-6.2-astra-pro` | `arm64` | — | PASS (R1, $0.20) |
| `ct_lt` | `openai/gpt-6.2-astra-pro` | `x86_64` | — | PASS (R1, $0.27) |
| `ebpf` | `anthropic/claude-fable-5.2` | `arm64` | PASS (R1, $0.99) | PASS (R5, $3.08) |
| `ebpf` | `anthropic/claude-fable-5.2` | `x86_64` | PASS (R1, $0.94) | FAIL ($5.00) |
| `ebpf` | `anthropic/claude-sonnet-5.5` | `arm64` | FAIL ($0.98) | FAIL ($0.86) |
| `ebpf` | `anthropic/claude-sonnet-5.5` | `x86_64` | FAIL ($1.02) | FAIL ($0.84) |
| `ebpf` | `google/gemini-4-neon` | `arm64` | FAIL ($3.96) | FAIL ($1.16) |
| `ebpf` | `google/gemini-4-neon` | `x86_64` | PASS (R5, $2.13) | FAIL ($1.12) |
| `ebpf` | `openai/gpt-6.2-astra-pro` | `arm64` | PASS (R2, $0.78) | PASS (R3, $1.23) |
| `ebpf` | `openai/gpt-6.2-astra-pro` | `x86_64` | PASS (R1, $0.57) | PASS (R2, $0.91) |

## Notes written after the run

1. **`ct_lt` (unseen constant-time big-endian `<`) passed 8/8 cells** (7/8 on Round 1, 1/8 on Round 2, $1.17 total), with 8/8 passing both Lean `odeverify` and independent `verify2.py` and 8/8 passing all 9 native hardware vectors (including 32-byte Curve25519 prime boundaries) on x86-64 Linux and Apple M6. `ct_lt` has zero overlap with `docs/QUICKSTART.md`.
2. **Lowering `--max-tokens` from 32,000 (`suite-v3`) to 16,000 (`suite-v4`) hurt `ebpf` Round 1.** All four `claude-fable-5.2` and `gemini-4-neon` `ebpf` cells hit `output_token_limit` at 16,000 tokens on Round 1 (whereas `claude-fable-5.2` passed both targets on Round 1 at 32,000 tokens in `suite-v3`). Future runs should keep `--max-tokens 24000`–`32000` paired with the new `--max-truncations 2` and `--cell-timeout 900` caps, which already cut total suite wall-clock time from ~35 minutes to 16.5 minutes.
3. **Diagnostics improved concrete feedback, and no cell used mid-function join points.** `compile_or_parse_error` on `ebpf` fell from 6 to 2 rounds, and every proof failure printed source-line attribution, byte/u32 bounds on anonymous variables, and matching specification comparisons (`claude-sonnet-5.5` arm64 progressed past `arith_need_compare` to a single remaining `x15` preservation check by Round 8). No model emitted a mid-function `place` join point (without `decreases`) on `ebpf` in this run.
4. **All 11/11 passing bundles dual-verified in `verify2.py` and passed native execution** on matching x86-64 Linux and Apple M6 hardware.

