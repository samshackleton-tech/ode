# Results: Pre-Registered Cold-Room Suite `suite-v5`

- **Pre-registration commit:** `bc366f10bdd109a3ba9a57150b075b42d0acefa9`
- **Finished (UTC):** `2026-11-26T02:52:22Z`
- **Strict pass rate:** **11/16** finished cells
- **Independent second verifier (`verify2.py`):** **11/11** passing cells dual-verified
- **Real-silicon native harness:** **11/11** passing cells executed and passed on matching hardware
- **Total rounds / API spend:** 54 rounds, **$13.83** USD

## Cell-by-Cell Outcomes

Each row reports one cold-room cell: verdict, rounds used, API cost, compiled code size, `verify2.py` status, and real-silicon test result.

| Task | Model | Target | Verdict | Rounds | Cost (USD) | Code | `verify2.py` | Native CPU |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `ebpf` | `anthropic/claude-fable-5.2` | `arm64` | PASS (R4) | 4 | $2.73 | 6 fns / 220 insns / 932 B | shown | NATIVE_PASS 7/7 |
| `ebpf` | `anthropic/claude-fable-5.2` | `x86_64` | PASS (R1) | 1 | $1.09 | 6 fns / 245 insns / 912 B | shown | NATIVE_PASS 7/7 |
| `ebpf` | `anthropic/claude-sonnet-5.5` | `arm64` | FAIL (arith_need_compare) | 8 | $1.04 | — | — | not_run |
| `ebpf` | `anthropic/claude-sonnet-5.5` | `x86_64` | FAIL (prover_timeout_120s) | 7 | $0.96 | — | — | not_run |
| `ebpf` | `google/gemini-4-neon` | `arm64` | PASS (R4) | 4 | $1.25 | 8 fns / 219 insns / 924 B | shown | NATIVE_PASS 7/7 |
| `ebpf` | `google/gemini-4-neon` | `x86_64` | FAIL (arith_need_compare) | 4 | $1.82 | — | — | not_run |
| `ebpf` | `openai/gpt-6.2-astra-pro` | `arm64` | PASS (R3) | 3 | $1.16 | 6 fns / 172 insns / 720 B | shown | NATIVE_PASS 7/7 |
| `ebpf` | `openai/gpt-6.2-astra-pro` | `x86_64` | PASS (R1) | 1 | $0.52 | 6 fns / 187 insns / 673 B | shown | NATIVE_PASS 7/7 |
| `header_score` | `anthropic/claude-fable-5.2` | `arm64` | PASS (R1) | 1 | $0.24 | 1 fns / 67 insns / 268 B | shown | NATIVE_PASS 1021/1021 |
| `header_score` | `anthropic/claude-fable-5.2` | `x86_64` | PASS (R1) | 1 | $0.28 | 1 fns / 66 insns / 249 B | shown | NATIVE_PASS 1021/1021 |
| `header_score` | `anthropic/claude-sonnet-5.5` | `arm64` | FAIL (arith_need_entail) | 8 | $0.88 | — | — | not_run |
| `header_score` | `anthropic/claude-sonnet-5.5` | `x86_64` | FAIL (other) | 8 | $0.85 | — | — | not_run |
| `header_score` | `google/gemini-4-neon` | `arm64` | PASS (R1) | 1 | $0.15 | 1 fns / 67 insns / 268 B | shown | NATIVE_PASS 1021/1021 |
| `header_score` | `google/gemini-4-neon` | `x86_64` | PASS (R1) | 1 | $0.17 | 1 fns / 66 insns / 249 B | shown | NATIVE_PASS 1021/1021 |
| `header_score` | `openai/gpt-6.2-astra-pro` | `arm64` | PASS (R1) | 1 | $0.31 | 1 fns / 67 insns / 268 B | shown | NATIVE_PASS 1021/1021 |
| `header_score` | `openai/gpt-6.2-astra-pro` | `x86_64` | PASS (R1) | 1 | $0.37 | 1 fns / 66 insns / 249 B | shown | NATIVE_PASS 1021/1021 |

## Failing Round Breakdown

Each row counts failing rounds across all cells by root-cause category.

| Failure category | Failing rounds |
| --- | --- |
| `arith_need_entail` | 15 |
| `arith_need_compare` | 13 |
| `prover_timeout_120s` | 10 |
| `compile_or_parse_error` | 1 |
| `kept_reg_refusal` | 1 |
| `other` | 1 |
| `spec_need_open` | 1 |
| `trace_refusal` | 1 |

## Notes written after the run

- **Acyclic mid-function `place` join points (Task 3A) worked out of the box in cold-room testing:** on the unseen 16-rule `header_score` task (`2^16 = 65,536` paths without join points), all 6 passing cells (`claude-fable-5.2`, `gemini-4-neon`, and `gpt-6.2-astra-pro` on both `x86_64` and `arm64`) used 15–16 acyclic mid-function `place` join points and passed on Round 1 (`$0.15`–`$0.37` per cell, 66 instructions x86-64 / 67 instructions arm64, `verify2.py` shown, `NATIVE_PASS 1021/1021`). Both failing `header_score` cells (`claude-sonnet-5.5`) used 0 join points and failed `arith_need_entail` / `other`.
- **Restoring `--max-tokens 32000` alongside `--max-truncations 2` and `--cell-timeout 900`:** eliminated all `output_token_limit` truncations (0 across 54 rounds, vs. 4 Round-1 truncations at 16,000 tokens in `suite-v4`), lifting `ebpf` back to 5/8 PASS (11/16 overall, $13.83, ~19.5 min wall clock), including `gemini-4-neon`'s first-ever `ebpf` pass on `arm64` (Round 4, 8 functions, 219 instructions, `verify2.py` shown, `NATIVE_PASS 7/7`).
- **Diagnostic and syntax trend:** `compile_or_parse_error` fell to 1/54 rounds (1.9%, down from 17 in `ebpf-v1`, 6 in `suite-v3`, and 2 in `suite-v4`). Note that `prereg-suite-v5.md` was committed on an isolated worktree at `128043c` (`bc366f10`) before the first API call so foreground edits in `advice/` could proceed concurrently without colliding.

