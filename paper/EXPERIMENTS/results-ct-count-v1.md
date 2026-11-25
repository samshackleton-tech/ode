# Results: Pre-Registered Cold-Room Suite `ct-count-v1`

- **Pre-registration commit:** `d30277258155ee0596437463c5e4887b340f0154`
- **Finished (UTC):** `2026-11-25T22:00:01Z`
- **Strict pass rate:** **8/8** cells
- **Independent second verifier (`verify2.py`):** **4/8** passing cells dual-verified
- **Real-silicon native harness:** **8/8** passing cells executed and passed on matching hardware
- **Total rounds / API spend:** 8 rounds, **$1.05** USD

## Cell-by-Cell Outcomes

Each row reports one cold-room cell: verdict, rounds used, API cost, compiled code size, `verify2.py` status, and real-silicon test result.

| Task | Model | Target | Verdict | Rounds | Cost (USD) | Code | `verify2.py` | Native CPU |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `ct_count` | `anthropic/claude-fable-5.2` | `arm64` | PASS (R1) | 1 | $0.15 | 1 fns / 19 insns / 76 B | refused | NATIVE_PASS 6/6 |
| `ct_count` | `anthropic/claude-fable-5.2` | `x86_64` | PASS (R1) | 1 | $0.19 | 1 fns / 19 insns / 77 B | shown | NATIVE_PASS 6/6 |
| `ct_count` | `anthropic/claude-sonnet-5.5` | `arm64` | PASS (R1) | 1 | $0.04 | 1 fns / 19 insns / 76 B | refused | NATIVE_PASS 6/6 |
| `ct_count` | `anthropic/claude-sonnet-5.5` | `x86_64` | PASS (R1) | 1 | $0.05 | 1 fns / 19 insns / 77 B | shown | NATIVE_PASS 6/6 |
| `ct_count` | `google/gemini-4-neon` | `arm64` | PASS (R1) | 1 | $0.07 | 1 fns / 19 insns / 76 B | refused | NATIVE_PASS 6/6 |
| `ct_count` | `google/gemini-4-neon` | `x86_64` | PASS (R1) | 1 | $0.09 | 1 fns / 19 insns / 77 B | shown | NATIVE_PASS 6/6 |
| `ct_count` | `openai/gpt-6.2-astra-pro` | `arm64` | PASS (R1) | 1 | $0.19 | 1 fns / 19 insns / 76 B | refused | NATIVE_PASS 6/6 |
| `ct_count` | `openai/gpt-6.2-astra-pro` | `x86_64` | PASS (R1) | 1 | $0.26 | 1 fns / 19 insns / 77 B | shown | NATIVE_PASS 6/6 |

## Failing Round Breakdown

Each row counts failing rounds across all cells by root-cause category.

| Failure category | Failing rounds |
| --- | --- |
| *(none)* | 0 |

## Note written after the run

What this run tests is narrower than its name. The Quickstart that every model is given holds a complete worked example of a neighbouring function (byte-slice equality with a trace that depends on the length alone, with its loop invariant). To pass here a model has to adapt that example: another specification, another invariant (`c <= i`), a bound on `n`, another returned value. It does not have to find the method. The second verifier `verify2.py` refuses the AArch64 proofs of this task, as it refuses the reference solution's; the Lean verifier shows them.
