# Pre-Registration: Cold-Room Suite `perf-v1`

Committed before any task API call begins.

## Frozen Configuration

- **Run ID:** `perf-v1`
- **UTC timestamp:** `2026-11-26T04:05:58Z`
- **Repository commit (HEAD before pre-registration):** `153a91073daced0faa7b3020823908d3d42bf777`
- **Tasks:** `byte_sum`
- **Models (4):** `openai/gpt-6.2-astra-pro`, `anthropic/claude-fable-5.2`, `google/gemini-4-neon`, `anthropic/claude-sonnet-5.5`
- **Targets (2):** `x86_64`, `arm64`
- **Experimental arms:** `blind`, `advised` (`--opt-rounds 3` after first pass)
- **Total cells:** 16
- **Budget cap:** max `6` rounds per cell, `120s` tool timeout, `900s` wall-clock cap per cell, early stop after `2` consecutive `output_token_limit` replies, `6` concurrent local prover slots, temperature `0.2`, reasoning effort `medium`, max_tokens `32000`, cumulative suite cap `$35.00`.

## Frozen Input BLAKE3-256 Hashes

The table below lists the full 64-hex BLAKE3-256 hash of every frozen prompt input and verifier artifact.

| Artifact | BLAKE3-256 (64 hex) |
| --- | --- |
| `arm64/arm64.tab` | `adaa95953e3526fa7e2ffcadf55b4aaebfd3417b2e9cba26f6a433d2c1c521c6` |
| `core/x86.tab` | `e9ff8cc0b3467375e7935569b469474e04cdd91a15bfb02556a7a959e4d38d73` |
| `docs/QUICKSTART.md` | `2088325772e7e21eaddc6311ada2f46eee8f885386722d189d0b723bcb46692b` |
| `paper/EXPERIMENTS/run_suite.py` | `ba8800888077d6b7685c17e77483a80193376353732851ae7d66bac826694a1a` |
| `paper/EXPERIMENTS/tasks/byte_sum_native.c` | `15faad3b843610569a5984d7231fee4e9e0121c942fb76e0bbe313cc02ff7ec8` |
| `paper/EXPERIMENTS/tasks/byte_sum_spec.ode` | `6f5dcaa274092de31f527310e2ab5d3fa579442dc236a6009a541f3ff5f98e64` |
| `proof-core/.lake/build/bin/odeverify` | `f028cb223488b94502093f9c085d2f4d7b9433e96d21312c7b630259815e36b9` |
| `proof-core/verify2.py` | `f975e2c37e99158d0bc9572836f8cbb844b2c21728d76029b55b66768f7ee103` |

## Expected Canonical Contract IDs

The table below lists each task's required 52-character base-32 contract identifier.

| Task | Entry function | Expected contract ID |
| --- | --- | --- |
| `byte_sum` | `byte_sum` | `4lzcji2jrhepmln3ah4chochys4klbj2cvugbw665estynenutja` |

## Strict Pass Criteria

A cell counts as a **strict pass** if and only if, within the round limit and with no manual intervention:
1. `ode pack` produces an ELF64 object file and `.proof` file matching the task's exact expected contract ID.
2. `ode audit --expect-contract <ID>` returns `VERDICT: shown` with 100% executable coverage and 0 hooks.
3. Secondary automated checks recorded on every passing cell: independent pure-Python second verifier (`proof-core/verify2.py`) and real-silicon native execution against the task harness.
