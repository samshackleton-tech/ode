# Pre-Registration: Cold-Room Suite `suite-v4`

Committed before any task API call begins.

## Frozen Configuration

- **Run ID:** `suite-v4`
- **UTC timestamp:** `2026-11-25T23:37:17Z`
- **Repository commit (HEAD before pre-registration):** `b292e79e420b7e8442e7c5f47d3b93f94a609ab1`
- **Tasks:** `ebpf`, `ct_lt`
- **Models (4):** `openai/gpt-6.2-astra-pro`, `anthropic/claude-fable-5.2`, `google/gemini-4-neon`, `anthropic/claude-sonnet-5.5`
- **Targets (2):** `x86_64`, `arm64`
- **Total cells:** 16
- **Budget cap:** max `8` rounds per cell, `120s` tool timeout, `900s` wall-clock cap per cell, early stop after `2` consecutive `output_token_limit` replies, `6` concurrent local prover slots, temperature `0.2`, reasoning effort `medium`, max_tokens `16000`, cumulative suite cap `$30.00`.

## Frozen Input BLAKE3-256 Hashes

The table below lists the full 64-hex BLAKE3-256 hash of every frozen prompt input and verifier artifact.

| Artifact | BLAKE3-256 (64 hex) |
| --- | --- |
| `arm64/arm64.tab` | `adaa95953e3526fa7e2ffcadf55b4aaebfd3417b2e9cba26f6a433d2c1c521c6` |
| `core/x86.tab` | `e9ff8cc0b3467375e7935569b469474e04cdd91a15bfb02556a7a959e4d38d73` |
| `docs/QUICKSTART.md` | `4e52bb24799943ad217f0c1c8e638c16c9359ae38fa4fec941692f66b44efd75` |
| `paper/EXPERIMENTS/run_suite.py` | `500295257f3840e4e05b6d038c6d84729fa2cd7a337813c764aaf3c75e6c366e` |
| `paper/EXPERIMENTS/tasks/ct_lt_native.c` | `e3402b01615ba245e1cd1581db4d881a206eef59ec3bcfcc58cd31d071501c57` |
| `paper/EXPERIMENTS/tasks/ct_lt_spec.ode` | `19a1b5f0d58a2dde825b361740881774c66c1b56281b62c41fd451b1b9dd062a` |
| `paper/EXPERIMENTS/tasks/ebpf_native.c` | `a1328ffc5960168fbe997b957c23c7e989c82958b6ff73d40d93e780a3b905e5` |
| `proof-core/.lake/build/bin/odeverify` | `f028cb223488b94502093f9c085d2f4d7b9433e96d21312c7b630259815e36b9` |
| `proof-core/examples/ebpf/ebpf_spec.ode` | `b13cc432c3cb48a1c88bea3b2a91eb9ca389a38b74a5d1ca971d3ec88b870b87` |
| `proof-core/verify2.py` | `f975e2c37e99158d0bc9572836f8cbb844b2c21728d76029b55b66768f7ee103` |

## Expected Canonical Contract IDs

The table below lists each task's required 52-character base-32 contract identifier.

| Task | Entry function | Expected contract ID |
| --- | --- | --- |
| `ebpf` | `ebpf_run` | `d7b6z5hr3w25whmsn56nvv3qcsq5ugtcxifauztdznaekaiiahfa` |
| `ct_lt` | `ct_bytes_lt` | `z5mi7h56f2qwr2uqti72jtovd26jpjh3e2ue7vw2l5v5vwxudzna` |

## Strict Pass Criteria

A cell counts as a **strict pass** if and only if, within the round limit and with no manual intervention:
1. `ode pack` produces an ELF64 object file and `.proof` file matching the task's exact expected contract ID.
2. `ode audit --expect-contract <ID>` returns `VERDICT: shown` with 100% executable coverage and 0 hooks.
3. Secondary automated checks recorded on every passing cell: independent pure-Python second verifier (`proof-core/verify2.py`) and real-silicon native execution against the task harness.
