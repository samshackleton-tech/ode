# Pre-Registration: Cold-Room Suite `suite-v5`

Committed before any task API call begins.

## Frozen Configuration

- **Run ID:** `suite-v5`
- **UTC timestamp:** `2026-11-26T02:33:18Z`
- **Repository commit (HEAD before pre-registration):** `128043c733adebea90c6b0f957b0de7826a802e4`
- **Tasks:** `header_score`, `ebpf`
- **Models (4):** `openai/gpt-6.2-astra-pro`, `anthropic/claude-fable-5.2`, `google/gemini-4-neon`, `anthropic/claude-sonnet-5.5`
- **Targets (2):** `x86_64`, `arm64`
- **Total cells:** 16
- **Budget cap:** max `8` rounds per cell, `120s` tool timeout, `900s` wall-clock cap per cell, early stop after `2` consecutive `output_token_limit` replies, `6` concurrent local prover slots, temperature `0.2`, reasoning effort `medium`, max_tokens `32000`, cumulative suite cap `$35.00`.

## Frozen Input BLAKE3-256 Hashes

The table below lists the full 64-hex BLAKE3-256 hash of every frozen prompt input and verifier artifact.

| Artifact | BLAKE3-256 (64 hex) |
| --- | --- |
| `arm64/arm64.tab` | `adaa95953e3526fa7e2ffcadf55b4aaebfd3417b2e9cba26f6a433d2c1c521c6` |
| `core/x86.tab` | `e9ff8cc0b3467375e7935569b469474e04cdd91a15bfb02556a7a959e4d38d73` |
| `docs/QUICKSTART.md` | `4e52bb24799943ad217f0c1c8e638c16c9359ae38fa4fec941692f66b44efd75` |
| `paper/EXPERIMENTS/run_suite.py` | `500295257f3840e4e05b6d038c6d84729fa2cd7a337813c764aaf3c75e6c366e` |
| `paper/EXPERIMENTS/tasks/ebpf_native.c` | `a1328ffc5960168fbe997b957c23c7e989c82958b6ff73d40d93e780a3b905e5` |
| `paper/EXPERIMENTS/tasks/header_score_native.c` | `c5b0212b9feb3e9fc0878e8a4152720d7a7fda96c72a33f60b61bfba32dbd22a` |
| `paper/EXPERIMENTS/tasks/header_score_spec.ode` | `0ba9181aef9472ba5a1916e55b5838d232cb6eadd4ab09c30b0e230042d205f7` |
| `proof-core/.lake/build/bin/odeverify` | `f028cb223488b94502093f9c085d2f4d7b9433e96d21312c7b630259815e36b9` |
| `proof-core/examples/ebpf/ebpf_spec.ode` | `b13cc432c3cb48a1c88bea3b2a91eb9ca389a38b74a5d1ca971d3ec88b870b87` |
| `proof-core/verify2.py` | `f975e2c37e99158d0bc9572836f8cbb844b2c21728d76029b55b66768f7ee103` |

## Expected Canonical Contract IDs

The table below lists each task's required 52-character base-32 contract identifier.

| Task | Entry function | Expected contract ID |
| --- | --- | --- |
| `header_score` | `header_score` | `hrslejxv4lnql6e53janwkl7tjtgn7oydsuja33hgvgktnbwwehq` |
| `ebpf` | `ebpf_run` | `d7b6z5hr3w25whmsn56nvv3qcsq5ugtcxifauztdznaekaiiahfa` |

## Strict Pass Criteria

A cell counts as a **strict pass** if and only if, within the round limit and with no manual intervention:
1. `ode pack` produces an ELF64 object file and `.proof` file matching the task's exact expected contract ID.
2. `ode audit --expect-contract <ID>` returns `VERDICT: shown` with 100% executable coverage and 0 hooks.
3. Secondary automated checks recorded on every passing cell: independent pure-Python second verifier (`proof-core/verify2.py`) and real-silicon native execution against the task harness.
