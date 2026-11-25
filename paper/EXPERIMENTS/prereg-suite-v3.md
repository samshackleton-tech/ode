# Pre-Registration: Cold-Room Suite `suite-v3`

Committed before any task API call begins.

## Frozen Configuration

- **Run ID:** `suite-v3`
- **UTC timestamp:** `2026-11-25T21:41:05Z`
- **Repository commit (HEAD before pre-registration):** `bb41fb356ce27d1c9411664f0f6db9d89b9da16e`
- **Tasks:** `ebpf`, `ct_eq`
- **Models (4):** `openai/gpt-6.2-astra-pro`, `anthropic/claude-fable-5.2`, `google/gemini-4-neon`, `anthropic/claude-sonnet-5.5`
- **Targets (2):** `x86_64`, `arm64`
- **Total cells:** 16
- **Budget cap:** max `8` rounds per cell, `120s` tool timeout, temperature `0.2`, reasoning effort `medium`, max_tokens `32000`, cumulative suite cap `$40.00`.

## Frozen Input BLAKE3-256 Hashes

The table below lists the full 64-hex BLAKE3-256 hash of every frozen prompt input and verifier artifact.

| Artifact | BLAKE3-256 (64 hex) |
| --- | --- |
| `arm64/arm64.tab` | `adaa95953e3526fa7e2ffcadf55b4aaebfd3417b2e9cba26f6a433d2c1c521c6` |
| `core/x86.tab` | `e9ff8cc0b3467375e7935569b469474e04cdd91a15bfb02556a7a959e4d38d73` |
| `docs/QUICKSTART.md` | `78dfb7aa10f3e96807bba0811c5a1e5fe148aaf1e0f712426b5a183ce80cfcf5` |
| `paper/EXPERIMENTS/run_suite.py` | `a1d83e2a572ca4e5569d73e63c316147470f4abc10e7b434b5fabc810a899407` |
| `paper/EXPERIMENTS/tasks/ct_eq_native.c` | `fd8aee7fdaf1f692773ee60de6eb95261e059ad2d49f3426e69529b2a4d3e406` |
| `paper/EXPERIMENTS/tasks/ebpf_native.c` | `a1328ffc5960168fbe997b957c23c7e989c82958b6ff73d40d93e780a3b905e5` |
| `proof-core/.lake/build/bin/odeverify` | `b95ed4a5fffee725ff55ee8d054f28084128c6a87d9b1d59086ab7e36490a231` |
| `proof-core/examples/ebpf/ebpf_spec.ode` | `b13cc432c3cb48a1c88bea3b2a91eb9ca389a38b74a5d1ca971d3ec88b870b87` |
| `proof-core/examples/hasher/hash_eq_ct_spec.ode` | `c1e92d70614e0e267e0071085d4704ca1ec24b267140244e0dc5860f520fc3c7` |
| `proof-core/verify2.py` | `7cdea62c792c16853f3cc06dd562aab77581a55417d0f114e58cf6c95f25430e` |

## Expected Canonical Contract IDs

The table below lists each task's required 52-character base-32 contract identifier.

| Task | Entry function | Expected contract ID |
| --- | --- | --- |
| `ebpf` | `ebpf_run` | `d7b6z5hr3w25whmsn56nvv3qcsq5ugtcxifauztdznaekaiiahfa` |
| `ct_eq` | `ct_bytes_eq` | `rpxfmeixumkaoep4wemhcysirkt7uciujxzihzc4m6obijc7bvmq` |

## Strict Pass Criteria

A cell counts as a **strict pass** if and only if, within the round limit and with no manual intervention:
1. `ode pack` produces an ELF64 object file and `.proof` file matching the task's exact expected contract ID.
2. `ode audit --expect-contract <ID>` returns `VERDICT: shown` with 100% executable coverage and 0 hooks.
3. Secondary automated checks recorded on every passing cell: independent pure-Python second verifier (`proof-core/verify2.py`) and real-silicon native execution against the task harness.
