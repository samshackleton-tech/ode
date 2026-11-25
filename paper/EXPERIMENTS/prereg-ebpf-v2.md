# Pre-Registration: Cold-Room Suite `ebpf-v2`

Committed before any task API call begins.

## Frozen Configuration

- **Run ID:** `ebpf-v2`
- **UTC timestamp:** `2026-11-25T20:35:05Z`
- **Repository commit (HEAD before pre-registration):** `cb2355ae97f9fb50bf5a4f2644cc2b678d92b515`
- **Tasks:** `ebpf`
- **Models (4):** `openai/gpt-6.2-astra-pro`, `anthropic/claude-fable-5.2`, `google/gemini-4-neon`, `anthropic/claude-sonnet-5.5`
- **Targets (2):** `x86_64`, `arm64`
- **Total cells:** 8
- **Budget cap:** max `8` rounds per cell, `120s` tool timeout, temperature `0.2`, reasoning effort `medium`, max_tokens `16000`, cumulative suite cap `$35.00`.

## Frozen Input BLAKE3-256 Hashes

The table below lists the full 64-hex BLAKE3-256 hash of every frozen prompt input and verifier artifact.

| Artifact | BLAKE3-256 (64 hex) |
| --- | --- |
| `arm64/arm64.tab` | `adaa95953e3526fa7e2ffcadf55b4aaebfd3417b2e9cba26f6a433d2c1c521c6` |
| `core/x86.tab` | `e9ff8cc0b3467375e7935569b469474e04cdd91a15bfb02556a7a959e4d38d73` |
| `docs/QUICKSTART.md` | `78dfb7aa10f3e96807bba0811c5a1e5fe148aaf1e0f712426b5a183ce80cfcf5` |
| `paper/EXPERIMENTS/run_suite.py` | `6df9c92f7016c147695c38b2b331b4357c3083eaa62a6adcb230126088c71037` |
| `paper/EXPERIMENTS/tasks/ebpf_native.c` | `a1328ffc5960168fbe997b957c23c7e989c82958b6ff73d40d93e780a3b905e5` |
| `proof-core/.lake/build/bin/odeverify` | `b95ed4a5fffee725ff55ee8d054f28084128c6a87d9b1d59086ab7e36490a231` |
| `proof-core/examples/ebpf/ebpf_spec.ode` | `b13cc432c3cb48a1c88bea3b2a91eb9ca389a38b74a5d1ca971d3ec88b870b87` |
| `proof-core/verify2.py` | `f24325037687445469d53dcac70549eb4de3f79e2fd92164d7e2140cb4eac332` |

## Expected Canonical Contract IDs

The table below lists each task's required 52-character base-32 contract identifier.

| Task | Entry function | Expected contract ID |
| --- | --- | --- |
| `ebpf` | `ebpf_run` | `d7b6z5hr3w25whmsn56nvv3qcsq5ugtcxifauztdznaekaiiahfa` |

## Strict Pass Criteria

A cell counts as a **strict pass** if and only if, within the round limit and with no manual intervention:
1. `ode pack` produces an ELF64 object file and `.proof` file matching the task's exact expected contract ID.
2. `ode audit --expect-contract <ID>` returns `VERDICT: shown` with 100% executable coverage and 0 hooks.
3. Secondary automated checks recorded on every passing cell: independent pure-Python second verifier (`proof-core/verify2.py`) and real-silicon native execution against the task harness.

## Status Note

Aborted ~90 seconds after launch ($1.60 spent) due to a harness CLI bug (`run_suite.py` passed `-o` instead of `--out` to `ode_tool.py pack`, so no candidate source reached the compiler or verifier). Fixed `run_suite.py` with a local pre-API CLI self-test (`self_test_cli`) and superseded by `ebpf-v2b`.
