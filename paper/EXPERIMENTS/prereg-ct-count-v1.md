# Pre-Registration: Cold-Room Suite `ct-count-v1`

Committed before any task API call begins.

## Frozen Configuration

- **Run ID:** `ct-count-v1`
- **UTC timestamp:** `2026-11-25T21:59:19Z`
- **Repository commit (HEAD before pre-registration):** `8598b4b345de1516bdb1f88022c83e56b14beb3e`
- **Tasks:** `ct_count`
- **Models (4):** `openai/gpt-6.2-astra-pro`, `anthropic/claude-fable-5.2`, `google/gemini-4-neon`, `anthropic/claude-sonnet-5.5`
- **Targets (2):** `x86_64`, `arm64`
- **Total cells:** 8
- **Budget cap:** max `8` rounds per cell, `120s` tool timeout, temperature `0.2`, reasoning effort `medium`, max_tokens `32000`, cumulative suite cap `$15.00`.

## Frozen Input BLAKE3-256 Hashes

The table below lists the full 64-hex BLAKE3-256 hash of every frozen prompt input and verifier artifact.

| Artifact | BLAKE3-256 (64 hex) |
| --- | --- |
| `arm64/arm64.tab` | `adaa95953e3526fa7e2ffcadf55b4aaebfd3417b2e9cba26f6a433d2c1c521c6` |
| `core/x86.tab` | `e9ff8cc0b3467375e7935569b469474e04cdd91a15bfb02556a7a959e4d38d73` |
| `docs/QUICKSTART.md` | `78dfb7aa10f3e96807bba0811c5a1e5fe148aaf1e0f712426b5a183ce80cfcf5` |
| `paper/EXPERIMENTS/run_suite.py` | `a1d83e2a572ca4e5569d73e63c316147470f4abc10e7b434b5fabc810a899407` |
| `paper/EXPERIMENTS/tasks/ct_count_native.c` | `118a14c985137d9531316e670e97c06c5316ac03764522ae3606e649eb9bda19` |
| `paper/EXPERIMENTS/tasks/ct_count_spec.ode` | `e359bf603529176328f6ed1fd6c66bca0a9832269aad9c61e4f0404127128186` |
| `proof-core/.lake/build/bin/odeverify` | `b95ed4a5fffee725ff55ee8d054f28084128c6a87d9b1d59086ab7e36490a231` |
| `proof-core/verify2.py` | `7cdea62c792c16853f3cc06dd562aab77581a55417d0f114e58cf6c95f25430e` |

## Expected Canonical Contract IDs

The table below lists each task's required 52-character base-32 contract identifier.

| Task | Entry function | Expected contract ID |
| --- | --- | --- |
| `ct_count` | `ct_count_diff` | `hbdtlkirrxt4sxhwsvqn3rmrrqxxfx3rpu4iebfgdgb3my2cr7ma` |

## Strict Pass Criteria

A cell counts as a **strict pass** if and only if, within the round limit and with no manual intervention:
1. `ode pack` produces an ELF64 object file and `.proof` file matching the task's exact expected contract ID.
2. `ode audit --expect-contract <ID>` returns `VERDICT: shown` with 100% executable coverage and 0 hooks.
3. Secondary automated checks recorded on every passing cell: independent pure-Python second verifier (`proof-core/verify2.py`) and real-silicon native execution against the task harness.
