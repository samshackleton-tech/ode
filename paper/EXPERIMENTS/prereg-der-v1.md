# Pre-Registration: Cold-Room Suite `der-v1`

Committed before any task API call begins.

## Frozen Configuration

- **Run ID:** `der-v1`
- **UTC timestamp:** `2026-11-26T06:39:28Z`
- **Repository commit (HEAD before pre-registration):** `bf49b6fe2afd2fb3b0aa827f5f0d545c5c72e812`
- **Tasks:** `der_valid`
- **Models (7):** `openai/gpt-6.2-astra-pro`, `anthropic/claude-fable-5.2`, `google/gemini-4-neon`, `anthropic/claude-sonnet-5.5`, `anthropic/claude-haiku-5.5`, `qwen/qwen3.8-2.4t-a95b`, `moonshotai/kimi-k3.1-pro`
- **Targets (2):** `x86_64`, `arm64`
- **Experimental arms:** `default`
- **Total cells:** 14
- **Budget cap:** max `8` rounds per cell, `45s` tool timeout, `540s` wall-clock cap per cell, early stop after `2` consecutive `output_token_limit` replies, `10` concurrent local prover slots, temperature `0.2`, reasoning effort `medium`, max_tokens `32000`, cumulative suite cap `$50.00`.

## Frozen Input BLAKE3-256 Hashes

The table below lists the full 64-hex BLAKE3-256 hash of every frozen prompt input and verifier artifact.

| Artifact | BLAKE3-256 (64 hex) |
| --- | --- |
| `arm64/arm64.tab` | `adaa95953e3526fa7e2ffcadf55b4aaebfd3417b2e9cba26f6a433d2c1c521c6` |
| `core/x86.tab` | `e9ff8cc0b3467375e7935569b469474e04cdd91a15bfb02556a7a959e4d38d73` |
| `docs/QUICKSTART.md` | `5037f8ed720737950363a2815140b17b14fcec2099b46a2a8501e0fc30cfffeb` |
| `paper/EXPERIMENTS/run_suite.py` | `8013657dbbf35fe4130c455b7c25c0e0bead39eb7bb562aba467bf612d010891` |
| `paper/EXPERIMENTS/tasks/der_valid_native.c` | `9b09fc02503bcbeda516e48eac3f39401205c299dbad44339707c9ba3b07f667` |
| `paper/EXPERIMENTS/tasks/der_valid_spec.ode` | `9b712495e0104aa09f4e64b8c23ee5c366fa51bc5b7941b574e5abc002b20ce9` |
| `proof-core/.lake/build/bin/odeverify` | `f028cb223488b94502093f9c085d2f4d7b9433e96d21312c7b630259815e36b9` |
| `proof-core/verify2.py` | `95d979c41514a097c5ed6c08c30813089b512b47743ac12c53237cecdc1f2b01` |

## Expected Canonical Contract IDs

The table below lists each task's required 52-character base-32 contract identifier.

| Task | Entry function | Expected contract ID |
| --- | --- | --- |
| `der_valid` | `der_valid` | `pyqksm2d6u3quuwvpwjwr4j4kgmgy7zlqjixoqobp2gr24sggfma` |

## Strict Pass Criteria

A cell counts as a **strict pass** if and only if, within the round limit and with no manual intervention:
1. `ode pack` produces an ELF64 object file and `.proof` file matching the task's exact expected contract ID.
2. `ode audit --expect-contract <ID>` returns `VERDICT: shown` with 100% executable coverage and 0 hooks.
3. Secondary automated checks recorded on every passing cell: independent pure-Python second verifier (`proof-core/verify2.py`) and real-silicon native execution against the task harness.
