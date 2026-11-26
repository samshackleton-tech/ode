# Pre-Registration: Cold-Room Suite `der-v2`

Committed before any task API call begins.

## Frozen Configuration

- **Run ID:** `der-v2`
- **UTC timestamp:** `2026-11-26T07:19:45Z`
- **Repository commit (HEAD before pre-registration):** `5b60b9235e7d55e4336c94cda3f15dd45ca50c38`
- **Tasks:** `der_valid`
- **Models (7):** `openai/gpt-6.2-astra-pro`, `anthropic/claude-fable-5.2`, `google/gemini-4-neon`, `anthropic/claude-sonnet-5.5`, `anthropic/claude-haiku-5.5`, `qwen/qwen3.8-2.4t-a95b`, `moonshotai/kimi-k3.1-pro`
- **Targets (2):** `x86_64`, `arm64`
- **Experimental arms:** `default`
- **Total cells:** 14
- **Budget cap:** max `8` rounds per cell, `45s` tool timeout, `720s` wall-clock cap per cell, early stop after `2` consecutive `output_token_limit` replies, `10` concurrent local prover slots, temperature `0.2`, reasoning effort `medium`, max_tokens `32000`, cumulative suite cap `$50.00`.

## Frozen Input BLAKE3-256 Hashes

The table below lists the full 64-hex BLAKE3-256 hash of every frozen prompt input and verifier artifact.

| Artifact | BLAKE3-256 (64 hex) |
| --- | --- |
| `arm64/arm64.tab` | `0b765d6f661c7ea6f90e58bcc26855692a5ac17d580e786406ce2274befc88da` |
| `core/x86.tab` | `c98e5b6a30dc2b05b5f736dba4b1f966840c9c4795a56eb3e272b0057a3a7740` |
| `docs/QUICKSTART.md` | `5037f8ed720737950363a2815140b17b14fcec2099b46a2a8501e0fc30cfffeb` |
| `paper/EXPERIMENTS/run_suite.py` | `40608ffdf96d6ce4eb04f0cbb89ae2c1fd6ee94af340e0540e3f72cee5dcd015` |
| `paper/EXPERIMENTS/tasks/der_valid_native.c` | `9b09fc02503bcbeda516e48eac3f39401205c299dbad44339707c9ba3b07f667` |
| `paper/EXPERIMENTS/tasks/der_valid_spec.ode` | `9b712495e0104aa09f4e64b8c23ee5c366fa51bc5b7941b574e5abc002b20ce9` |
| `proof-core/.lake/build/bin/odeverify` | `ea56486970a7ae5f38f23b2571bfa0e402f036d963044fa0f4690f366854096f` |
| `proof-core/verify2.py` | `6f149adf9edfa32b80572a233d3e9db8970ea60f8938973ae244c8630587ad99` |

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
