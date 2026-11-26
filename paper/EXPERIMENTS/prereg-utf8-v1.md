# Pre-Registration: Cold-Room Suite `utf8-v1`

Committed before any task API call begins.

## Frozen Configuration

- **Run ID:** `utf8-v1`
- **UTC timestamp:** `2026-11-26T14:01:18Z`
- **Repository commit (HEAD before pre-registration):** `33a0fff929b8e16f301cbb40df4294b484db29e3`
- **Tasks:** `utf8_valid`
- **Models (7):** `openai/gpt-6.2-astra-pro`, `anthropic/claude-fable-5.2`, `google/gemini-4-neon`, `anthropic/claude-sonnet-5.5`, `anthropic/claude-haiku-5.5`, `qwen/qwen3.8-2.4t-a95b`, `moonshotai/kimi-k3.1-pro`
- **Targets (2):** `x86_64`, `arm64`
- **Experimental arms:** `blind`, `advised` (`--opt-rounds 3` after first pass)
- **Total cells:** 28
- **Budget cap:** max `8` rounds per cell, `45s` tool timeout, `600s` wall-clock cap per cell, early stop after `2` consecutive `output_token_limit` replies, `10` concurrent local prover slots, temperature `0.2`, reasoning effort `medium`, max_tokens `32000`, cumulative suite cap `$60.00`.

## Frozen Input BLAKE3-256 Hashes

The table below lists the full 64-hex BLAKE3-256 hash of every frozen prompt input and verifier artifact.

| Artifact | BLAKE3-256 (64 hex) |
| --- | --- |
| `arm64/arm64.tab` | `93cfb4c85ff2b3076017f11e4ebee0e0d715663056fa91ad07d3ec7d2409f6aa` |
| `core/x86.tab` | `1d3ba333dabca7c705da03e59320e3bf69335ee1ab082f9fab54ec3c8dea8fb2` |
| `docs/QUICKSTART.md` | `d6472bd4e0915f3211ff2c953945ddc13c0475a54850fcdb3987da902313e05b` |
| `paper/EXPERIMENTS/run_suite.py` | `7c40bbd48f663de05c1fb64e90dc0ecc54d63db2a4394ec31afb28feca325f31` |
| `paper/EXPERIMENTS/tasks/utf8_valid_native.c` | `fbdaec3406fd4c3e989ce61162452f059352ac22b8ccbc3bb393308fc8e02ed3` |
| `paper/EXPERIMENTS/tasks/utf8_valid_spec.ode` | `2680bccdf2434a2439326cc18d825ac01a7463ef78585d5ce140c379d5ad082a` |
| `proof-core/.lake/build/bin/odeverify` | `e3b467f34a7c615c16026e303e1d0ce6727cc5c7baf17025fa01c2bdce974498` |
| `proof-core/verify2.py` | `35dba8f3c7c16af007b6a2db2a7a3013773174ae15d50c2966d19e715ecc4c75` |

## Expected Canonical Contract IDs

The table below lists each task's required 52-character base-32 contract identifier.

| Task | Entry function | Expected contract ID |
| --- | --- | --- |
| `utf8_valid` | `utf8_valid` | `ykps3cug73fjveiyq2i3t55756kxodpe5l6x4gexcdnvjmyhcrna` |

## Strict Pass Criteria

A cell counts as a **strict pass** if and only if, within the round limit and with no manual intervention:
1. `ode pack` produces an ELF64 object file and `.proof` file matching the task's exact expected contract ID.
2. `ode audit --expect-contract <ID>` returns `VERDICT: shown` with 100% executable coverage and 0 hooks.
3. Secondary automated checks recorded on every passing cell: independent pure-Python second verifier (`proof-core/verify2.py`) and real-silicon native execution against the task harness.
