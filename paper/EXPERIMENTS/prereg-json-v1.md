# Pre-Registration: Cold-Room Suite `json-v1`

Committed before any task API call begins.

## Frozen Configuration

- **Run ID:** `json-v1`
- **UTC timestamp:** `2026-11-26T12:35:34Z`
- **Repository commit (HEAD before pre-registration):** `1c4fa7dac2930ef22b1873e466c3a4af621739e8`
- **Tasks:** `json_str_valid`
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
| `docs/QUICKSTART.md` | `676026309e3c1452f3f86329a2417620a6d45bec31230fd91667bee010721574` |
| `paper/EXPERIMENTS/run_suite.py` | `c76abad012fefb5c9c39fda61261d42a64db86cbdb866c720857c78e7d588d87` |
| `paper/EXPERIMENTS/tasks/json_str_valid_native.c` | `88b7b790a0e03ca35daa33dee794521bc2fc3622238de886c7b4bb0c5c4604d8` |
| `paper/EXPERIMENTS/tasks/json_str_valid_spec.ode` | `ebf52f0293bf0cf02baddf0b47338435d333e7cbdf24c06a8a774e9b3eda1b26` |
| `proof-core/.lake/build/bin/odeverify` | `eddc07b283790b95ec5ad76aa7a81cbabb7a8350f625dc39f51defd69280b40a` |
| `proof-core/verify2.py` | `350c9cffb4833824f606591ef515b6e403449434b4dce6debdbf2b51a5fd4df4` |

## Expected Canonical Contract IDs

The table below lists each task's required 52-character base-32 contract identifier.

| Task | Entry function | Expected contract ID |
| --- | --- | --- |
| `json_str_valid` | `json_str_valid` | `4totxwdumkxnrfw5zgsfvw54fmy24uvfzvgtjkvn2u77hkoetyma` |

## Strict Pass Criteria

A cell counts as a **strict pass** if and only if, within the round limit and with no manual intervention:
1. `ode pack` produces an ELF64 object file and `.proof` file matching the task's exact expected contract ID.
2. `ode audit --expect-contract <ID>` returns `VERDICT: shown` with 100% executable coverage and 0 hooks.
3. Secondary automated checks recorded on every passing cell: independent pure-Python second verifier (`proof-core/verify2.py`) and real-silicon native execution against the task harness.
