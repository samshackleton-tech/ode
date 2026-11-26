# Pre-Registration: Cold-Room Suite `ct-b64-v2`

Committed before any task API call begins.

## Frozen Configuration

- **Run ID:** `ct-b64-v2`
- **UTC timestamp:** `2026-11-26T12:07:17Z`
- **Repository commit (HEAD before pre-registration):** `52cc661e34ad281ac647482be4e803a1f622dcf2`
- **Tasks:** `ct_base64_decode`
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
| `paper/EXPERIMENTS/run_suite.py` | `4137879c34f4af7a1c6c3687d9a35e87d7c79bd644cc82bf997ebe8c8bee6404` |
| `paper/EXPERIMENTS/tasks/ct_base64_decode_native.c` | `280dd6dffc7b0ffedfdc2ddeabf8d576dfbb54583d5c83c8d7b120f43e431734` |
| `paper/EXPERIMENTS/tasks/ct_base64_decode_spec.ode` | `8d5fd88d8c83e228b5ce69dcbcafb447f8c794b62e3ec3c9b17acf4773c33355` |
| `proof-core/.lake/build/bin/odeverify` | `eddc07b283790b95ec5ad76aa7a81cbabb7a8350f625dc39f51defd69280b40a` |
| `proof-core/verify2.py` | `4d7bf4231aeb37f619f75225d87a7cd5696b46c55af02764f84ba950835a5a30` |

## Expected Canonical Contract IDs

The table below lists each task's required 52-character base-32 contract identifier.

| Task | Entry function | Expected contract ID |
| --- | --- | --- |
| `ct_base64_decode` | `ct_base64_decode` | `5ibuszg65c23xbxdcscfcsjfpw3w3xju3hi672yvtmecj7y7e2dq` |

## Strict Pass Criteria

A cell counts as a **strict pass** if and only if, within the round limit and with no manual intervention:
1. `ode pack` produces an ELF64 object file and `.proof` file matching the task's exact expected contract ID.
2. `ode audit --expect-contract <ID>` returns `VERDICT: shown` with 100% executable coverage and 0 hooks.
3. Secondary automated checks recorded on every passing cell: independent pure-Python second verifier (`proof-core/verify2.py`) and real-silicon native execution against the task harness.
