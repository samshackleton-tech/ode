# Pre-Registration: Cold-Room Suite `ipv4-v1`

Committed before any task API call begins.

## Frozen Configuration

- **Run ID:** `ipv4-v1`
- **UTC timestamp:** `2026-11-26T13:06:25Z`
- **Repository commit (HEAD before pre-registration):** `435c40d14b2513c15d802529b9b4a1dae2e5a7da`
- **Tasks:** `ipv4_valid`
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
| `paper/EXPERIMENTS/run_suite.py` | `d8ea992b1a19e133b37fdfc04623dad595a96fcce00853df06d977ff579b82e2` |
| `paper/EXPERIMENTS/tasks/ipv4_valid_native.c` | `5396d6de3cfd761f95e34ba2cf60c0f55b701a0d181c0d2072f1925b8728577f` |
| `paper/EXPERIMENTS/tasks/ipv4_valid_spec.ode` | `ac3a8c96246621431ed85c6d8c79c0f8f2e62558f25edf9de3947fd5b3c55a9a` |
| `proof-core/.lake/build/bin/odeverify` | `933c451093f53648a8c4a6ce4269d41cd1562356450fa1ba36e86acd747abb9a` |
| `proof-core/verify2.py` | `e8f20343d9ce301eaeed6f67b5c958e7cb35a6604ce736b3d3fbd1c71e8daf0d` |

## Expected Canonical Contract IDs

The table below lists each task's required 52-character base-32 contract identifier.

| Task | Entry function | Expected contract ID |
| --- | --- | --- |
| `ipv4_valid` | `ipv4_valid` | `hh2id4zrh6vshq5hjpeuu53hlzy3x4uqhnnvuctrsk6hlfzseysa` |

## Strict Pass Criteria

A cell counts as a **strict pass** if and only if, within the round limit and with no manual intervention:
1. `ode pack` produces an ELF64 object file and `.proof` file matching the task's exact expected contract ID.
2. `ode audit --expect-contract <ID>` returns `VERDICT: shown` with 100% executable coverage and 0 hooks.
3. Secondary automated checks recorded on every passing cell: independent pure-Python second verifier (`proof-core/verify2.py`) and real-silicon native execution against the task harness.
