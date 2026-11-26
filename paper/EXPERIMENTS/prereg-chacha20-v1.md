# Pre-Registration: Cold-Room Suite `chacha20-v1`

Committed before any task API call begins.

## Frozen Configuration

- **Run ID:** `chacha20-v1`
- **UTC timestamp:** `2026-11-26T13:25:53Z`
- **Repository commit (HEAD before pre-registration):** `75cd37e118f6e2a0a248c062b66bbff8ddcc5e47`
- **Tasks:** `chacha20_4way`
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
| `paper/EXPERIMENTS/run_suite.py` | `7c40bbd48f663de05c1fb64e90dc0ecc54d63db2a4394ec31afb28feca325f31` |
| `paper/EXPERIMENTS/tasks/chacha20_4way_native.c` | `1f038baa31df4cf96ad6935a432c47f923d0bbe4a8d5595d5f80b7505ed3c10f` |
| `paper/EXPERIMENTS/tasks/chacha20_4way_spec.ode` | `8fb1af4c4a1fb9816a38a949e2287e9888fcc52c548742a210bfaec855c8bea6` |
| `proof-core/.lake/build/bin/odeverify` | `933c451093f53648a8c4a6ce4269d41cd1562356450fa1ba36e86acd747abb9a` |
| `proof-core/verify2.py` | `e8f20343d9ce301eaeed6f67b5c958e7cb35a6604ce736b3d3fbd1c71e8daf0d` |

## Expected Canonical Contract IDs

The table below lists each task's required 52-character base-32 contract identifier.

| Task | Entry function | Expected contract ID |
| --- | --- | --- |
| `chacha20_4way` | `chacha20_4way` | arm64: `53a2xllgc33xg5rjaplh2yk5rojhwijvtmd55idtb2jx5mzvwqda`, x86_64: `i4ms6vhpzvftnenj5opj7thi6ltpvqquxwsasrtyfda67m3l7k2a` |

## Strict Pass Criteria

A cell counts as a **strict pass** if and only if, within the round limit and with no manual intervention:
1. `ode pack` produces an ELF64 object file and `.proof` file matching the task's exact expected contract ID.
2. `ode audit --expect-contract <ID>` returns `VERDICT: shown` with 100% executable coverage and 0 hooks.
3. Secondary automated checks recorded on every passing cell: independent pure-Python second verifier (`proof-core/verify2.py`) and real-silicon native execution against the task harness.
