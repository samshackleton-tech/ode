# Pre-Registration: Cold-Room Suite `hl-reg-v3`

Committed before any task API call begins.

## Frozen Configuration

- **Run ID:** `hl-reg-v3`
- **UTC timestamp:** `2026-11-26T22:34:00Z`
- **Repository commit (HEAD before pre-registration):** `ceb5c60042fb29b4eef207a094421da24c0a0058`
- **Tasks:** `der_valid`, `ct_base64_decode`, `ipv4_valid`, `chacha20_4way`
- **Models (9):** `openai/gpt-6.2-astra-pro`, `anthropic/claude-fable-5.2`, `google/gemini-4-neon`, `anthropic/claude-sonnet-5.5`, `anthropic/claude-haiku-5.5`, `qwen/qwen3.8-2.4t-a95b`, `moonshotai/kimi-k3.1-pro`, `meta/muse-spark-open`, `z-ai/glm-5.3-prime`
- **Targets (2):** `x86_64`, `arm64`
- **Experimental arms:** `advised` (`--opt-rounds 2` after first pass)
- **Total cells:** 72
- **Budget cap:** max `8` rounds per cell, no subprocess tool timeout (deterministic query cap `ODE_PROVE_MAX_ASKS`), `0s` wall-clock cap per cell (`0` = off), early stop after `2` consecutive `output_token_limit` replies, `48` concurrent local prover slots, provider sort `throughput`, temperature `0.2`, reasoning effort `medium`, max_tokens `32000`, cumulative suite cap `$140.00`.

## Frozen Input BLAKE3-256 Hashes

The table below lists the full 64-hex BLAKE3-256 hash of every frozen prompt input and verifier artifact.

| Artifact | BLAKE3-256 (64 hex) |
| --- | --- |
| `arm64/arm64.tab` | `93cfb4c85ff2b3076017f11e4ebee0e0d715663056fa91ad07d3ec7d2409f6aa` |
| `core/x86.tab` | `1d3ba333dabca7c705da03e59320e3bf69335ee1ab082f9fab54ec3c8dea8fb2` |
| `docs/QUICKSTART.md` | `42b4c988a95020b9ccc11dfb2d743a68378b6bb03dc365a80f6687320d8b58de` |
| `paper/EXPERIMENTS/run_suite.py` | `e083267456424ee14fc53ad9bf817a7c6597a78e2e2b5b9254a837283c1d4616` |
| `paper/EXPERIMENTS/suites/regression-v1.json` | `f89880728ba8bcb884a75c6c50949c1ce3d33d40b6cd14b94301f1e68f8ae368` |
| `paper/EXPERIMENTS/tasks/chacha20_4way_native.c` | `1f038baa31df4cf96ad6935a432c47f923d0bbe4a8d5595d5f80b7505ed3c10f` |
| `paper/EXPERIMENTS/tasks/chacha20_4way_spec.ode` | `8fb1af4c4a1fb9816a38a949e2287e9888fcc52c548742a210bfaec855c8bea6` |
| `paper/EXPERIMENTS/tasks/ct_base64_decode_native.c` | `280dd6dffc7b0ffedfdc2ddeabf8d576dfbb54583d5c83c8d7b120f43e431734` |
| `paper/EXPERIMENTS/tasks/ct_base64_decode_spec.ode` | `8d5fd88d8c83e228b5ce69dcbcafb447f8c794b62e3ec3c9b17acf4773c33355` |
| `paper/EXPERIMENTS/tasks/der_valid_native.c` | `9b09fc02503bcbeda516e48eac3f39401205c299dbad44339707c9ba3b07f667` |
| `paper/EXPERIMENTS/tasks/der_valid_spec.ode` | `9b712495e0104aa09f4e64b8c23ee5c366fa51bc5b7941b574e5abc002b20ce9` |
| `paper/EXPERIMENTS/tasks/ipv4_valid_native.c` | `5396d6de3cfd761f95e34ba2cf60c0f55b701a0d181c0d2072f1925b8728577f` |
| `paper/EXPERIMENTS/tasks/ipv4_valid_spec.ode` | `ac3a8c96246621431ed85c6d8c79c0f8f2e62558f25edf9de3947fd5b3c55a9a` |
| `proof-core/.lake/build/bin/odeverify` | `2ff4c8ccfe3b850b76f146a11411c6662556d460fd09f6d66728f11ef62a9ebb` |
| `proof-core/verify2.py` | `12caab95edfb880999a0c770c38bbe51a1170dbf252671c4cf666fb3fce9a8d4` |

## Expected Canonical Contract IDs

The table below lists each task's required 52-character base-32 contract identifier.

| Task | Entry function | Expected contract ID |
| --- | --- | --- |
| `der_valid` | `der_valid` | `pyqksm2d6u3quuwvpwjwr4j4kgmgy7zlqjixoqobp2gr24sggfma` |
| `ct_base64_decode` | `ct_base64_decode` | `5ibuszg65c23xbxdcscfcsjfpw3w3xju3hi672yvtmecj7y7e2dq` |
| `ipv4_valid` | `ipv4_valid` | `hh2id4zrh6vshq5hjpeuu53hlzy3x4uqhnnvuctrsk6hlfzseysa` |
| `chacha20_4way` | `chacha20_4way` | arm64: `53a2xllgc33xg5rjaplh2yk5rojhwijvtmd55idtb2jx5mzvwqda`, x86_64: `i4ms6vhpzvftnenj5opj7thi6ltpvqquxwsasrtyfda67m3l7k2a` |

## Strict Pass Criteria

A cell counts as a **strict pass** if and only if, within the round limit and with no manual intervention:
1. `ode pack` produces an ELF64 object file and `.proof` file matching the task's exact expected contract ID.
2. `ode audit --expect-contract <ID>` returns `VERDICT: shown` with 100% executable coverage and 0 hooks.
3. Secondary automated checks recorded on every passing cell: independent pure-Python second verifier (`proof-core/verify2.py`) and real-silicon native execution against the task harness.
