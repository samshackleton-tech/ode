# Pre-Registration: Cold-Room Suite `sha256-v1`

Committed before any task API call begins.

## Frozen Configuration

- **Run ID:** `sha256-v1`
- **UTC timestamp:** `2026-11-26T09:18:02Z`
- **Repository commit (HEAD before pre-registration):** `b4b8679b718a7a876e8abb50a647af842f5cdf68`
- **Tasks:** `sha256_4way`
- **Models (7):** `openai/gpt-6.2-astra-pro`, `anthropic/claude-fable-5.2`, `google/gemini-4-neon`, `anthropic/claude-sonnet-5.5`, `anthropic/claude-haiku-5.5`, `qwen/qwen3.8-2.4t-a95b`, `moonshotai/kimi-k3.1-pro`
- **Targets (2):** `arm64`, `x86_64`
- **Experimental arms:** `blind`, `advised` (`--opt-rounds 4` after first pass)
- **Total cells:** 28
- **Budget cap:** max `8` rounds per cell, `45s` tool timeout, `720s` wall-clock cap per cell, early stop after `2` consecutive `output_token_limit` replies, `10` concurrent local prover slots, temperature `0.2`, reasoning effort `medium`, max_tokens `32000`, cumulative suite cap `$80.00`.

## Frozen Input BLAKE3-256 Hashes

The table below lists the full 64-hex BLAKE3-256 hash of every frozen prompt input and verifier artifact.

| Artifact | BLAKE3-256 (64 hex) |
| --- | --- |
| `arm64/arm64.tab` | `f22aec61d16cae81f33bedca91e22bf5ede2bc5ec396d0f9153a73e30e60d511` |
| `core/x86.tab` | `b4b7cdf8e708835920701e4fb9979b56365bb83551bac99df1d07332de8bd45f` |
| `docs/QUICKSTART.md` | `c969b45ed458beb12e60f54b94be6157b52b307155830b3e4bbbc488dc68c0dd` |
| `paper/EXPERIMENTS/run_suite.py` | `4137879c34f4af7a1c6c3687d9a35e87d7c79bd644cc82bf997ebe8c8bee6404` |
| `paper/EXPERIMENTS/tasks/sha256_4way_native.c` | `e65673076e806b0b63deb1f9600c3a59af2efedbd37ec6aa5d44b53b8024ee04` |
| `paper/EXPERIMENTS/tasks/sha256_4way_spec.ode` | `b09a463b6c27a42f1f613bd85f737742d2b5fe5735308d9306a14be7efc6bfb1` |
| `proof-core/.lake/build/bin/odeverify` | `bad00e34235da9fe56c4c189dfd92d7a043a0182bbb779513963677bf1e5c6fd` |
| `proof-core/verify2.py` | `6f149adf9edfa32b80572a233d3e9db8970ea60f8938973ae244c8630587ad99` |

## Expected Canonical Contract IDs

The table below lists each task's required 52-character base-32 contract identifier.

| Task | Entry function | Expected contract ID |
| --- | --- | --- |
| `sha256_4way` | `sha256_4way` | arm64: `o3hgxtczokkzp7r2eaybjvdgc4cyrny6vawtweqxrzmxu32hrswa`, x86_64: `2wohv4skh4liyco6pegmuwcvelhqew4xgp7gbki4hrg44azweuda` |

## Strict Pass Criteria

A cell counts as a **strict pass** if and only if, within the round limit and with no manual intervention:
1. `ode pack` produces an ELF64 object file and `.proof` file matching the task's exact expected contract ID.
2. `ode audit --expect-contract <ID>` returns `VERDICT: shown` with 100% executable coverage and 0 hooks.
3. Secondary automated checks recorded on every passing cell: independent pure-Python second verifier (`proof-core/verify2.py`) and real-silicon native execution against the task harness.
