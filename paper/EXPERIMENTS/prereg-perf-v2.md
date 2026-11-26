# Pre-Registration: Cold-Room Suite `perf-v2`

Committed before any task API call begins.

## Frozen Configuration

- **Run ID:** `perf-v2`
- **UTC timestamp:** `2026-11-26T05:40:34Z`
- **Repository commit (HEAD before pre-registration):** `190cac74b22f31750125a8a6fa25b3833fbf1c62`
- **Tasks:** `weighted_sum`
- **Models (4):** `openai/gpt-6.2-astra-pro`, `anthropic/claude-fable-5.2`, `google/gemini-4-neon`, `anthropic/claude-sonnet-5.5`
- **Targets (2):** `x86_64`, `arm64`
- **Experimental arms:** `blind`, `advised` (`--opt-rounds 3` after first pass)
- **Total cells:** 16
- **Budget cap:** max `6` rounds per cell, `120s` tool timeout, `900s` wall-clock cap per cell, early stop after `2` consecutive `output_token_limit` replies, `4` concurrent local prover slots, temperature `0.2`, reasoning effort `medium`, max_tokens `32000`, cumulative suite cap `$35.00`.

## Frozen Input BLAKE3-256 Hashes

The table below lists the full 64-hex BLAKE3-256 hash of every frozen prompt input and verifier artifact.

| Artifact | BLAKE3-256 (64 hex) |
| --- | --- |
| `arm64/arm64.tab` | `adaa95953e3526fa7e2ffcadf55b4aaebfd3417b2e9cba26f6a433d2c1c521c6` |
| `core/x86.tab` | `e9ff8cc0b3467375e7935569b469474e04cdd91a15bfb02556a7a959e4d38d73` |
| `docs/QUICKSTART.md` | `5037f8ed720737950363a2815140b17b14fcec2099b46a2a8501e0fc30cfffeb` |
| `paper/EXPERIMENTS/run_suite.py` | `ba8800888077d6b7685c17e77483a80193376353732851ae7d66bac826694a1a` |
| `paper/EXPERIMENTS/tasks/weighted_sum_native.c` | `bf6911591f5e5886c6270af792d0f6b8eb8351ccb1d67978b8442c84543a3353` |
| `paper/EXPERIMENTS/tasks/weighted_sum_spec.ode` | `a36744c1338fe4b1e8cd362e2d428b3d17129f7dcdc83fb865de6ca0311db508` |
| `proof-core/.lake/build/bin/odeverify` | `f028cb223488b94502093f9c085d2f4d7b9433e96d21312c7b630259815e36b9` |
| `proof-core/verify2.py` | `e970ed97bac00630293304e5b2e7ceb5eb562ea8e4ea0c0fac732f448608f904` |

## Expected Canonical Contract IDs

The table below lists each task's required 52-character base-32 contract identifier.

| Task | Entry function | Expected contract ID |
| --- | --- | --- |
| `weighted_sum` | `weighted_sum` | `dlj5zmyx5h52zjp64x66mwebhrwevsttwvvbbgujxktxk6eat4vq` |

## Strict Pass Criteria

A cell counts as a **strict pass** if and only if, within the round limit and with no manual intervention:
1. `ode pack` produces an ELF64 object file and `.proof` file matching the task's exact expected contract ID.
2. `ode audit --expect-contract <ID>` returns `VERDICT: shown` with 100% executable coverage and 0 hooks.
3. Secondary automated checks recorded on every passing cell: independent pure-Python second verifier (`proof-core/verify2.py`) and real-silicon native execution against the task harness.
