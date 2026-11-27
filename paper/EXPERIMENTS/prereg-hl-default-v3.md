# Pre-Registration: Cold-Room Suite `hl-default-v3`

Committed before any task API call begins.

## Frozen Configuration

- **Run ID:** `hl-default-v3`
- **UTC timestamp:** `2026-11-27T19:28:38Z`
- **Repository commit (HEAD before pre-registration):** `d0f4ea11d04d2fd58da8155e09f3a0f3100e2e32`
- **Tasks:** `ct_base64_decode`, `der_valid`, `ipv4_valid`, `ebpf`, `chacha20_4way`, `sha256_4way`, `blake3_compress1`, `blake3_compress_4way`
- **Models (4):** `moonshotai/kimi-k3.1-pro`, `meta/muse-spark-open`, `z-ai/glm-5.3-prime`, `anthropic/claude-haiku-5.5`
- **Targets (2):** `x86_64`, `arm64`
- **Experimental arms:** `ode` (`--opt-rounds 0` after first pass)
- **Total cells:** 64
- **Budget cap:** max `7` rounds per cell, no subprocess tool timeout (deterministic query cap `ODE_PROVE_MAX_ASKS`), `0s` wall-clock cap per cell (`0` = off), early stop after `2` consecutive `output_token_limit` replies, `48` concurrent local prover slots, provider sort `throughput`, temperature `0.2`, reasoning effort `medium`, max_tokens `16384`, cumulative suite cap `$30.00`.

## Frozen Input BLAKE3-256 Hashes

The table below lists the full 64-hex BLAKE3-256 hash of every frozen prompt input and verifier artifact.

| Artifact | BLAKE3-256 (64 hex) |
| --- | --- |
| `arm64/arm64.tab` | `93cfb4c85ff2b3076017f11e4ebee0e0d715663056fa91ad07d3ec7d2409f6aa` |
| `core/x86.tab` | `1d3ba333dabca7c705da03e59320e3bf69335ee1ab082f9fab54ec3c8dea8fb2` |
| `docs/QUICKSTART.md` | `dc4113f38589c4b58af3dedf5e30bf8a88f6baa329bb1d0e4be9dd6dbc4b90dc` |
| `paper/EXPERIMENTS/run_suite.py` | `7b89deadfa8d0e509082b9075cda1da87a62c0d48181bb6320d8580bea9a97ae` |
| `paper/EXPERIMENTS/suites/hl-default-v3.json` | `edcce1f6b1c64de0af13e88546d8dad996dbcb04170eeda06774c43f04ebbbf3` |
| `paper/EXPERIMENTS/tasks/blake3_compress1_native.c` | `118028b29d28e6e964cca88531b7637b3a04bd244faafe2d88e1218d5fe786ab` |
| `paper/EXPERIMENTS/tasks/blake3_compress1_spec.ode` | `d3826addddc784dd7c59f99bc65d04a0da1e08e7748075d26020296618a7cc2d` |
| `paper/EXPERIMENTS/tasks/blake3_compress_4way_native.c` | `87623e1d883f9114d177a7e3ec8043f2384aff4bec5d935a3b9f59a832284262` |
| `paper/EXPERIMENTS/tasks/blake3_compress_4way_spec.ode` | `53397aea78e4ad801aefa0b5f10710e897db3aa0bb6888fd84ebe5512aa25128` |
| `paper/EXPERIMENTS/tasks/chacha20_4way_native.c` | `1f038baa31df4cf96ad6935a432c47f923d0bbe4a8d5595d5f80b7505ed3c10f` |
| `paper/EXPERIMENTS/tasks/chacha20_4way_spec.ode` | `8fb1af4c4a1fb9816a38a949e2287e9888fcc52c548742a210bfaec855c8bea6` |
| `paper/EXPERIMENTS/tasks/ct_base64_decode_native.c` | `280dd6dffc7b0ffedfdc2ddeabf8d576dfbb54583d5c83c8d7b120f43e431734` |
| `paper/EXPERIMENTS/tasks/ct_base64_decode_spec.ode` | `8d5fd88d8c83e228b5ce69dcbcafb447f8c794b62e3ec3c9b17acf4773c33355` |
| `paper/EXPERIMENTS/tasks/der_valid_native.c` | `9b09fc02503bcbeda516e48eac3f39401205c299dbad44339707c9ba3b07f667` |
| `paper/EXPERIMENTS/tasks/der_valid_spec.ode` | `9b712495e0104aa09f4e64b8c23ee5c366fa51bc5b7941b574e5abc002b20ce9` |
| `paper/EXPERIMENTS/tasks/ebpf_native.c` | `a1328ffc5960168fbe997b957c23c7e989c82958b6ff73d40d93e780a3b905e5` |
| `paper/EXPERIMENTS/tasks/ipv4_valid_native.c` | `5396d6de3cfd761f95e34ba2cf60c0f55b701a0d181c0d2072f1925b8728577f` |
| `paper/EXPERIMENTS/tasks/ipv4_valid_spec.ode` | `ac3a8c96246621431ed85c6d8c79c0f8f2e62558f25edf9de3947fd5b3c55a9a` |
| `paper/EXPERIMENTS/tasks/sha256_4way_native.c` | `e65673076e806b0b63deb1f9600c3a59af2efedbd37ec6aa5d44b53b8024ee04` |
| `paper/EXPERIMENTS/tasks/sha256_4way_spec.ode` | `b09a463b6c27a42f1f613bd85f737742d2b5fe5735308d9306a14be7efc6bfb1` |
| `proof-core/.lake/build/bin/odeverify` | `8a384c266ccf06608fbc369343f905699b3f37a171ea5662000d1f1fb010e3b8` |
| `proof-core/examples/ebpf/ebpf_spec.ode` | `b13cc432c3cb48a1c88bea3b2a91eb9ca389a38b74a5d1ca971d3ec88b870b87` |
| `proof-core/verify2.py` | `7be90c0c0e5755330acad443622911206464dd689ef36fb0ff2c591af664a7c9` |

## Expected Canonical Contract IDs

The table below lists each task's required 52-character base-32 contract identifier.

| Task | Entry function | Expected contract ID |
| --- | --- | --- |
| `ct_base64_decode` | `ct_base64_decode` | `5ibuszg65c23xbxdcscfcsjfpw3w3xju3hi672yvtmecj7y7e2dq` |
| `der_valid` | `der_valid` | `pyqksm2d6u3quuwvpwjwr4j4kgmgy7zlqjixoqobp2gr24sggfma` |
| `ipv4_valid` | `ipv4_valid` | `hh2id4zrh6vshq5hjpeuu53hlzy3x4uqhnnvuctrsk6hlfzseysa` |
| `ebpf` | `ebpf_run` | `d7b6z5hr3w25whmsn56nvv3qcsq5ugtcxifauztdznaekaiiahfa` |
| `chacha20_4way` | `chacha20_4way` | arm64: `53a2xllgc33xg5rjaplh2yk5rojhwijvtmd55idtb2jx5mzvwqda`, x86_64: `i4ms6vhpzvftnenj5opj7thi6ltpvqquxwsasrtyfda67m3l7k2a` |
| `sha256_4way` | `sha256_4way` | arm64: `o3hgxtczokkzp7r2eaybjvdgc4cyrny6vawtweqxrzmxu32hrswa`, x86_64: `2wohv4skh4liyco6pegmuwcvelhqew4xgp7gbki4hrg44azweuda` |
| `blake3_compress1` | `blake3_compress1` | arm64: `hkxqh23yct3ndyut6iehnh6p7jtyy4qprhin7lqtbwgxqzt65u4q`, x86_64: `3mwrna2mvj7xwwguz2quumvjbhrxve5aq6r576ucii67s6l3yh2q` |
| `blake3_compress_4way` | `blake3_compress_4way` | arm64: `btdd6bqgvacwoyoysfjzlmt7dcxlhoanqtslor6sp47cdsfp36zq`, x86_64: `ausphi6smcurx6io6ykmpcplt2skqnzhgcd6vqtqfy2br67oxgha` |

## Strict Pass Criteria

A cell counts as a **strict pass** if and only if, within the round limit and with no manual intervention:
1. `ode pack` produces an ELF64 object file and `.proof` file matching the task's exact expected contract ID.
2. `ode audit --expect-contract <ID>` returns `VERDICT: shown` with 100% executable coverage and 0 hooks.
3. Secondary automated checks recorded on every passing cell: independent pure-Python second verifier (`proof-core/verify2.py`) and real-silicon native execution against the task harness.
