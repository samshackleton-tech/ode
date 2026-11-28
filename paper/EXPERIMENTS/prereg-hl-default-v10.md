# Pre-Registration: Cold-Room Suite `hl-default-v10`

Committed before any task API call begins.

## Frozen Configuration

- **Run ID:** `hl-default-v10`
- **UTC timestamp:** `2026-11-28T05:04:53Z`
- **Repository commit (HEAD before pre-registration):** `fcead48e66b0c12bfe3ed70b74f4b95a1ba8a021`
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
| `docs/QUICKSTART.md` | `c26c8901c9be43bbe416f0cc3e5e7c5d5d5e3d343bac0629027fc9ea70dd4c4c` |
| `paper/EXPERIMENTS/run_suite.py` | `2cfbb7631d9b6a0a41e0cc451739d4d2ea219088d2fc5048363abe6368860e7b` |
| `paper/EXPERIMENTS/suites/hl-default-v10.json` | `ed805163efd83456a76e1eeb9e2195f81221c6283f7b9b79a8bb7cded69a5fd1` |
| `paper/EXPERIMENTS/tasks/blake3_compress1_native.c` | `118028b29d28e6e964cca88531b7637b3a04bd244faafe2d88e1218d5fe786ab` |
| `paper/EXPERIMENTS/tasks/blake3_compress1_spec.ode` | `d3826addddc784dd7c59f99bc65d04a0da1e08e7748075d26020296618a7cc2d` |
| `paper/EXPERIMENTS/tasks/blake3_compress_4way_native.c` | `87623e1d883f9114d177a7e3ec8043f2384aff4bec5d935a3b9f59a832284262` |
| `paper/EXPERIMENTS/tasks/blake3_compress_4way_spec.ode` | `53397aea78e4ad801aefa0b5f10710e897db3aa0bb6888fd84ebe5512aa25128` |
| `paper/EXPERIMENTS/tasks/chacha20_4way_native.c` | `1f038baa31df4cf96ad6935a432c47f923d0bbe4a8d5595d5f80b7505ed3c10f` |
| `paper/EXPERIMENTS/tasks/chacha20_4way_spec.ode` | `8fb1af4c4a1fb9816a38a949e2287e9888fcc52c548742a210bfaec855c8bea6` |
| `paper/EXPERIMENTS/tasks/ct_base64_decode_native.c` | `b7a882968d57fb7c13739a1cc7cfc7d687ac32db6a166bbd4983edef427401ec` |
| `paper/EXPERIMENTS/tasks/ct_base64_decode_spec.ode` | `8d5fd88d8c83e228b5ce69dcbcafb447f8c794b62e3ec3c9b17acf4773c33355` |
| `paper/EXPERIMENTS/tasks/der_valid_native.c` | `e3731241543b5c160e2436f5022f9eea887d2561765389d175f17da52fe0ce9b` |
| `paper/EXPERIMENTS/tasks/der_valid_spec.ode` | `9b712495e0104aa09f4e64b8c23ee5c366fa51bc5b7941b574e5abc002b20ce9` |
| `paper/EXPERIMENTS/tasks/ebpf_native.c` | `6efdeb57d0417303be7fc128fb7bf8d2b5cac628612143f758bf8e5377145465` |
| `paper/EXPERIMENTS/tasks/ipv4_valid_native.c` | `67b7aa72363663396cb5529e14e9ba30a3bfb32c22e8c49907ef8f1a2e19ee66` |
| `paper/EXPERIMENTS/tasks/ipv4_valid_spec.ode` | `ac3a8c96246621431ed85c6d8c79c0f8f2e62558f25edf9de3947fd5b3c55a9a` |
| `paper/EXPERIMENTS/tasks/sha256_4way_native.c` | `6484615258676752a084382e8f6ba8ac6b8c8d575db5f99c9934ef4117001a06` |
| `paper/EXPERIMENTS/tasks/sha256_4way_spec.ode` | `b09a463b6c27a42f1f613bd85f737742d2b5fe5735308d9306a14be7efc6bfb1` |
| `proof-core/.lake/build/bin/odeverify` | `e7a17cc25119af561dad2647fa2baf96a2f95a9541e1532a85836ea1a9cfe73a` |
| `proof-core/examples/ebpf/ebpf_spec.ode` | `b13cc432c3cb48a1c88bea3b2a91eb9ca389a38b74a5d1ca971d3ec88b870b87` |
| `proof-core/verify2.py` | `fc01c3466c23c321d7912214e737db531073f7120cff09349d1e095e0e2db107` |
| `std/bytes.ode` | `764ca47f8e33075a668194d106c89dbacfa350166cc1d1b0f16020e559fb1960` |
| `std/int.ode` | `880980bc60a819fa3d1940153c98f45d4a6af891ef1e26fae93221fa51c2f2ab` |
| `std/vec.ode` | `fe5e2cbf31f4e47cc7c4b70ad3ae8053f759721bbd38f68ce55b333afa237c22` |

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
