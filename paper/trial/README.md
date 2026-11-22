# The trial's files

What stands behind [`../STYLES.md`](../STYLES.md) and [`../TRACE-PROPOSAL.md`](../TRACE-PROPOSAL.md). None of it is one of the repository's tools, and `tests.sh` runs none of it.

| File | What it is |
|---|---|
| `ode2.py` | The prototype front end (420 lines): a `target` line, names for registers, a `frame` of named fields, `inline fn`, `for` over a constant range, `:=`, and a `place` written at its loop. For x86-64 it hands plain instructions to `core/asm.py`; for AArch64 it prints assembly for clang. It chooses no register and adds no instruction. |
| `src/` | The same functions in each notation: three mixing steps (`mix16_raw.ode`, `mix16_macro.ode`, `mix16.ode2`, `mix16.spec`); a scan with a loop (`all_zero.ode` with `all_zero.places`, `all_zero.ode2`, `all_zero.spec`); `quad32.ode2` (today's is `proof-core/examples/quad/quad32.ode`); `arm.ode2` with the C it is run against, `arm_check.c`. |
| `test_styles.py` | Compiles each source and compares the bytes; tries nine sources that the front end must refuse. With `--verify OUT` it also runs the prover and the verifier on each x86-64 function (`odeverify` must be built). With `--arm OUT` it assembles `src/arm.ode2` and runs it on an AArch64 Mac. |
| `results/` | What `--verify` wrote on an x86-64 Linux work machine and `--arm` on an Apple M6, on November 22, 2026. |
| `make_styles.py` | Writes the page of styles from `src/` and `results/`. |
| `trace/` | Three small programs that ask today's reader and verifier the questions of the trace proposal, and what they printed. |

To make everything again, in this folder:

```
python3 test_styles.py
python3 test_styles.py --verify results/verify.json
python3 test_styles.py --arm results/arm.json
python3 make_styles.py ../STYLES.md
```

The first runs anywhere with Python. The second needs the verifier built (`proof-core/README.md`) and takes about two minutes, one of them waiting for a prover that does not stop. The third needs clang on an AArch64 Mac.
