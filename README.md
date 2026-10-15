Ode: a short poem of praise

## What this is

Ode builds cryptographic code together with proofs that a small checker
verifies: `SPEC.md` defines it, `DESIGN.md` says why it is shaped this
way. This repository is an early implementation that proves BLAKE3's
building blocks, and the hash of fixed-length messages, down to the
AArch64 bytes the CPU runs.

```sh
pypy3 -m ode build-a64 examples/blake3-hash-3.sexp /tmp/h  # produce bytes + certificate
pypy3 -m ode check /tmp/h                                  # ACCEPT: proved for every input
pypy3 -m ode run   /tmp/h 6513249 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
# 2897426276 860964408 ... -- the 8 words of blake3("abc"), run natively
pypy3 -m unittest discover -s tests                        # 26 tests
```

`6513249` is `"abc"` as a little-endian word; the other 15 are the
block's zero padding. Needs PyPy3; native runs need aarch64 Linux
(`build` without `-a64` makes portable W32 bytes, run by interpretation).

## How it fits together

1. **A specification** says what to compute, in one s-expression
   (`examples/blake3-g.sexp` is G in 8 steps; read its `(inputs ...)` and
   `(outputs ...)` for the interface). Specifications compose by hash:
   the 65-byte hash calls the compression by `(call #hash ...)`, with the
   compression carried inside under `(defs ...)`.
2. **A producer** (`ode/produce.py`) turns a specification into bytes and
   a certificate. Nothing relies on it. For W32 it certifies each callee
   first and has the caller call it *by certificate*.
3. **The checker** (`ode/check.py`) decodes the bytes -- W32
   (`ode/word.py`) or eight AArch64 instruction forms (`ode/a64.py`) --
   executes them and the specification symbolically over fresh inputs,
   and accepts when both reduce to the same expressions. Straight-line
   code and constant addresses make memory safety and a data-independent
   trace hold by construction. A call by certificate is checked once and
   then stands as one opaque function of its arguments, the same node on
   both sides (congruence): a 3,072-byte hash, 50 compressions, checks in
   0.05 s instead of 103 s.
4. **Running** executes exactly the program the checker proved, from the
   bytes it read once.

Every definition, certificate, and record is a canonical s-expression
(`ode/canon.py`) named by its BLAKE3 hash (`ode/blake3.py`).

## What a relying party relies on

`game/` shows it end to end: Bob receives only a 235-line root (BLAKE3
and a launcher) and about 260 bytes of hashes from Sam, and everything
else -- the checker itself, the specifications, the implementation --
from anyone, admitted by hash or by proof. Thirty-three recorded
attacks, replayed by the tests, have found and fixed several real flaws
and lost every time; `game/README.md` has them.

The AArch64 model is checked against this CPU on random states
(`tests/test_a64.py`), not derived from Arm's specification, and the
producer is naive: about 8 us per 65-byte hash natively, mostly call
overhead (wall time, `time.perf_counter_ns`, this VM; the team's
`clocks` crate is not available here).

## Next

BLAKE3 of any length: a specification with definite recursion over its
chunks and tree, and a proof by induction over the implementation's
chunk loop, so one certificate covers every length.
