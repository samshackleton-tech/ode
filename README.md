Ode: a short poem of praise

## What this is

Ode builds cryptographic code together with proofs that a small checker
verifies: `SPEC.md` defines it, `DESIGN.md` says why it is shaped this
way. This repository is an early implementation. BLAKE3, for messages of
any length, is one 50-line specification (`examples/blake3.sexp`). For
any length you choose, Ode produces code -- down to AArch64 bytes the CPU
runs -- and proves it computes that specification for every message of
that length.

```sh
pypy3 -m ode build-a64 examples/blake3.sexp /tmp/h len=44   # bytes + certificate, 44-byte messages
pypy3 -m ode check /tmp/h                                   # ACCEPT: proved for every such message
pypy3 -m ode hash  /tmp/h "The quick brown fox jumps over the lazy dog."
# 4c9bd68d7f0baa2e167cef98295eb1ec99a3ec8f0656b33dbae943b387f31d5d, run natively
pypy3 -m unittest discover -s tests                         # 27 tests
```

Needs PyPy3; native runs need aarch64 Linux (`build` without `-a64`
makes portable W32 bytes, run by interpretation). A proof covers one
length; covering every length at once is the next step.

## How it fits together

1. **A specification** says what to compute, in one s-expression: words,
   naturals (lengths, indices), lists, `if`, `let`, recursive local
   functions, and callees named by hash in `(uses ...)`. `blake3.sexp`
   reads like C2SP: a chunk chain, a recursive tree split, the root; its
   `(inputs ...)` and `(outputs ...)` are the interface. One evaluator
   (`ode/word.py`) gives the language its meaning, over three algebras:
   integers to run, symbolic expressions to prove, W32 steps to compile.
2. **A producer** (`ode/produce.py`) turns a specification, at a chosen
   length, into bytes and a certificate. Nothing relies on it. For W32 it
   certifies each callee first and calls it *by certificate*.
3. **The checker** (`ode/check.py`) decodes the bytes -- W32
   (`ode/word.py`) or eight AArch64 instruction forms (`ode/a64.py`) --
   evaluates them and the specification symbolically over fresh inputs,
   and accepts when both reduce to the same expressions. Straight-line
   code and constant addresses make memory safety and a data-independent
   trace hold by construction. A call by certificate is checked once and
   then stands as one opaque function of its arguments, the same node on
   both sides (congruence): a 16 KB hash, 271 compressions, checks in
   about a second.
4. **Running** executes exactly the program the checker proved, from the
   bytes it read once.

Every definition, certificate, and record is a canonical s-expression
(`ode/canon.py`) named by its BLAKE3 hash (`ode/blake3.py`).

## What a relying party relies on

`game/` shows it end to end: Bob receives only a 235-line root (BLAKE3
and a launcher) and about 260 bytes of hashes from Sam, and everything
else -- the checker itself, the specifications, the implementation --
from anyone, admitted by hash or by proof. Thirty-four recorded attacks,
replayed by the tests, have found and fixed several real flaws and lost
every time; `game/README.md` has them.

The AArch64 model is checked against this CPU on random states
(`tests/test_a64.py`), not derived from Arm's specification, and the
AArch64 producer is naive: about 8 us per short hash natively, mostly
call overhead (wall time, `time.perf_counter_ns`, this VM; the team's
`clocks` crate is not available here).

## Next

One certificate for every length: loops over chunks whose trip count
depends only on the length, and a proof by induction over them.
