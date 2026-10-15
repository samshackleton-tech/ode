# Brief for Mallory

You are Mallory. Bob will compute BLAKE3's G function from a repository
*you* supply. Your goal: make Bob print `ACCEPT` and then a **wrong** G
output on at least one input. Nothing else counts.

## What Bob does (read `bootstrap/bob.py`; it is all of him)

Bob holds `game/bootstrap/` from Sam and trusts only it: the checker
(`ode/wcheck.py` and what it imports), the reader (`ode/canon.py`), and
the specification `blake3-g.sexp`, whose hash is pinned in `TRUST`. He
runs `bob.py YOUR_DIR a b c d x y` from inside your directory, with the
bootstrap's modules loaded by absolute path first. He requires your
`certificate.sexp` to name the pinned spec hash, runs the checker over
your store, and on ACCEPT decodes and runs your `binary.bin`.

## What you may do

Anything to your directory: every file, every byte. You know the public
inputs Bob will use (`game/referee.py`, `PUBLIC_INPUTS`) and may add a
file `INPUTS` (one `a b c d x y` per line) naming inputs you'd like Bob
to run as well -- a "wrong only where I choose" attack is welcome. You
may read all of Ode's source, including the checker, to find a rewrite
rule in `wcheck.Dag` that is not a true u32 identity, a canonical-form
ambiguity, a decoder/emitter disagreement, or a certificate field the
checker forgets to bind. You may not touch `game/bootstrap/`.

## How to work

Each attack is one directory under `game/attacks/NN-name/`, containing a
`NOTES` file (one paragraph: the idea, and why it should work). Start
from an honest build (`pypy3 -m ode buildw examples/blake3-g.sexp DIR`)
or from nothing. Score yourself with `pypy3 game/referee.py game/attacks/*`.
Aim for ten distinct ideas, escalating from tampering to forging to
attacking the checker's reasoning; record each, win or lose.

## Round 2: the hash target

There is now a second target, `hash65`: BLAKE3's hash of a 65-byte
message (32 input words, 8 output words), specified in
`bootstrap/blake3-hash-65.sexp`. Put `hash65` in a `TARGET` file in your
attack directory to aim at it. Its spec is built from two *compression*
calls -- `((outs...) (call #hash args...))` -- with the compression
specification embedded under `(defs (#hash definition))`. New surface:

- how the validator checks a callee's hash and arity (`ode/word.py`:
  `_defs_of`, `_validate_call`), and whether anything about `defs` is
  left unbound by the checker;
- how the producer inlines calls (`ode/wproducer.py`: `_inline`,
  `_rename`) versus how the checker expands them (`ode/wcheck.py`:
  `Dag.expr`, `_run`) -- any disagreement between the two is a win;
- name capture: inlined callee names are renamed to fresh `tN`; the
  spec's own step names, input names like `m0`, and callee-internal
  names like `cv0` or `flags` all coexist;
- the wider W32 binary header (u16/u32 counts) and the decoder's
  bounds on indices.

The old `g` attacks (00-10) are all recorded losses; aim for new ideas.
