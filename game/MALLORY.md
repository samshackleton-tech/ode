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
