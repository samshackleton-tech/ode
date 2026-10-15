# The adversarial game: Sam, Bob, and Mallory

A test from the relying party's side. Three roles:

- **Sam** publishes `bootstrap/`: the specification of BLAKE3's G
  (`blake3-g.sexp`), its hash pinned in `TRUST`, the checker and the
  canonical-form reader (`ode/`), and Bob's whole procedure (`bob.py`).
  This is everything Bob relies on (SPEC s1) and it travels separately
  from everything else.
- **Mallory** supplies the implementation: a directory with a machine
  definition, `binary.bin`, and `certificate.sexp`. He may change
  anything in it. He knows every input Bob will use and may add his own.
- **Bob** follows `bob.py` literally: load the bootstrap's modules first,
  confirm the spec's hash, require the certificate to be about that
  spec, run the checker, and on ACCEPT run Mallory's bytes.

Mallory wins when Bob prints `ACCEPT` and then a wrong G. The inputs are
public because the claim is universal: a kernel wrong on one known input
is exactly the real-world attack, and hiding inputs would only hide the
failure.

```sh
pypy3 game/make_attacks.py                # regenerate every attack, deterministically
pypy3 game/referee.py game/attacks/*      # replay every recorded attack
```

The attacks themselves are produced by `game/make_attacks.py` -- one
function per attack, so the corpus is a program future readers can
rerun, vary, and learn from, not a pile of one-off directories.

Each attack lives in `attacks/NN-name/` with a `NOTES` file. The
corpus from round 1 (ten attacks, all lost) and what the game found:

| Attack | Idea | Result |
|---|---|---|
| 01 | flip a byte of `binary.bin` | rejected: binding of the executed file (fixed before the game: the checkers once never opened `binary.bin`) |
| 02 | wrong machine, honest hashes | rejected: symbolic disagreement |
| 03 | drop an output | rejected: output count |
| 04 | plant an `ode/` package and `sitecustomize.py` in cwd | no effect: bootstrap loads by absolute path first |
| 05 | honest definition, mutant binary | rejected: emitter binding |
| 06 | out-of-domain inputs | **found**: Bob printed ACCEPT then crashed. Fixed: Bob rejects inputs outside the spec's domain before anything else; the referee scores ACCEPT there as a win for Mallory |
| 07 | rotr 39 in the bytes, 7 in the definition | rejected: emitter binding |
| 08 | Mallory's own chosen inputs | correct: the claim is universal |
| 09 | correct hash, non-canonical file bytes | rejected: the reader |
| 10 | forward reference in raw W32 bytes | rejected by the decoder; and **found**: an all-digit hex string was indistinguishable from an integer in canonical form. Fixed: byte strings are `#hex` and symbols never start with a digit |

## Round 2: the hash target

A second target, `hash65` -- BLAKE3 of a 65-byte message, two
compressions composed by `(call #hash ...)` with the compression embedded
under `(defs ...)` -- widened the surface to the call machinery, the
producer's inlining versus the checker's expansion, and the wider W32
header. Ten more attacks, all lost, one finding:

| Attack | Idea | Result |
|---|---|---|
| 11 | honest hash65 build | control: correct |
| 12 | the two blocks swapped | rejected: symbolic disagreement |
| 13 | second compression chained from the IV | rejected: symbolic disagreement |
| 14 | ROOT on block 0 alone (hash of the first 64 bytes) | rejected: symbolic disagreement |
| 15 | an honest machine with one add commuted | accepted and correct: commutativity is canonical |
| 16 | Mallory's own messages (zero, repeated block, equal blocks) | correct: the claim is universal |
| 17 | the spec named as the machine | rejected: not a wmachine |
| 18 | raw binary whose outputs index the inputs | rejected: emitter binding |
| 19 | the proved hash-3 machine certified against the hash65 spec, `(inputs 16)` | rejected: inputs differ |
| 20 | name capture in the producer's inliner | **found**: a spec whose input was named `t0` collided with minted names; an invalid machine (SSA caught it; nothing wrong was ever certified), but a producer bug. Fixed: fresh names use a prefix no spec name starts with |

A direct probe of the deepest surface -- the producer's inlining
against the checker's independent symbolic expansion on a spec built to
provoke name capture -- agreed with the spec's semantics on 200 random
inputs after the fix, and the checker accepted it.

Besides the corpus, 8,000 randomized trials compared the checker's
symbolic rewrites against concrete u32 evaluation and found no unsound
rewrite, and the DAG's value on the full hash65 machine agreed with
concrete execution on 50 random messages. The corpus is replayed by
`tests/test_game.py`.
