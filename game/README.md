# The adversarial game: Sam, Bob, and Mallory

A test from the relying party's side. Three roles:

- **Sam** publishes `bootstrap/`, which is all Bob must receive from
  Sam for *correctness*:
  - `root/` -- `blake3.py` and `launch.py`, 235 lines: the hash, and a
    launcher that reads an ode-base into memory, computes its tree hash,
    compares it with the package's pin, stops on any difference, and
    runs Bob's procedure from the very bytes it hashed.
  - `blake3/RELIANCE` -- about 260 bytes of s-expression: the pinned tree hash
    of the ode-base this package was checked against, and the hashes of
    its two specifications (G, and the hash of a 65-byte message).

  Everything else Bob needs only for *availability*, and may get from
  anyone: `game/ode-base/` (the checker, reader, store loader, semantics,
  and `bob.py`, admitted by tree hash; its hash is the root's own BLAKE3,
  so Bob relies on exactly one) and the specifications (fetched
  from Mallory's store by hash; readable copies in `examples/`). A wrong
  copy of any of them is a reject, never a wrong answer.
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

## Round 3: the root

Bob now holds only the root and the pins; Mallory may deliver the
ode-base and the specifications too, and the certificate no longer
names a machine definition -- the checker proves the decoded bytes, so
neither machine definitions nor the emitter are relied on. Attacks
05, 07, 09, 17 and 18 now lose to the proof itself (or are simply
irrelevant) instead of to binding checks.

| Attack | Idea | Result |
|---|---|---|
| 21 | Mallory's own ode-base, with a wcheck that accepts all | rejected by the root: tree hash differs |
| 22 | a genuine ode-base plus one added file | rejected by the root: tree hash differs |
| 23 | the delivered spec, with a trailing newline | rejected: not canonical |
| 24 | the spec withheld | rejected: Mallory can deny availability, never correctness |

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

## What `bootstrap/` itself relies on

This is a property of the bootstrap, not part of it, so it lives here:
running `root/launch.py` at all relies on the Python implementation
(PyPy), its standard library (`os`, `re`, `importlib`), the operating
system that reads files, runs processes, and maps executable pages,
ctypes (to call native code), and the hardware beneath -- in
particular, that the CPU executes the eight AArch64 forms as
`ode/a64.py` models them, which `tests/test_a64.py` checks on random
states rather than proves.
None of them is checked; each is a place where a fault could make Bob
accept a wrong answer. The real-machine milestone (SPEC s1, R4 and R5)
is where these shrink.

## Round 5: real AArch64, run natively

Bob's ode-base now proves AArch64 bytes (`ode/a64.py`) and runs them on
the CPU (`ode/native.py`). Controls 25-26 (G, and the 65-byte hash, as
proved AArch64) are accepted and correct natively. Attacks:

| Attack | Idea | Result |
|---|---|---|
| 27 | one ROR count off by one in real code | rejected: symbolic disagreement |
| 28 | a branch spliced in | rejected: outside the eight modelled forms |
| 29 | scratch declared one word short | rejected: the access is out of bounds |
| 30 | an extra store far past `out[]` | rejected: out of bounds |

Running natively adds to what the bootstrap relies on (below): the
kernel's mmap of executable pages, ctypes, and the CPU executing the
eight forms as modelled -- the last checked on this CPU, not proved.

## Round 4: the minimality pass

Reading `bootstrap/` and `ode-base/` once more for what could go found:
- **Bob read binary.bin twice** -- once inside the checker, once to run
  it -- so a store owner could swap the file in between. The checker now
  returns the program it proved, and Bob runs that from memory.
- **Two BLAKE3s:** ode-base carried its own; the root now serves its
  copy to ode-base, so Bob relies on one.
- **The certificate held the binary three ways** (the bytes, their hash,
  and binary.bin) and an input count the spec and binary already fix.
  It now names the binary by hash only.
- **The decoder's step names could collide with input names** (`s0`), so
  such a spec could never be checked. Fixed like the producer's.
- **The referee scored a rejected honest control as a Mallory loss.**
  Controls now carry `EXPECT` (accept) and a rejection fails the run --
  which caught Bob rejecting every G attack after a lookup bug during
  this very pass.
- `RELIANCE` lost a wrapper level; `check_store`, `is_symbol`, and a
  stale docstring left ode-base.
