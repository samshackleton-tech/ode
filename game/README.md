# The adversarial game: Sam, Bob, and Mallory

A test from the relying party's side.

- **Sam** publishes `bootstrap/`: everything Bob relies on for
  *correctness*.
  - `root/` -- `blake3.py` and `launch.py`, 235 lines. The launcher reads
    an ode-base into memory, computes its tree hash, compares it with the
    pin, stops on any difference, and runs `bob.py` with every `ode`
    import served from the very bytes it hashed. The root's BLAKE3 is the
    only one: it serves it to ode-base as `ode.blake3`.
  - `game-targets/RELIANCE` -- about 260 bytes: the tree hash of the
    ode-base, and the hashes of the game's two specifications (BLAKE3's
    G, and BLAKE3 of a 65-byte message).
- **Anyone**, Mallory included, may deliver what Bob needs only for
  *availability*: `ode-base/` (the checker, reader, semantics, AArch64
  model and runner, and `bob.py`), admitted by tree hash, and the
  specifications, fetched by hash from the store. A wrong copy is a
  reject, never a wrong answer.
- **Mallory** supplies the store: binaries (`<hash>.bin`), `certificate.sexp`, and
  the definitions it names. He may change anything in it, deliver his own
  ode-base, and knows every input Bob will use.
- **Bob** follows `ode-base/bob.py`: require the certificate to be about
  the pinned spec, check it, and run exactly the program proved -- W32 by
  interpretation, AArch64 natively.

Mallory wins when Bob prints `ACCEPT` and then a wrong answer; a control
(`EXPECT`) that Bob rejects fails the run too. The inputs are public
because the claim is universal: a kernel wrong on one known input is
the real-world attack.

```sh
pypy3 game/make_attacks.py              # regenerate every attack (one call each, with NOTES)
pypy3 game/referee.py game/attacks/*    # replay them all
pypy3 game/pin_ode_base.py              # after changing ode/: refresh ode-base and its pin
```

## What the game has found

Each became a fix and a permanent test:

| Finding | Fix |
|---|---|
| The checkers never opened the binary file, the one that runs | bind it by hash |
| Bob printed ACCEPT, then crashed, on out-of-domain inputs | reject inputs outside the domain first |
| An all-digit hex string read as an integer in canonical form | byte strings are `#hex`; symbols never start with a digit |
| The producer's fresh names collided with a spec input named `t0` | fresh prefixes no spec name starts with |
| The decoder's step names could collide with inputs named `s0` | the same, in the decoder |
| Bob read the binary file twice, so its owner could swap it between check and run | the checker returns the program it proved; Bob runs that |
| The referee counted a rejected honest control as a Mallory loss | controls carry `EXPECT` and fail the run |

Calls by certificate met six attacks -- a wrong compression under the
right claim, an honest certificate for a different spec of the same
shape, swapped arguments, a withheld callee, and two controls (one
calling a proved AArch64 compression from W32 glue) -- and gave up no
new finding.

Besides the corpus, 8,000 randomized trials found no unsound symbolic
rewrite, and the AArch64 model is cross-checked against the CPU.

## What the bootstrap itself relies on

Running the root relies on PyPy, its standard library (`os`, `re`,
`importlib`, `ctypes`), the operating system (files, processes, mapping
executable pages), and the hardware -- in particular that the CPU
executes the eight AArch64 forms as `ode/a64.py` models them, checked on
random states by `tests/test_a64.py`, not proved. None of these is
checked here; the real-machine milestone (SPEC s1, R4 and R5) is where
they shrink.
