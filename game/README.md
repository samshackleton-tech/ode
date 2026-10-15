# The adversarial game: Sam, Bob, and Mallory

A test from the relying party's side.

- **Sam** publishes `bootstrap/`: everything Bob relies on for
  *correctness*.
  - `root/` -- `blake3.py`, `domains.py`, and `launch.py`. The launcher reads
    an ode-base into memory, computes its tree hash, compares it with the
    pin, stops on any difference, and runs `bob.py` with every `ode`
    import served from the very bytes it hashed. The root serves its single BLAKE3 implementation and semantic-domain
    registry to the delivered package as `ode.blake3` and `ode.domains`.
  - `game-targets/RELIANCE` -- the domain-separated tree identity of the
    ode-base, and the hashes of the game's two specifications: BLAKE3's
    G, and BLAKE3 of any length (`examples/blake3.sexp`), which Bob asks
    for at 65 bytes.
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

## Kernel-based fragment recipient

A separate recipient uses the same unchanged root launcher with
`kernel-base/`. Its owner pins the package tree, the instruction-encoding
theory, and both the encoding and execution goals in
`bootstrap/kernel-targets/RELIANCE`. All package files, proof files, and
fragment bytes may be delivered by anyone.

```sh
pypy3 game/bootstrap/root/launch.py \
  game/bootstrap/kernel-targets/RELIANCE game/kernel-base examples/proofs g-fragment
pypy3 -m unittest tests.test_kernel_bootstrap
```

The recipient admits the delivered package by its tree hash, checks the
theory and goals against the owner's pins, and verifies both proofs and
the exact fragment bytes. It retains the objects and bytes it read;
verification does not reopen them. Alternative valid proofs are accepted.
Tests reject altered package code before it runs, changed owner claims,
corrupted proofs or bytes, and missing artifacts, with honest controls.

The package includes `kernel.py`, `canon.py`, `proof_cli.py`,
`encoding_cli.py`, `word_literal.py`, and an empty package initializer.
It contains no old symbolic verifier, native runner, or proof producer.
`game/pin_ode_base.py` refreshes both recipient packages and their code
pins together; it preserves the owner's theory, goal, and specification
pins.

Acceptance concerns the declared arithmetic fragment model, not a
callable native function or refinement against Arm's ISA. Correctness
relies on the pinned kernel and readers, the root loader/hash, PyPy and
its standard library, the OS, and hardware. Hash admission fixes code
identity; it does not establish that code's correctness. The package
runs no supplied binary.

File identities and tree identities use separate BLAKE3 derive-key contexts;
specification, theory, and goal identities have their own semantic contexts.
`../DOMAINS.md` documents the policy. A meaning change updates the relevant
domain revision and all dependent pins; old identities are rejected.

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
