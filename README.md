# Ode

Ode is a way to write fast native code together with a proof that its bytes meet a contract, so that the
person who depends on the code can verify it for himself while relying only on a short, named list of things.

A maker ships three things: a binary, a proof carried inside it, and a specification. Bob, the auditor,
reads a short contract ("this function writes the BLAKE3 hash of the input to `out`, reads and writes
nothing else, and uses this much stack"), and runs his verifier on the binary. The compiler, the prover and
the maker are relied on for nothing: whatever they produced is accepted only where the verifier shows the
bytes meet the contract. The coder chooses the machine code, instruction by instruction where speed needs
it; the tools automate its proof. [DESIGN.md](DESIGN.md) is the whole design.

**State, November 17, 2026: a research prototype.** One real program is verified from its bytes: the
one-shot BLAKE3 hash for x86-64 with AVX-512, fourteen functions written in Ode, at 97% of BLAKE3-Servil's
speed for a megabyte and 60% at 16 to 32 KiB. Twelve smaller functions (Adler-32, LZ4, UTF-8, base-64 and
others) are verified the same way. **The verifier itself is unverified Python**, tested and audited; six
ways to have it accept a wrong binary were found by reading on November 17 and closed. Making the part Bob
relies on small and provable is the work ahead. Section 13 of DESIGN.md sets the state against the design,
line by line.

## Verify the first example

    cd kcheck
    python3 verify.py b3hashr.o blake3.spec

Python 3, this folder and `core/` beside it are all it needs: nothing is installed, no solver runs, no network is used. In
about 25 seconds it prints the public contract (seven lines), the verification ("`b3l_hashr` in this file
meets its public contract, with all it calls: 14 functions, from the file's bytes"), and the files that ran
to reach it (3,291 lines of Python in fourteen files, and the table of instructions: 93 rows, and under them
150 ways of writing them in bytes). Exit status 0
means shown.
[kcheck/VERIFY.md](kcheck/VERIFY.md) is the page for a reader: what is shown, what is left unshown, and
what you rely on. Another program: `python3 verify.py programs/lz4/odelz4.o programs/lz4/lz4.spec`.

## Make it again, and test it

    sh kcheck/make_hash.sh /tmp/out      # the shipped b3hashr.o from its Ode sources, byte for byte
    python3 kcheck/gate.py --jobs 16     # the check before a merge: under five minutes
    sh tests.sh                          # every test file

Making needs Python 3 and nothing else: `core/asm.py` writes a function's bytes by the instruction table. (clang
is used by tests only: `lang/test_asm.py` compares the two assemblers on every function.) The gate and some tests run code on a processor and need
x86-64 Linux with AVX-512; they skip elsewhere. `kcheck/audit.sh` changes every bit of every verified function in turn and has a processor
judge each change the verifier accepts: hours, run in the background.

## What is where

| | |
|---|---|
| `DESIGN.md` | what Ode is for and how it is built; the state today; open decisions |
| `NAMES.md` | names and identities: requirements, the proposal, what the tools do |
| `LESSONS.md` | what the work has taught, October and November 2026 |
| `AGENTS.md` | how the team works, and how to work here |
| `kcheck/` | the tools and the examples (table below); `README.md` there is the dated record of evidence |
| `core/` | the machine, written once as a table: `x86.tab` (one row an instruction form: how it is written, what it does, and under it the ways it is written in bytes) and what reads it (second table below) |
| `wide/` | BLAKE3's five kernels in Ode (`one.ode`, `k32.ode`, `p16.ode`), with tests that they assemble to the reference kernels' bytes |
| `lang/` | `odec.py`: Ode source to an object. A function is the instructions its coder chose; `odec.py` expands the source's few fixed forms (a `def`, a `for`), chooses nothing, and has `core/asm.py` write each instruction's bytes by the table (`test_asm.py`: the same bytes as clang gives, for every function of the sources) |
| `reference/blake3-servil/` | BLAKE3-Servil's own kernels and the official test vectors, for comparison |

Inside `kcheck/`, by what a file is relied on for:

| role | files |
|---|---|
| what Bob is given | `VERIFY.md`, `verify.py`, `LANGUAGE.md`; `blake3.spec` and `b3hashr.o`; `programs/NAME/NAME.spec` and `programs/NAME/odeNAME.o` |
| the verifier (relied on) | `check_binary.py`, `programs/check_file.py`, `kdecode.py`, `kfn.py`, `kbyte.py`, `kspec.py`, `ode.py`, `klin.py`, `kterms.py`, `kproof.py`, `kshow.py`, `kends.py`, `varith.py`; and from `core/` (below) the table and the files that read it |
| provers (relied on for nothing) | `kprove.py`, `kguess.py`, `kplace.py`, `kwide.py` |
| makers | `hash.ode` and `programs/NAME/*.ode` (the sources), `kernels.py`, `klink.py`, `make_hash.sh`, `programs/kpack.py`, `proofs/` |
| testers and audits | `refute.py` (looks for an input that breaks a contract), `gate.py`, `test_*.py`, `audit.sh` and the `k*_flip.py` tools, `lemma_audit.py`, `kadversary.py`, `kfile_flip.py`, `audit/` (the last whole audit's output), `backdoor.o` (a wrong binary that must be refused), `varith2.c` (a second verifier of arithmetic proofs) |
| earlier pieces, loaded by no verification | `kcheck.py`, `kremove.py`, `lift_one.py` |

Inside `core/`:

| role | files |
|---|---|
| relied on: what each instruction does, and what bytes are one | `x86.tab` (93 rows, 150 ways of writing them in bytes), `table.py` (reads it), `step.py` (does a row's effect on the verifier's machine: a rule on symbols for each primitive, none about one instruction), `encode.py` (writes an instance's bytes in one of its row's ways: one byte string), `decode.py` (reads the bytes at a place as an instance only if `encode.py` writes those very bytes for it; the part of it that proposes what the bytes might be is relied on for nothing) |
| the rules, written down | `RULES.md`: every rule the verifier follows, with why it is right: which instruction the bytes are, what a row concludes, memory in regions, calls by contract, paths and splits, loop places and lemmas, returns, traces, and whole-file checks |
| maker (relied on for nothing) | `asm.py`: the assembler. An instruction of an Ode source becomes the bytes `encode.py` writes for its row (the shortest way; a jump short where it reaches); what comes out is read back by the verifier like any other bytes |
| testers | `conc.py` (each primitive's meaning on numbers), `cross.py` (every row, as an assembler writes it and in each way the table writes its bytes, run on this machine's processor from random states and compared), `decoder.py` (what an assembler writes for each row's instances is read as that row), `meaning.py` (every rule on symbols against the meaning on numbers), `test_core.py` |

## Where this came from

- **Ode 0.1** (October 2026) is this repository's tag `v0.1.0`: a proof kernel for equations, a symbolic
  verifier for a bytecode and an AArch64 subset, and the design pages this one grew from.
- **The present tools** were built from November 11 to 17, 2026 inside BLAKE3-Servil's repository (fork
  `samshackleton-tech/BLAKE3`, branch `experiment/sam-wide-model`, `tools/verify/machine/`) and moved here
  from its commit `dca7275f`. The Lean experiments that came before them stay there.

## Licence

Copyright (c) the Ode contributors.

You may use Ode under the terms of any of these four Free and Open Source Software licences, at your
choice (the same four as [smalloc](https://github.com/zooko/smalloc)):

* MIT license ([LICENSE-MIT](LICENSE-MIT))
* Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE))
* Transitive Grace Period Public Licence 1.0 ([LICENSE-TGPPL](LICENSE-TGPPL)):
  *Licensed under the Transitive Grace Period Public Licence version 1.0*
* Bootstrap Open Source Licence v1.0 ([LICENSE-BOSL.txt](LICENSE-BOSL.txt)):
  *Licensed under the Bootstrap Open Source Licence version 1.0*

The files under `reference/blake3-servil/` are BLAKE3-Servil's, kept for comparison, and carry the licence
texts they came with.
