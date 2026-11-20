# Ode

Ode is a research project in proof-carrying native code. The goal is fast machine code that ships with a
machine-checkable proof that it does what a short, readable contract says. A skeptical user can then check
the proof himself. He does not rely on the author, the compiler or the build for the code doing what the
contract says.

## The idea in one example

Take a hash function. Its author ships three things:

1. The binary: the compiled function, as an ordinary object file.
2. A contract: a few lines saying what the function does. Our BLAKE3 contract is seven lines long. It says
   that the function writes the BLAKE3 hash of `input` into `out`. It requires that `out`, `input` and
   `key` are separate pieces of memory. It bounds the stack the function uses, and it names the processor
   feature the function needs (AVX-512).
3. A proof that the binary satisfies the contract.

The user, whom we call **Bob**, is an auditor who assumes that anyone who touched the code may be mistaken
or hostile. Bob reads the contract and decides whether it is what he wants. Then he runs a **verifier** on
the binary, the contract and the proof. The verifier gives a verdict: it either accepts ("this binary
satisfies this contract") or rejects. Bob has no need to read the implementation.

Three design decisions follow from that picture:

- The verifier checks the bytes that will run. Source code is not what it reads. So the verdict does not
  rely on the compiler, the assembler or the author's tools: whatever they produced is accepted only if
  the proof checks.
- The programmer chooses the machine code, instruction by instruction where speed needs it. Ode's tools
  leave optimizing to the programmer. Their job is to produce the proof.
- Whatever the verdict does rely on should be small and itself checkable. Finding a proof is the clever
  part, and a separate program called the **prover** does it. The verdict does not rely on the prover: the
  verifier checks whatever the prover produces.

[DESIGN.md](DESIGN.md) is the full design.

## Where the project stands (November 18, 2026)

It is a research prototype. Nothing here is ready to protect anything of value.

### What works

One real program is verified from its bytes. It is a one-shot BLAKE3 hash for x86-64 with AVX-512, made
of fourteen functions written in Ode. On a 1 MiB input it runs at 97% of the speed of BLAKE3-Servil's
hand-written assembly. On 16 to 32 KiB inputs it reaches 60%, because one kernel is still missing there.

Twelve smaller functions are verified the same way. Among them are Adler-32, an LZ4 decoder and a UTF-8
validator.

### The main weakness

The verifier that checks those programs is about 3,300 lines of Python that nobody has proved correct. It
is tested and audited, and we attack it ourselves. On November 17 and 18 we found eight ways to make it
accept a wrong binary, and closed them. A verifier that can be fooled defeats the purpose, so this is the
main thing we are working on.

### What we are doing about it

The folder `proof-core/` holds a second, much smaller verifier, written in Lean 4. With it comes a
soundness theorem that Lean checks: if this verifier accepts a function, the function satisfies its
contract, whatever proof it was given. So far it can verify five of the twelve small functions and five
of the fourteen functions of BLAKE3: the two versions of the kernel that compresses one 64-byte block;
`b3l_node_out`, which reads a node record and calls whichever kernel the processor supports; the
16-way kernel, with its loop over the blocks of sixteen chunks, for every number of blocks; and
`b3l_pad`, whose loop writes a padded block byte by byte.
It can follow arithmetic and shuffles on 512-bit registers, loads and stores of those registers
in buffers and on the stack, loads through a table of addresses, and loads of constants from the object
file's read-only data.
[proof-core/README.md](proof-core/README.md) says exactly what its theorem assumes.

Section 13 of DESIGN.md compares the current state with the design, point by point.

## Try it: verify the BLAKE3 example

    cd kcheck
    python3 verify.py b3hashr.o blake3.spec

This needs Python 3 and this repository. Nothing is installed, no SMT solver runs, and no network is used.
In about 25 seconds it prints:

- the contract (seven lines),
- the verdict: `b3l_hashr` in this file meets its public contract, together with the thirteen functions
  it calls,
- the list of files that took part in reaching that verdict: 3,291 lines of Python in fourteen files, and
  a table describing the x86-64 instructions the verifier understands (93 instruction forms, with 150
  byte encodings).

Exit status 0 means the binary was accepted. In these shipped examples the proof is stored inside the
object file; `--proof FILE` reads it from a separate file instead, which is where proofs are moving.

[kcheck/VERIFY.md](kcheck/VERIFY.md) is written for someone verifying: what exactly was established,
what was not, and what the result relies on. Another example:
`python3 verify.py programs/lz4/odelz4.o programs/lz4/lz4.spec`.

## Rebuild it and run the tests

    sh kcheck/make_hash.sh /tmp/out      # rebuilds the shipped b3hashr.o from its Ode sources, byte for byte
    python3 kcheck/gate.py --jobs 16     # the check we run before every merge: under five minutes
    sh tests.sh                          # every test

Rebuilding needs only Python 3: our own assembler, `core/asm.py`, writes each instruction's bytes from the
instruction table. (clang is used only by a test that compares the two assemblers on every function.)

Some tests execute the verified code on a real processor and need x86-64 Linux with AVX-512; elsewhere
they are skipped. The tests of `proof-core/` need Lean's build tool `lake` and are skipped without it.

`kcheck/audit.sh` is a long-running fault-injection test. It flips every single bit of every verified
function, one at a time. Whenever the verifier still accepts the changed function, the changed code is run
on a real processor and compared with a reference implementation. It takes hours.

## What is where

| | |
|---|---|
| `DESIGN.md` | what Ode is for and how it is built; the state today; open decisions |
| `NAMES.md` | names and identities: requirements, the proposal, what the tools do |
| `LESSONS.md` | what the work has taught, October and November 2026 |
| `AGENTS.md` | how the team works, and how to work here |
| `kcheck/` | the tools and the examples (table below); `README.md` there is the dated record of evidence |
| `core/` | the machine, written once as a table: `x86.tab` (one row an instruction form: how it is written, what it does, and under it the ways it is written in bytes) and what reads it (second table below) |
| `proof-core/` | a first small verifier, in Lean 4, with the theorem that its yes is right whatever proof it is handed (`verify_all_sound`); it shows five shipped functions (`ode_common`, `ode_adler32`, `ode_adler32_blocks`, `ode_adler32_blocks4`, and `ode_varint`, which writes its result into memory its caller gives it), a function that calls the first, and the hash's two one-block kernels (AVX-512 and SSE4.1), so far. Its `README.md` says what that rests on. No other folder needs Lean |
| `wide/` | BLAKE3's five kernels in Ode (`one.ode`, `k32.ode`, `p16.ode`), with tests that they assemble to the reference kernels' bytes |
| `lang/` | `odec.py`: Ode source to an object. A function is the instructions its coder chose; `odec.py` expands the source's few fixed forms (a `def`, a `for`), chooses nothing, and has `core/asm.py` write each instruction's bytes by the table (`test_asm.py`: the same bytes as clang gives, for every function of the sources) |
| `reference/blake3-servil/` | BLAKE3-Servil's own kernels and the official test vectors, for comparison |
| `advice/` | numbers about speed, for the coder; no verifier reads this folder and no verdict relies on it. First in it: a test of predicting the 16-way kernel's cycles from uops.info's table |

Inside `kcheck/`, by what a file is relied on for:

| role | files |
|---|---|
| what Bob is given | `VERIFY.md`, `verify.py`, `LANGUAGE.md`; `blake3.spec` and `b3hashr.o`; `programs/NAME/NAME.spec` and `programs/NAME/odeNAME.o` |
| the verifier (relied on) | `check_binary.py`, `programs/check_file.py`, `kdecode.py`, `kfn.py`, `kbyte.py`, `kspec.py`, `ode.py`, `klin.py`, `kterms.py`, `kproof.py`, `kshow.py`, `kends.py`, `varith.py`; and from `core/` (below) the table and the files that read it |
| provers (relied on for nothing) | `kprove.py`, `kguess.py`, `kplace.py`, `kwide.py` |
| makers | `hash.ode` and `programs/NAME/*.ode` (the sources), `kernels.py`, `klink.py`, `make_hash.sh`, `programs/kpack.py`, `proofs/` |
| testers and audits | `refute.py` (looks for an input that breaks a contract), `gate.py`, `test_*.py`, `audit.sh` and the `k*_flip.py` tools, `lemma_audit.py`, `kadversary.py`, `kfile_flip.py`, `audit/` (the last whole audit's output), `backdoor.o` (a wrong binary that must be refused), `varith2.c` (a second verifier of arithmetic proofs) |
| a disassembler's reading, for a test of the decoder | `lift_one.py` |

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
