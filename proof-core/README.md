# proof-core: a small verifier, with the theorem that its yes is right

This folder is the first cut of the small core that [DESIGN.md](../DESIGN.md) section 7 asks for. It is a
verifier written in Lean 4 that decides by a proof it is handed, and a theorem, checked by Lean, that
whatever proof it is handed, its yes is right. It reads a first part of what the verifier in `kcheck/`
reads: enough for one shipped function with a loop. `kcheck/` is still the verifier a reader uses for the
hash and the other programs.

Lean is the language of this implementation. Nobody needs Lean to use Ode, and the proof a maker ships is
plain text that a verifier in any language can read.

## Try it

    cd proof-core
    lake build                           # the verifier, and every proof of the theorems (Lean 4.34.1)
    python3 lean_verify.py ../kcheck/programs/common/odecommon.o ode_common \
            ../kcheck/programs/common/common.spec proofs/ode_common.proof

It prints the public contract and `shown`. `ode_common` counts the bytes two runs have alike at their
start: 45 instructions, one loop. The proof is 68 lines of text (1,773 bytes), and the verifier decides in
4 ms.

## The theorem

    theorem verify_sound (ctx : Ctx) (p : Program) (proof : List Item) :
        p.code = ctx.code → verdict ctx proof = none → Meets ctx.contract ctx.defs p

`verdict ctx proof = none` is the verifier's yes: of the function's instructions, its contract and the
specification's definitions (`ctx`), by the maker's `proof`. Nothing is asked of the proof: it may be
anything. `Meets` (Contract.lean) says what the contract promises of the code, on the machine of
Machine.lean. From every state at entry in which the caller has done its part:

- the machine runs only instructions of the function;
- it reads only the runs of bytes the contract's arguments name, its own frame, and its return address;
  it writes only its own frame, and that is no more than the contract's `stack` bytes;
- after finitely many instructions it returns to the address its caller left at the stack pointer;
- then the stack pointer is above that address, the registers a callee keeps (rbx, rbp, r12 to r15) are as
  they were, memory outside the frame is as it was, and `rax` holds the value the contract's `returns` has
  by the specification's definitions.

The caller's part (`Contract.pre`): the registers hold numbers below 2^64 and memory holds bytes; `stack`
bytes below the stack pointer are there to use; each run of bytes lies in memory, apart from that frame and
from the return address.

A loop is covered by a place in the proof and induction on the place's number: the verifier shows that the
place's facts hold on first coming there and again on every way round, and that a number the place names is
never below zero and is less each time round.

Lean reports what the theorem depends on: `propext`, `Classical.choice`, `Quot.sound`, the three axioms of
Lean itself (test_sound.py checks this, and that no proof is left open).

## What a `shown` rests on

| | |
|---|---|
| covered by the theorem, so not to be read | the verifier's rules: Core.lean (570 lines of code) and the arithmetic rule of Arithmetic.lean. Everything clever is here or in the prover |
| what the theorem is about: to be read, or relied on some other way | the account: Table.lean (reads `../core/x86.tab`), Machine.lean (what a row's effect does to registers, flags and memory), Contract.lean (what a contract and a definition mean, `Meets`). 420 lines of code |
| that the proofs are proofs | Lean's kernel, or any other checker of Lean's proofs |
| compared by tests, not proved | Machine.lean against `../core/conc.py` on every row it gives a meaning (48 rows, from random states: test_machine.py). `conc.py` is what three processors were compared with, row by row (`../core/cross.py`). What a definition means (`evalSpec` in Contract.lean) against `../kcheck/ode.py`, which the reader's tester takes it from: 1,500 uses of ten definitions and 4,000 random expressions (test_spec.py). The arithmetic rule against `../kcheck/varith.py` on the 7,649 proofs the shipped files carry (test_arith.py) |

Not covered by the theorem, and relied on today:

- **From the file's bytes to the rows.** The theorem is about a function given as rows of the table.
  `statement.py` has `../kcheck/kdecode.py` read the rows from the file's bytes (by the table's ways of
  writing a row in bytes), and those files are Python. The reading of the ELF file is there too.
- **From the specification's text to the definitions.** `statement.py` has `../kcheck/ode.py` read the
  specification and writes the contract and the definitions as the lines Main.lean reads.
- **Reader.lean**, which reads those lines and the proof's and takes each instruction for the first row of
  the table it is an instance of; and the program Lean's compiler makes of the verifier. The theorem is
  about the function `verdict`, as Lean's logic defines it.
- **That the table is true of processors.** That is `cross.py`'s comparison, and it does not run a return:
  what a return does (it takes the address at the stack pointer) is said in Machine.lean.

A proof can add nothing to what is to be shown: the statement and the proof are two files, and a line of
the statement's kinds in the proof is refused.

## What it reads so far

A function whose instructions are rows over the general registers, the two flags, and memory of 1, 4 and
8 bytes; with jumps and one loop place; no calls. A contract whose arguments are numbers and runs of bytes
that are only read, with `returns` and `stack`. Definitions that are one expression: numbers, names,
arithmetic and comparison, `if`, a byte of a run, `len`, and uses of definitions (which may use
themselves). A difference has a value only where it is not below zero, as in the language, and the
verifier asks for that to be shown wherever it meets one.

`statement.py` refuses a contract with any other line, so that none is dropped: `requires`, `ensures`,
`writes`, `needs`, `calls`; and a contract that promises that the trace does not depend on some run's
bytes, since the account here says nothing of the trace. (`ode_common`'s contract allows the trace to
depend on both runs.) Vector registers, calls by contract, memory that is written for the caller, and
more than one place are the next parts.

## The proof

A proof is text, one line a thing, in the order the verifier comes to need it:

    place 52                      where the loop's place is, by the instruction's offset
    name i r13                    names for what registers hold there
    fact (bin <= (name i) (name n))
    keep rcx rdx rbx rsp …        registers that hold there what they held on first coming there
    decreases (bin - (name n) (name i))
    t open 1                      open this use of a definition
    t live / t dead               a way a jump can go: some input takes it / none does (then why, by arithmetic)
    r 0 0 1 …  /  s 0 1 2 1 1  /  q      a proof of arithmetic: rows it starts from, steps that add two rows up

The verifier replays the instructions itself by the table and opens definitions itself; the proof carries
only what would otherwise be searched for. A proof of arithmetic starts from rows the verifier already
holds and adds them up, with whole multipliers, to a row that says a number below zero is at least zero.

`prove.py` is the prover, relied on for nothing: it runs the verifier, which says what it needs next, finds
an answer (the arithmetic by elimination), and runs it again: 101 runs and half a second for `ode_common`.

## What was measured (November 18, 2026)

| | |
|---|---|
| `ode_common`: the proof | 68 lines, 1,773 bytes: the place 8 lines, 7 proofs of arithmetic |
| the verifier's time on it | 4 ms |
| wrong versions | 18 changes of one place in the code, the specification, the contract or the place: each refused, and the prover finds no proof for any. Every line of the proof left out or changed: refused, but for two rows an arithmetic proof starts from and does not use |
| the arithmetic rule | all 7,649 proofs of arithmetic the shipped files carry (17,505 steps) add up, in 0.3 s; of 3,000 changed proofs Lean and `varith.py` say the same, proof by proof |
| the machine | 48 rows, 60 instances a row in the tests (14,400 in a longer run): Machine.lean and `conc.py` leave the same registers, flags, memory and place to go on at |
| size | the account 420 lines of code; the verifier 729 (Core.lean 570, Arithmetic.lean 159 with its proofs); the reader of lines 100; the proofs of the theorems 3,221 |

## The files

| | |
|---|---|
| the account | `Table.lean`, `Machine.lean`, `Contract.lean` |
| the verifier | `Core.lean`; `Arithmetic.lean` (the arithmetic rule and `refutes_sound`); `Reader.lean` and `Main.lean` (the program `odeverify TABLE STATEMENT PROOF`) |
| the theorem | `SoundLin.lean` (arithmetic on rows), `SoundState.lean` (what the verifier's state says of the machine's), `SoundStep.lean` (one statement of an effect), `SoundSpec.lean` (the specification on symbols), `SoundPlace.lean` (a place), `SoundTop.lean` (paths, induction, `verify_sound`) |
| what is to be shown (relied on) | `statement.py` |
| for a reader | `lean_verify.py`; `proofs/ode_common.proof` |
| the prover (relied on for nothing) | `prove.py` |
| tests | `test_sound.py`, `test_verify.py`, `test_machine.py`, `test_spec.py`, `test_arith.py`; `MachineMain.lean`, `SpecMain.lean` and `ArithMain.lean` are the programs the last three run |

The tests skip where Lean's `lake` is not installed.
