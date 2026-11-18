# proof-core: a small verifier, with the theorem that its yes is right

This folder is the first cut of the small core that [DESIGN.md](../DESIGN.md) section 7 asks for. It is a
verifier written in Lean 4 that decides by a proof it is handed, and a theorem, checked by Lean, that
whatever proof it is handed, its yes is right. It reads a first part of what the verifier in `kcheck/`
reads: enough for four shipped functions (three of them the Adler-32 checksum: plain, in blocks, and four
bytes a turn), and for a function that calls one of them.
`kcheck/` is still the verifier a reader uses for the hash and the other programs.

Lean is the language of this implementation. Nobody needs Lean to use Ode, and the proof a maker ships is
plain text that a verifier in any language can read.

## Try it

    cd proof-core
    lake build                           # the verifier, and every proof of the theorems (Lean 4.34.1)
    python3 lean_verify.py ../kcheck/programs/common/common.spec proofs/ode_common.proof \
            ../kcheck/programs/common/odecommon.o:ode_common
    python3 lean_verify.py examples/equal/equal.spec proofs/ode_equal.proof \
            ../kcheck/programs/common/odecommon.o:ode_common examples/equal/odeequal.o:ode_equal
    python3 lean_verify.py ../kcheck/programs/adler32/adler32.spec proofs/ode_adler32_blocks.proof \
            ../kcheck/programs/adler32/odeadler32.o:ode_adler32_blocks
    python3 lean_verify.py ../kcheck/programs/adler32/adler32.spec proofs/ode_adler32_blocks4.proof \
            ../kcheck/programs/adler32/odeadler32.o:ode_adler32_blocks4
    python3 lean_verify.py examples/low/low.spec proofs/ode_low.proof examples/low/odelow.o:ode_low
    python3 lean_verify.py ../kcheck/programs/adler32/adler32.spec proofs/ode_adler32.proof \
            ../kcheck/programs/adler32/odeadler32.o:ode_adler32

Each prints the contracts and `shown`. `ode_common` counts the bytes two runs have alike at their start:
45 instructions, one loop. Its proof is 55 lines of text (646 bytes), and the verifier decides in 4 ms.
`ode_equal` says whether two runs are the same by calling `ode_common`: ten instructions, and nine more
lines of proof. The verifier shows `ode_common` first and then takes the call by its contract alone.
`ode_adler32` is the Adler-32 checksum: 55 instructions, one loop, two sums each kept below 65521. Its
proof is 265 lines (3 kB), most of it the arithmetic of remainders, and the verifier decides in 5 ms.
`ode_adler32_blocks` is the same checksum taken in blocks of at most 5552 bytes, the sums reduced once a
block by shifts and masks: 116 instructions, a loop inside a loop. Its proof is about 1,400 lines (19 kB),
and the verifier decides in 77 ms. `ode_adler32_blocks4` takes the bytes of a block four a turn, and is the
one of the three that is fast (87% of the usual C): 164 instructions, three loops. Its proof is about 2,100
lines (27 kB), and the verifier decides in 188 ms.

## The theorem

    theorem verify_all_sound (world : List Program) (defs : List Def) (fns : List Fn) :
        Linked world fns → verdictAll defs fns = none →
        ∀ f ∈ fns, ∃ p, findProgram world f.name = some p ∧ Meets world f.contract defs p

`verdictAll defs fns = none` is the verifier's yes: of the functions of a statement (`fns`: each one's
name, instructions and contract, with the maker's proof for it) and the specification's definitions
(`defs`). Nothing is asked of the proofs: they may be anything. The theorem says that every function of the
statement then meets its contract. `Meets` (Contract.lean) says what a contract promises of code, on the
machine of Machine.lean. From every state at entry in which the caller has done its part:

- the machine runs only instructions of the function and of the functions it calls;
- it reads only the runs of bytes the contract's arguments name, its own frame, and its return address;
  it writes only its own frame, and that is no more than the contract's `stack` bytes. A function it calls
  touches no more than that either;
- after finitely many instructions it returns to the address its caller left at the stack pointer;
- then the stack pointer is above that address, the registers a callee keeps (rbx, rbp, r12 to r15) are as
  they were, memory outside the frame is as it was, `rax` holds the value the contract's `returns` has by
  the specification's definitions, and every register holds a number below 2^64.

The caller's part (`Contract.pre`): the registers hold numbers below 2^64; `stack` bytes below the stack
pointer are there to use; each run of bytes lies in memory, apart from that frame and from the return
address, and holds bytes; the function's code lies in memory.

`Linked world fns` is the one thing taken as given. `world` is the functions there are when the code runs.
`Linked` says that under each name of the statement, that is the function with the instructions the
statement gives, lying in memory. A call in the account goes to the function of the name called. That a
linker makes it so is not shown here (nor in `kcheck/`: [VERIFY.md](../kcheck/VERIFY.md) says the same).

**A loop** is covered by a place in the proof and induction on the place's number. Where a path first
comes to a place, the verifier shows the place's facts and goes on from a general state: the registers the
place keeps and the frame as they were, every other register any number, and what the path knew of the
unknowns it had, which are what they were. Each way round to the place is shown to keep what the place
keeps and its facts, with the place's number, never below zero, less than it was. A function may have
several places. A place inside another's loop is come to afresh each time round the outer loop, with what
is known then; a way from it back to the outer place is shown as a way round the outer loop is.

**A call** is taken by the contract of the function called, and by nothing else. That function must stand
earlier in the statement, where the verifier has shown it: so nothing is assumed of any function, no
function calls itself, and there is no ring of calls. At the call the verifier shows what the called
function's contract asks of its caller (`Contract.pre` again, now the caller's duty):

- the return address and the called function's frame fit in what is left of this function's own frame;
- each run of bytes handed over is one of the runs this function was given, whole;

and it goes on with only what that contract leaves: the registers a callee keeps, memory outside the
called function's frame, and in `rax` the value the contract says. The other registers and the flags are
unknown after a call. The theorem for one function (`verify_sound`) is about a function whose callees meet
their contracts; `verify_all_sound` follows by going through the statement in its order.

Lean reports what the theorems depend on: `propext`, `Classical.choice`, `Quot.sound`, the three axioms of
Lean itself (test_sound.py checks this, the statements above, and that no proof is left open).

## What a `shown` rests on

| | |
|---|---|
| covered by the theorem, so not to be read | the verifier's rules: Core.lean (706 lines of code) and the arithmetic rule of Arithmetic.lean. Everything clever is here or in the prover |
| what the theorem is about: to be read, or relied on some other way | the account: Table.lean (reads `../core/x86.tab`), Machine.lean (what a row's effect does to registers, flags and memory; what a call and a return do), Contract.lean (what a contract and a definition mean, `Meets`). 442 lines of code |
| that the proofs are proofs | Lean's kernel, or any other checker of Lean's proofs |
| compared by tests, not proved | Machine.lean against `../core/conc.py` on every row it gives a meaning (48 rows, from random states: test_machine.py). `conc.py` is what three processors were compared with, row by row (`../core/cross.py`). What a definition means (`evalSpec` in Contract.lean) against `../kcheck/ode.py`, which the reader's tester takes it from: 2,100 uses of fourteen definitions, 4,000 random expressions, and 300 places of Adler-32's two sequences as `statement.py` writes them (test_spec.py). The arithmetic rule against `../kcheck/varith.py` on the 7,649 proofs the shipped files carry (test_arith.py) |

Not covered by the theorem, and relied on today:

- **From the file's bytes to the rows.** The theorem is about functions given as rows of the table.
  `statement.py` has `../kcheck/kdecode.py` read the rows from the file's bytes (by the table's ways of
  writing a row in bytes), and those files are Python. The reading of the ELF file is there too, and so is
  the name of a function called.
- **From the specification's text to the definitions.** `statement.py` has `../kcheck/ode.py` read the
  specification and writes the contracts and the definitions as the lines Main.lean reads. A sequence it
  writes as the definition it is: `s[0] = E`, `s[i + 1] = F` becomes "at place 0, E; at place k, F of the
  place before".
- **Reader.lean**, which reads those lines and the proof's and takes each instruction for the first row of
  the table it is an instance of; and the program Lean's compiler makes of the verifier. The theorem is
  about the function `verdictAll`, as Lean's logic defines it.
- **That the table is true of processors.** That is `cross.py`'s comparison. It runs no call and no
  return: what those two do (a call writes the address to come back to below the stack pointer; a return
  takes the address at the stack pointer) is said in Machine.lean.
- **The link step** (`Linked`, above).

A proof can add nothing to what is to be shown: the statement and the proof are two files, and a line of
the statement's kinds in the proof is refused. The one string in a statement that comes from the maker is
the name of a function called; a name that is not one plain word is refused by the reader of code, and a
line with a line break in it by `statement.py`.

## What it reads so far

Functions whose instructions are rows over the general registers, the two flags, and memory of 1, 4 and
8 bytes; with jumps, places of loops (several a function, one loop inside another), and calls of functions
of the same statement. Contracts
whose arguments are numbers and runs of bytes that are only read, with `returns` and `stack`. Definitions
that are one expression: numbers, names, arithmetic and comparison, a remainder and a quotient by a number,
`if`, a byte
of a run, `len`, and uses of definitions (which may use themselves); and sequences. A use of a definition
that is met while another is opened, and whose value nothing holds, is opened in turn where the proof says
so, to eight deep. A difference has a
value only where it is not below zero, as in the language, and the verifier asks for that to be shown
wherever it meets one. Of the rows that compute, it has rules for adding, subtracting, comparing, shifting
left by a number of the table, shifting right by one (the quotient by a power of two), an and with one
less than a power of two (the remainder by it), and the low half and the low byte of a register (the
remainders by 2^32 and by 256: `mov ecx, esi`, `movzx eax, dil`). The quotient and the remainder of one number by one divisor
are found once: a second shift of the same number gives the same unknown.

`statement.py` refuses a contract with any other line, so that none is dropped: `requires`, `ensures`,
`writes`, `needs`, `calls`; and a contract that promises that the trace does not depend on some run's
bytes, since the account here says nothing of the trace. (The two contracts here allow the trace to depend
on both runs.) It refuses a specification with a constant, a layout or a lemma in the same way.

Where it says "not shown" of something true, so far:

- a run of bytes is handed to a called function only whole (the same start, the same count);
- what a called function returns is known as the value of one use of a definition (`common(a, b)`). It
  serves where the caller's contract comes to a use shown to be the same: of that definition, with the
  same things. A callee's contract that says the same by another definition is not shown;
- an and with any other number, an or, and a shift by a register have no rule;
- of the rows that set the low half of a register, an or (`or eax, ecx`), a read of four bytes, and the
  rows that set the low byte alone (`mov al, 1`) have no rule;
- nothing may be written below the stack pointer.

Vector registers and memory that is written for the caller are the next parts.

## The statement and the proof

What is to be shown is text, written by `statement.py` from the files' bytes and the specification:

    fn ode_common                 a function, then its instructions and its contract
    i 0 1 .push .rbx              (an instruction: where it starts and ends, and its row)
    arg a bytes n
    returns (call common (name a) (name b))
    stack 40
    fn ode_equal                  the next function: it may call those before it
    …
    def common a b = (call alike (name a) (name b) (num 0))        the definitions, for all of them

A proof is text too, one line a thing, in the order the verifier comes to need it:

    for ode_common                what follows is for that function
    place 52                      where a loop's place is, by the instruction's offset (there may be several)
    name i r13                    names for what registers hold there
    fact (bin <= (name i) (name n))
    keep rcx rdx rbx rsp …        registers that hold there what they held when the path first came there
    decreases (bin - (name n) (name i))
    t open 1                      open this use of a definition (of those in the facts held and the fact asked)
    t open                        where a number is needed and a use of a definition is met: open that use
    t held 0 / t carry 0          a value the verifier holds for one use of a definition serves another use,
                                  shown to be the same (of one definition, with numbers shown equal)
    t live / t dead               a way a jump can go: some input takes it / none does (then why, by arithmetic)
    t lt / t eq / t gt            which of two numbers is the greater (then why, by arithmetic)
    p 0 3 17  /  s 0 1 2 1 1  /  q       a proof of arithmetic: the rows it starts from, by their numbers
                                  among the rows the verifier holds; steps that add two rows up; the end

The verifier replays the instructions itself by the table and opens definitions itself; the proof carries
only what would otherwise be searched for. A proof of arithmetic starts from rows the verifier already
holds and adds them up, with whole multipliers, to a row that says a number below zero is at least zero.
The call in `ode_equal` needs no line of proof of its own.

`prove.py` is the prover, relied on for nothing: it runs the verifier, which says what it needs next, finds
an answer (the arithmetic by elimination, the equalities first), and runs it again: 47 runs and a fifth of a
second for `ode_common`, 16 runs more for `ode_equal`, 763 runs and 20 seconds for `ode_adler32_blocks`,
2,206 runs and 81 seconds for `ode_adler32_blocks4`.

## What was measured (November 18, 2026)

| | |
|---|---|
| `ode_common`: the proof | 55 lines, 646 bytes: the place 8 lines, 7 proofs of arithmetic |
| `ode_equal`, which calls it: its part of the proof | 9 lines, 77 bytes (the two together: 65 lines, 723 bytes; the statement 2,262 bytes) |
| `ode_adler32`: the proof | 265 lines, 3 kB: the place 11 lines, 39 proofs of arithmetic (the prover's elimination does not give the same proof every run); found in 204 runs of the verifier, 1.0 s |
| `ode_adler32_blocks` (116 instructions, two loops): the proof | about 1,400 lines, 19 kB: two places (24 lines), 174 proofs of arithmetic; found in 763 runs of the verifier, 20 s. (It was 135 kB while a proof of arithmetic wrote out the rows it starts from; it names them by number now) |
| `ode_adler32_blocks4` (164 instructions, three loops): the proof | about 2,100 lines, 27 kB: three places (36 lines), 266 proofs of arithmetic, 12 uses of definitions opened where they are met; found in 2,206 runs of the verifier, 81 s |
| the verifier's time | 4 ms for `ode_common`; 4 ms for it and `ode_equal` together; 5 ms for `ode_adler32`; 77 ms for `ode_adler32_blocks`; 188 ms for `ode_adler32_blocks4` |
| wrong versions of `ode_common` | 18 changes of one place in the code, the specification, the contract or the place: each refused, and the prover finds no proof for any. Every line of the proof left out or changed (85 trials): refused |
| wrong versions of `ode_adler32` | 19 changes of one place in the code (another modulus, a sum not reduced, the shift by 15, …), the specification, the contract or the place: none shown, and the prover finds no proof for any in four times the runs it needs for the right one. Every line of the proof left out, and 167 changed: refused |
| wrong versions of `ode_adler32_blocks` | 14 changes of one place in the code (a shift by 15, a mask of 17 bits, the high part counted 8 times, a sum not reduced, …), the specification, the contract or the places (a place that does not keep the block's end, a number that does not decrease): none shown, and the prover finds no proof for any within the runs, and one and a half times the time, of the right one. Of every seventh line of the proof left out or changed (343 trials): each refused |
| wrong versions of `ode_adler32_blocks4` | 4 changes of one place (four bytes taken where three are left, the third byte taken for the second, three bytes gone on after four are taken, the specification's second sum by the first sum of one place before): none shown, and the prover finds no proof for any within the runs, and three quarters of the time, of the right one. Of every eleventh line of the proof left out or changed (326 trials): each refused |
| the low half and the low byte (`ode_low` of `examples/low/`: 4 instructions) | the proof 528 bytes, found in 8 runs of the verifier, verified in 3 ms; 4 changes of the code and 4 of the contract (the whole number for its low half, the other number's low byte, 7 bits for 8, …): none shown, and no proof found; each of the proof's lines left out: refused |
| a quotient in a specification (`ode_eighth` of `examples/low/`: a shift right by three, against `a / 8`) | the proof 158 bytes; 3 changes of the code and 3 of the contract (a shift by two, a quotient by nine, the remainder for the quotient, …): none shown, and no proof found; each of the proof's lines left out: refused |
| wrong versions of the caller | 11 changes of the caller's code (the count kept in a register a call may change, a run not handed over whole, the stack pointer moved, what a call leaves in rcx used, …) and 5 of the contracts: none shown, no proof found, and for each the test names what the verifier then lacks or refuses. The caller before its callee, a function that calls itself, a callee left out, two functions of one name: refused. Two other ways of writing the caller and two of writing its contract: shown |
| the arithmetic rule | all 7,649 proofs of arithmetic the shipped files carry (17,505 steps) add up, in 0.3 s; of 3,000 changed proofs Lean and `varith.py` say the same, proof by proof |
| the machine | 48 rows, 60 instances a row in the tests (14,400 in a longer run): Machine.lean and `conc.py` leave the same registers, flags, memory and place to go on at |
| size | the account 442 lines of code; the verifier 911 (Core.lean 752, Arithmetic.lean 159 with its proofs); the reader of lines 117; the proofs of the theorems 4,122 |

## The files

| | |
|---|---|
| the account | `Table.lean`, `Machine.lean`, `Contract.lean` |
| the verifier | `Core.lean`; `Arithmetic.lean` (the arithmetic rule and `refutes_sound`); `Reader.lean` and `Main.lean` (the program `odeverify TABLE STATEMENT PROOF`) |
| the theorems | `SoundLin.lean` (arithmetic on rows), `SoundState.lean` (what the verifier's state says of the machine's), `SoundStep.lean` (one statement of an effect), `SoundSpec.lean` (the specification on symbols), `SoundPlace.lean` (a place), `SoundCall.lean` (a call), `SoundTop.lean` (paths and places: `explore_sound`, by induction on a place's number; `verify_sound`, `verify_all_sound`) |
| what is to be shown (relied on) | `statement.py` |
| for a reader | `lean_verify.py`; `proofs/ode_common.proof`, `proofs/ode_equal.proof`, `proofs/ode_adler32.proof`, `proofs/ode_adler32_blocks.proof`, `proofs/ode_adler32_blocks4.proof`, `proofs/ode_low.proof`, `proofs/ode_eighth.proof`; `examples/equal/` and `examples/low/` (a source, its specification, and the object the source makes); `examples/adler32/adler32.places`, `blocks.places` and `blocks4.places` (the places the prover starts from) |
| the prover (relied on for nothing) | `prove.py` |
| tests | `test_sound.py`, `test_verify.py`, `test_call.py`, `test_adler.py`, `test_blocks.py`, `test_blocks4.py`, `test_low.py`, `test_machine.py`, `test_spec.py`, `test_arith.py`; `MachineMain.lean`, `SpecMain.lean` and `ArithMain.lean` are the programs the last three run |

The tests skip where Lean's `lake` is not installed.
