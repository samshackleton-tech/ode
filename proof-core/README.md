# proof-core: a small verifier with a machine-checked soundness theorem

[DESIGN.md](../DESIGN.md) section 7 asks for a small core that an auditor can trust for stated reasons.
This folder is the first version of it. It contains:

- a **verifier**, written in Lean 4. It takes a compiled function, a contract and a proof, and either
  accepts or rejects;
- a **soundness theorem**, checked by Lean: if the verifier accepts, the function satisfies its contract.
  The theorem holds for every possible proof input, so a wrong or malicious proof cannot make the verifier
  accept a wrong function.

It is not finished. Today it handles a subset of what the Python verifier in `kcheck/` handles. That is
enough for five of the twelve small shipped functions, and for a function that calls one of them. It does
not yet handle any function of the BLAKE3 hash. For the hash and the other programs, `kcheck/` is still
the verifier to use.

Lean is how this version is implemented. Nobody needs Lean in order to use Ode: the proof that an author
ships is a plain text file, and a verifier for it can be written in any language.

## Try it

    cd proof-core
    lake build                           # builds the verifier and checks the theorems (Lean 4.34.1)
    python3 lean_verify.py ../kcheck/programs/common/common.spec proofs/ode_common.proof \
            ../kcheck/programs/common/odecommon.o:ode_common
    python3 lean_verify.py examples/equal/equal.spec proofs/ode_equal.proof \
            ../kcheck/programs/common/odecommon.o:ode_common examples/equal/odeequal.o:ode_equal
    python3 lean_verify.py ../kcheck/programs/adler32/adler32.spec proofs/ode_adler32.proof \
            ../kcheck/programs/adler32/odeadler32.o:ode_adler32
    python3 lean_verify.py ../kcheck/programs/adler32/adler32.spec proofs/ode_adler32_blocks.proof \
            ../kcheck/programs/adler32/odeadler32.o:ode_adler32_blocks
    python3 lean_verify.py ../kcheck/programs/adler32/adler32.spec proofs/ode_adler32_blocks4.proof \
            ../kcheck/programs/adler32/odeadler32.o:ode_adler32_blocks4
    python3 lean_verify.py ../kcheck/programs/varint/varint.spec proofs/ode_varint.proof \
            ../kcheck/programs/varint/odevarint.o:ode_varint
    python3 lean_verify.py examples/low/low.spec proofs/ode_low.proof examples/low/odelow.o:ode_low

Each command prints the contracts and then the word `shown`, which is how the verifier says "accepted".
The arguments are a specification file, a proof file, and one or more `OBJECT-FILE:FUNCTION` pairs.

The functions it verifies today:

| function | what it does | size | proof | time to verify |
|---|---|---|---|---|
| `ode_common` | length of the common prefix of two buffers | 45 instructions, 1 loop | 55 lines, 646 bytes | 4 ms |
| `ode_equal` | whether two buffers are equal, by calling `ode_common` | 10 instructions | 9 more lines | 4 ms for both |
| `ode_adler32` | the Adler-32 checksum, reducing modulo 65521 at every byte | 55 instructions, 1 loop | 265 lines, 3 kB | 5 ms |
| `ode_adler32_blocks` | Adler-32, reducing once per block of up to 5552 bytes, by shifts and masks | 116 instructions, 2 nested loops | about 1,400 lines, 19 kB | 40 ms |
| `ode_adler32_blocks4` | the same, four bytes per iteration; this is the fast one (87% of the speed of the usual C) | 164 instructions, 3 loops | about 2,000 lines, 26 kB | 80 ms |
| `ode_varint` | encodes a number as a varint into a 10-byte buffer supplied by the caller; returns the length | 35 instructions, 1 loop of at most 10 iterations | 790 lines, 9 kB | 35 ms |

`ode_equal`, `ode_low` and `ode_eighth` are small examples written for this folder. The other five are
shipped functions from `kcheck/programs/`.

## The soundness theorem

    theorem verify_all_sound (world : List Program) (defs : List Def) (fns : List Fn) :
        Linked world fns → verdictAll defs fns = none →
        ∀ f ∈ fns, ∃ p, findProgram world f.name = some p ∧ Meets world f.contract defs p

In words: suppose the verifier accepts a list of functions (`verdictAll defs fns = none`; `none` means "no
objection"). Then every function in the list satisfies its contract (`Meets`).

- `fns` is the input: for each function its name, its instructions, its contract, and the author's proof.
- `defs` are the definitions from the specification file, which contracts refer to.
- The proofs inside `fns` are not constrained in any way. The theorem holds whatever they contain.
- `Linked world fns` is the one assumption. It is explained below.

### What "satisfies its contract" means

`Meets` is defined in Contract.lean, in terms of the machine model in Machine.lean. Start the function in
any machine state that satisfies the caller's obligations (listed next). Then:

- **Control flow.** The machine executes only instructions of this function and of the functions it calls.
- **Memory safety.** The function reads only the input buffers named in the contract, its own stack frame
  and its return address. It writes only its own stack frame and the output buffers named in the contract.
  It does not read an output buffer. The stack frame is exactly the number of bytes the contract's `stack`
  line states. Functions it calls obey the same limits.
- **Termination.** After finitely many instructions it returns to the return address its caller pushed.
- **Result.** At that point: the stack pointer is just above the return address; the callee-saved
  registers (rbx, rbp, r12 to r15) have their original values; memory outside the stack frame and the
  output buffers is unchanged; `rax` holds the value that the contract's `returns` line specifies; and
  every `ensures` line holds. An `ensures` line has the form `BUFFER[lo .. hi] = LIST` and says that those
  bytes of an output buffer equal a list defined by the specification.

The caller's obligations (`Contract.pre`):

- every register holds a 64-bit value;
- `stack` bytes below the stack pointer are available;
- every input buffer is mapped memory, holds bytes, and does not overlap the stack frame or the return
  address;
- every output buffer is mapped memory and does not overlap the stack frame, the return address, any input
  buffer, or any other output buffer;
- a contract can also name a fixed-size read-only buffer, and a fixed-size buffer that is both read and
  written. They have the same obligations, and the read-and-written one counts as an output buffer;
- the function's code is in memory.

### The one assumption: `Linked`

`world` stands for the set of functions that exist when the code runs. `Linked world fns` says that each
function name in the input refers, at run time, to a function with exactly the instructions given in the
input, present in memory. In the model, a call instruction goes to the function with the called name. That
the real linker arranges this is not proved here. (It is not proved in `kcheck/` either;
[VERIFY.md](../kcheck/VERIFY.md) says so.)

### Axioms

Lean reports which axioms a theorem depends on. For these theorems it reports `propext`,
`Classical.choice` and `Quot.sound`, which are the three standard axioms of Lean itself.
`test_sound.py` checks this, checks that the theorem statements are the ones printed above, and checks
that no proof is left unfinished.

## How the verifier works

The verifier executes the function symbolically. It keeps, for every register and stack slot, a symbolic
expression over unknowns, plus a set of linear inequalities known to hold between those unknowns. It
follows every path through the code. What an instruction does is not built into the verifier: it is looked
up in the instruction table `../core/x86.tab`.

The proof file supplies only what the verifier would otherwise have to search for: loop invariants, and
proofs of arithmetic facts. Everything in the proof file is checked. Nothing in it is believed.

**Arithmetic.** When the verifier needs a fact such as "this index is inside the buffer", the proof gives a
short derivation: add up some of the known inequalities, with integer multipliers, and reach a
contradiction with the negation of the fact. The verifier just does the additions.

**Loops.** A loop is handled by a loop invariant that the proof supplies, attached to an instruction inside
the loop. The proof file calls such a point a `place`. An invariant states which registers still hold
their earlier values, some facts, and a termination measure (a quantity that is never negative and
decreases on every iteration). The first time a path reaches the invariant's instruction, the verifier
checks that the invariant holds, and then continues from a generalized state in which only the invariant
is known. Each path that comes back around the loop must re-establish the invariant with a smaller
measure. Soundness for loops is proved by induction on the measure. A function may have several
invariants, and loops may be nested.

**Calls.** A call is handled using only the contract of the called function. The called function must
appear earlier in the input and must already have been verified. So nothing is assumed about any function,
and recursion (direct or mutual) is impossible. At a call the verifier checks the caller's obligations
from the callee's contract: that the callee's stack frame and return address fit in what is left of the
caller's frame, and that each buffer passed is one of the caller's own buffers, passed whole. After the
call it keeps only what the callee's contract guarantees: the callee-saved registers, memory outside the
callee's frame, and the returned value in `rax`. All other registers and the flags become unknown.

There are two theorems. `verify_sound` is about one function, assuming the functions it calls satisfy
their contracts. `verify_all_sound`, above, removes that assumption by going through the functions in
order.

**Output buffers.** A contract may give the function a buffer to write, for example `out: 10 bytes`, with
an `ensures` line about its contents. The verifier tracks single-byte stores into such a buffer. For each
store it checks that the address is inside the buffer and that the stored value is a byte, and it records
the offset and the value. It requires all recorded offsets of a buffer to be provably distinct, and rejects
a store whose offset it cannot distinguish from an earlier one. At the return it evaluates the list in each
`ensures` line from the specification, element by element, and checks that the recorded byte at each
offset equals the corresponding element.

## What you have to trust

| | |
|---|---|
| Proved, so you need not read it | The verifier's rules: Core.lean (914 lines of code) and the arithmetic rule in Arithmetic.lean. All the clever parts are here or in the prover. |
| What the theorem is *about*. You need to read it, or trust it for some other reason | The formal model: Table.lean (reads the instruction table `../core/x86.tab`), Machine.lean (what each instruction does to registers, flags, memory and the low 128 bits of vector registers; what call and return do), and Contract.lean (what a contract and a specification definition mean; the definition of `Meets`). 731 lines of code. |
| That the Lean proofs are valid | Lean's kernel, or any independent checker for Lean proofs. |
| Tested, not proved | See the next list. |

Tested but not proved:

- **The machine model against a second model.** Machine.lean is compared with the Python model
  `../core/conc.py` on every instruction form it supports: 68 forms, 20 of them 128-bit vector
  instructions, from random states (`test_machine.py`). `conc.py` in turn was compared with three real
  processors, instruction form by instruction form (`../core/cross.py`).
- **The specification evaluator against a second evaluator.** `evalSpec` in Contract.lean is compared with
  `../kcheck/ode.py`: 2,700 evaluations of 18 definitions, 600 lists, 4,000 random expressions, 300
  sequence elements, and 2,040 evaluations of 17 further definitions that use the newer forms (words,
  records and so on). It is also run on BLAKE3 itself: evaluating `../kcheck/blake3.spec` in Lean
  reproduces the 105 official BLAKE3 test vectors (`test_spec.py`).
- **The arithmetic rule against a second implementation**, `../kcheck/varith.py`, on the 7,649 arithmetic
  proofs in the shipped files (`test_arith.py`).

Not covered by the theorem, and trusted today:

- **Decoding bytes into instructions.** The theorem is about functions given as a list of instruction
  forms from the table. Turning the object file's bytes into that list is done by `statement.py` using
  `../kcheck/kdecode.py`. That code is Python. It also parses the ELF file and resolves the names of called
  functions.
- **Parsing the specification.** `statement.py` uses `../kcheck/ode.py` to parse the specification text,
  and writes the contracts and definitions in the line format that the Lean program reads. A sequence
  given by a first element and a step is written out as the recursive definition it stands for.
- **Reader.lean and the compiled program.** Reader.lean parses the input and proof files. The theorem is
  about the Lean function `verdictAll`. That the compiled executable computes that function is trusted to
  Lean's compiler.
- **That the instruction table matches real processors.** This rests on the comparison done by
  `cross.py`. That comparison cannot execute a `call` or a `ret` in isolation, so what those two
  instructions do is stated directly in Machine.lean.
- **Linking** (the `Linked` assumption above).

A proof file cannot change what is being proved. The input (what is to be proved) and the proof are two
separate files, and a line of an input kind inside a proof file is rejected. The only string in the input
that comes from the author is the name of a called function. The decoder rejects a name that is not a
single plain word, and `statement.py` rejects a line containing a line break.

## What is supported so far

**Instructions.** Instruction forms over the general-purpose registers, the zero and carry flags, and
memory operands of 1, 4 and 8 bytes; jumps; calls to functions in the same input. The verifier has rules
for: add, subtract, compare, shift left by a constant, shift right by a constant, AND with a mask of the
form 2^k - 1, taking the low 32 bits or low 8 bits of a register (`mov ecx, esi`, `movzx eax, dil`),
8-byte stores to a stack slot, and 1-byte stores to an output buffer.

**Contracts.** Arguments that are numbers, read-only input buffers, and write-only output buffers of a
fixed size; `returns`; `stack`; and `ensures BUFFER[lo .. hi] = LIST`.

**Specifications.** Definitions that are a single expression built from numbers, names, arithmetic,
comparisons, remainder and quotient by a constant, `if`, a byte of a buffer, `len`, list literals, list
concatenation, and calls of other definitions (including recursive ones), plus sequences defined by a
first element and a step. When checking a fact, the proof tells the verifier where to unfold a definition;
unfolding nests up to eight deep. Subtraction is defined only when the result is not negative, as in the
specification language, and the verifier demands a proof of that wherever a subtraction occurs.

The quotient and remainder of a value by a given divisor are introduced once. A later shift or mask of the
same value in the code, or a later `/` or `%` of it in the specification, refers to the same unknowns. That
is what lets shift-and-mask code be matched against a specification written with `/` and `%`.

`statement.py` refuses any contract line it does not support, so that nothing is silently dropped. Today
it refuses `requires` (other than `requires no_overlap`), other forms of `ensures`, `writes` and `calls`.
A `needs` line (the processor feature a function requires, such as `needs avx512`) is carried through. It
has no meaning in the machine model, which has every instruction of the table. The verifier does check
that a caller's contract repeats every `needs` of the functions it calls. It refuses a contract that promises that the execution trace is independent of a buffer's contents
(the constant-time property), because the model here does not define a trace. It refuses specifications that use a layout, a kind, a lemma, or a definition that can fail.
A contract with an output buffer and another buffer must state `requires no_overlap` over all of them,
because the model demands that of the caller.

**Further than the verifier goes.** The Lean definition of the specification language (the evaluator
`evalSpec`) covers more than the verifier can reason about symbolically: `let`, 32-bit words and their
operations, counters, list comprehensions, slices, list update, records, "the least number such that",
"the greatest power of two such that", and conversion between bytes and words. That is everything
`../kcheck/blake3.spec` uses. The verifier rejects a function whose verification would need to unfold one
of these forms, with the message "not here yet". The machine model likewise already defines the 128-bit
vector instructions, and the verifier rejects them.

The same is true of the contract of BLAKE3's one-block compression kernel
(`blake3_servil_compress_in_place_avx512`). `statement.py` can now express it in the model's terms: 32
bytes that are read and written, 64 bytes that are read, three numbers, and a postcondition saying that the
32 bytes end up holding `compress(...)` of what they and the other arguments held at entry
(`test_kernel.py`). The verifier rejects the function, because it has no rules for vector instructions
yet. One promise of the kernel's real contract is left out: that its execution trace does not depend on
the data (constant time). The model does not define a trace.

### Known limitations

These are cases where the verifier rejects a correct function:

- A buffer can be passed to a called function only whole (same start, same length).
- The return value of a called function is known only as "the value of this call of this definition". It
  can be used where the caller's contract mentions the same definition with provably equal arguments.
- No rule yet for: AND with a constant that is not a mask, OR, shift by a register, a 4-byte load,
  instructions that set only the low byte of a register (`mov al, 1`).
- Nothing may be written below the stack pointer.
- Output buffers: only single-byte stores; the function cannot read back what it wrote; what was written
  before a loop invariant is forgotten at the invariant; a called function cannot write to the caller's
  output buffer.
- `ensures` has one form only, with no condition.

The next parts to build are vector registers in the verifier, and loops that write to an output buffer.

## The two input files

**What is to be proved** is a text file written by `statement.py` from the object file's bytes and the
specification. (The code and file names call this file the "statement".)

    fn ode_common                 a function; its instructions and contract follow
    i 0 1 .push .rbx              an instruction: start offset, end offset, instruction form and operands
    arg a bytes n                 an input buffer of n bytes (`arg out out 10`: an output buffer of 10 bytes)
    returns (call common (name a) (name b))
    stack 40
    fn ode_equal                  the next function; it may call the ones before it
    …
    def common a b = (call alike (name a) (name b) (num 0))        definitions from the specification

**The proof** is also a text file, one item per line, in the order in which the verifier needs them:

    for ode_common                the following lines are for this function
    place 52                      a loop invariant, at the instruction at offset 52
    name i r13                    names for the values that registers hold there
    fact (bin <= (name i) (name n))
    keep rcx rdx rbx rsp …        registers that still hold the value they had on first arrival
    decreases (bin - (name n) (name i))                the termination measure
    t open 1                      unfold this occurrence of a definition
    t held 0 / t carry 0          reuse a value already computed for an equal call of a definition
    t live / t dead               a branch is feasible / infeasible (followed by an arithmetic proof)
    t lt / t eq / t gt            how two values compare (followed by an arithmetic proof)
    p 0 3 17  /  s 0 1 2 1 1  /  q       an arithmetic proof: which known inequalities it starts from
                                  (by index), steps that each add two inequalities, and the end

## The prover

`prove.py` finds proofs. It is not trusted: whatever it produces is checked by the verifier.

It works as a dialogue. It gives the verifier the proof so far; the verifier replies with the next thing
it needs (for example, "prove that these inequalities imply that one"); the prover finds it and appends
it. Arithmetic is found by variable elimination. The prover is deterministic: it finds the same proof on
every run, and the tests compare each stored proof with what the prover finds.

The verifier executable `odeverify` re-checks the whole proof from the first line every time it is asked.
For `ode_adler32_blocks4`, whose proof has 2,023 lines, that meant re-reading 1.2 million proof lines in
total and took 47 of the prover's 62 seconds. So the prover now talks to a helper, `odeprove`
(ProveMain.lean, driven by `session.py`). The helper runs the same verifier code but keeps its position:
when the verifier asks for a proof line that has not been supplied yet, the process forks. The child
continues as if the proof ended there and reports what the verifier says. The parent waits for the next
line. Backtracking to an earlier point is just terminating the later processes.

Time to find each proof, on a 64-thread Zen 4 machine:

| function | questions asked | with `odeprove` | with `odeverify` each time |
|---|---|---|---|
| `ode_common` | 47 | 0.16 s | 0.28 s |
| `ode_adler32` | 204 | 0.58 s | 1.26 s |
| `ode_adler32_blocks` | 763 | 5.3 s | 14.0 s |
| `ode_adler32_blocks4` | 2,101 | 15.2 s | 53.1 s |
| `ode_varint` | 186 | 2.2 s | 6.2 s |

Both ways find byte-for-byte the same proofs (`ODE_PROVE_FROM_START=1` selects the old way). The remaining
time is the prover's own search for arithmetic proofs. `odeprove` is not trusted either: `prove.py`
returns a proof only after `odeverify` has accepted it, and `test_session.py` checks that the two give
identical answers at every prefix of three stored proofs.

## Measurements (November 18, 2026)

**Speed of the verifier.** 4 ms for `ode_common`, 5 ms for `ode_adler32`, 40 ms for `ode_adler32_blocks`,
80 ms for `ode_adler32_blocks4`, 35 ms for `ode_varint`. Each figure is a whole run, including process
start and reading three files. The Python verifier in `kcheck/` takes 4, 4, 14 and 28 ms for the first
four and 25 to 40 ms for `ode_varint`, not counting its start-up. So the Lean verifier is about as fast on small functions and about
three times slower on the large ones. Most of its time goes into the representation of inequalities,
which are stored as dense lists with one slot per unknown.

**Two limits that are enforced by a test** (`test_limits.py`): every stored proof must be under 100 kB,
and a whole run of this verifier must take at most five times as long as the Python verifier takes for the
same function.

**Proof sizes.** A proof is mostly arithmetic. `ode_adler32`: 39 arithmetic proofs. `ode_adler32_blocks`:
two loop invariants and 174 arithmetic proofs. `ode_adler32_blocks4`: three loop invariants, 258 arithmetic
proofs, and 23 places where a definition is unfolded. `ode_varint`: no loop invariant (the loop is unrolled,
at most ten iterations) and 111 arithmetic proofs. The `ode_adler32_blocks` proof was 135 kB when each
arithmetic proof wrote out the inequalities it starts from; it now names them by index.

**Wrong inputs are rejected.** For each function, the tests make single changes to the code, the
specification, the contract or the loop invariants, and check two things: the verifier does not accept
with the stored proof, and the prover finds no proof within a budget comparable to what the correct
version needs.

| function | changes tried | examples |
|---|---|---|
| `ode_common` | 18 | |
| `ode_adler32` | 19 | a different modulus; a sum not reduced; a shift by 15 |
| `ode_adler32_blocks` | 14 | a mask of 17 bits; an invariant that does not keep the block's end; a measure that does not decrease |
| `ode_adler32_blocks4` | 4 | reading four bytes where three remain; using the third byte as the second |
| `ode_varint` | 15 | a byte not written; a byte written one position late; adding 127 instead of 128; reading back what was written |
| `ode_low`, `ode_eighth` | 14 | the whole register instead of its low half; a shift by two instead of three |
| `ode_equal` (the caller) | 16 | keeping a value in a register that a call may change; passing part of a buffer; moving the stack pointer |

Also rejected: a caller listed before its callee, a function that calls itself, a missing callee, and two
functions with the same name.

**Wrong proofs are rejected.** The tests delete or alter single lines of the stored proofs: every line
for `ode_common` (85 trials) and `ode_adler32`, every third line for `ode_varint` (443 trials), every
seventh for `ode_adler32_blocks` (343 trials), every eleventh for `ode_adler32_blocks4` (326 trials). Every
altered proof is rejected.

**The arithmetic rule.** All 7,649 arithmetic proofs in the shipped files (17,505 steps) check, in 0.3 s.
On 3,000 deliberately altered proofs, Lean and the Python implementation `varith.py` agree on every one.

**The machine model.** 68 instruction forms, 60 random instances each: Machine.lean and `conc.py` produce
the same registers, flags, memory, low 128 bits of each vector register, and next instruction address.
24 instruction forms are not yet defined in Machine.lean: the 512-bit ones, one that uses a mask register,
`lea_data` (the address of the file's data), and `call`.

**The BLAKE3 specification.** Evaluating `../kcheck/blake3.spec` (29 definitions) in Lean gives the 105
official test vectors (35 input lengths up to 102,400 bytes, in three modes) in 43 s. With one constant in
the specification changed (a rotation by 11 bits instead of 12), it does not.

**Code size.** The formal model: 731 lines. The verifier: 1,073 lines (Core.lean 914, Arithmetic.lean 159
including its proofs). The file parser: 156 lines. The proofs of the theorems: 5,089 lines.

## The files

| | |
|---|---|
| the formal model | `Table.lean`, `Machine.lean`, `Contract.lean` |
| the verifier | `Core.lean`; `Arithmetic.lean` (the arithmetic rule and its soundness lemma `refutes_sound`); `Reader.lean` and `Main.lean` (the program `odeverify TABLE STATEMENT PROOF`) |
| the soundness proofs | `SoundLin.lean` (arithmetic on inequalities), `SoundState.lean` (how the verifier's symbolic state relates to a machine state), `SoundStep.lean` (one instruction effect), `SoundSpec.lean` (symbolic evaluation of the specification), `SoundList.lean` (lists and `ensures`), `SoundPlace.lean` (loop invariants), `SoundCall.lean` (calls), `SoundTop.lean` (paths and loops: `explore_sound`, by induction on the termination measure; `verify_sound`; `verify_all_sound`) |
| writes the input file (trusted) | `statement.py` |
| for someone verifying | `lean_verify.py`; the stored proofs in `proofs/`; `examples/equal/` and `examples/low/` (source, specification and object file); `examples/adler32/*.places` (the loop invariants the prover starts from) |
| the prover (not trusted) | `prove.py`, `session.py`, `ProveMain.lean` (`odeprove`) |
| tests | `test_sound.py`, `test_verify.py`, `test_call.py`, `test_adler.py`, `test_blocks.py`, `test_blocks4.py`, `test_varint.py`, `test_low.py`, `test_limits.py`, `test_machine.py`, `test_spec.py`, `test_arith.py`, `test_session.py`, `test_kernel.py`. `MachineMain.lean`, `SpecMain.lean` and `ArithMain.lean` are small programs that three of the tests run. `built.py` runs Lean's build tool once per process. |

The tests are skipped where Lean's build tool `lake` is not installed.
