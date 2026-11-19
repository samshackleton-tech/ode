# proof-core: a small verifier with a machine-checked soundness theorem

[DESIGN.md](../DESIGN.md) section 7 asks that the verifier's verdict (its answer: accept or reject) rely on
a small core only, and that an auditor be given reasons he can check for relying on that core. This folder
is the first version of such a core. It contains:

- a **verifier**, written in Lean 4. It takes a compiled function, a contract and a proof, and either
  accepts or rejects;
- a **soundness theorem**, checked by Lean: if the verifier accepts, the function satisfies its contract.
  The theorem holds for every possible proof input, so a wrong or malicious proof cannot make the verifier
  accept a wrong function.

It is not finished. Today it handles a subset of what the Python verifier in `kcheck/` handles. That is
enough for five of the twelve small shipped functions and for a function that calls one of them. It is
also enough for four of the fourteen functions of the BLAKE3 hash: the two versions of the kernel that
compresses one 64-byte block (one written with AVX-512 instructions and one with SSE4.1 instructions);
`b3l_node_out`, the function that reads a node record and calls the kernel selected by its `plat`
argument; and the 16-way kernel, which compresses sixteen chunks at once, block after block, in a loop.
For the rest of the hash and the other programs, `kcheck/` is still the verifier to use.

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
    cat ../kcheck/blake3.spec examples/kernel/kernel.contract > /tmp/kernel.spec
    python3 lean_verify.py /tmp/kernel.spec proofs/blake3_servil_compress_in_place_avx512.proof \
            ../kcheck/b3hashr.o:blake3_servil_compress_in_place_avx512
    cat ../kcheck/blake3.spec examples/kernel/kernel_sse41.contract > /tmp/kernel_sse41.spec
    python3 lean_verify.py /tmp/kernel_sse41.spec proofs/blake3_servil_compress_in_place_sse41.proof \
            ../kcheck/b3hashr.o:blake3_servil_compress_in_place_sse41
    cat ../kcheck/blake3.spec examples/kernel/kernel.contract examples/kernel/kernel_sse41.contract \
            examples/kernel/node_out.contract > /tmp/node_out.spec
    cat proofs/blake3_servil_compress_in_place_avx512.proof proofs/blake3_servil_compress_in_place_sse41.proof \
            proofs/b3l_node_out.proof > /tmp/node_out.proof
    python3 lean_verify.py /tmp/node_out.spec /tmp/node_out.proof \
            ../kcheck/b3hashr.o:blake3_servil_compress_in_place_avx512 \
            ../kcheck/b3hashr.o:blake3_servil_compress_in_place_sse41 \
            ../kcheck/b3hashr.o:b3l_node_out
    cat ../kcheck/blake3.spec examples/kernel/p16.contract > /tmp/p16.spec
    python3 lean_verify.py /tmp/p16.spec proofs/blake3_servil_avx512_p16.proof \
            ../kcheck/b3hashr.o:blake3_servil_avx512_p16

Each command prints the contracts and then the word `shown`, which is how the verifier says "accepted".
The arguments are a specification file, a proof file, and one or more `OBJECT-FILE:FUNCTION` pairs.

The functions it verifies today:

| function | what it does | size | proof | time to verify |
|---|---|---|---|---|
| `ode_common` | length of the common prefix of two buffers | 45 instructions, 1 loop | 55 lines, 646 bytes | 3.5 ms |
| `ode_equal` | whether two buffers are equal, by calling `ode_common` | 10 instructions | 9 more lines | 3.5 ms for both |
| `ode_adler32` | the Adler-32 checksum, reducing modulo 65521 at every byte | 55 instructions, 1 loop | 260 lines, 3 kB | 4 ms |
| `ode_adler32_blocks` | Adler-32, reducing once per block of up to 5552 bytes, by shifts and masks | 116 instructions, 2 nested loops | 1,154 lines, 15 kB | 14 ms |
| `ode_adler32_blocks4` | the same, four bytes per iteration; this is the fast one (87% of the speed of the usual C) | 164 instructions, 3 loops | 1,815 lines, 23 kB | 22 ms |
| `ode_varint` | encodes a number as a varint into a 10-byte buffer supplied by the caller; returns the length | 35 instructions, 1 loop of at most 10 iterations | 79 lines, 453 bytes | 5 ms |
| `blake3_servil_compress_in_place_avx512` | BLAKE3's compression function on one 64-byte block: the hash's one-block kernel, written with AVX-512 instructions on 128-bit registers | 76 instructions, 1 loop of 7 iterations | 9 lines, 131 bytes | 12 ms |
| `blake3_servil_compress_in_place_sse41` | the same compression function for processors that have SSE4.1 and no more. It rotates a word by two shifts and an OR, or by a byte shuffle | 94 instructions, 1 loop of 7 iterations | 10 lines, 137 bytes | 13 ms |
| `b3l_node_out` | reads a 120-byte node record from memory, packs its flags, and calls the AVX-512 or SSE4.1 kernel | 18 instructions | 4 lines, 38 bytes | 22 ms with both kernels |
| `blake3_servil_avx512_p16` | the hash's 16-way kernel: sixteen chunks at once, each of `n` blocks read through a table of sixteen addresses, with AVX-512 instructions on 512-bit registers | 460 instructions, a loop over the blocks around a loop of 7 rounds | 204 lines, 2.4 kB | 1.1 s |

`ode_equal`, `ode_low` and `ode_eighth` are small examples written for this folder. Five are shipped
functions from `kcheck/programs/`. The last four are four of the fourteen functions in the shipped
BLAKE3 object file `kcheck/b3hashr.o`. Each one-block kernel's contract says that the eight 32-bit words
at `h` end up holding `compress(h, m, t, length, flags)`, as `kcheck/blake3.spec` defines it.
`b3l_node_out`'s contract says that `out` ends up holding `bytes_of(node_value(nd, root))`. The 16-way
kernel's contract says, for every `n` from 1 up, that the sixteen chaining values at `out` are
`chunk(key, t, flags, start, end, length, n, inputs[i])` for the sixteen lanes `i`.

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
- **Memory safety.** The function reads only the buffers declared for reading, its own stack frame, and
  its return address. It writes only its own stack frame and the buffers declared for writing. A buffer
  declared as output-only cannot be read. The `stack` line gives the size of the stack frame in bytes.
  Functions it calls obey the same limits.
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
- where the contract bounds a number argument (`length: word`), the number is below the bound;
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

An invariant can also say what vector registers hold. Such a line names some 512-bit registers and a
definition of the specification, with the things the definition is applied to written in terms of a lane
number. It says: in each of the sixteen lanes, the words of those registers are the list of words that the
definition gives. The first time a path reaches the invariant, and each time a path comes back to it, the
verifier evaluates the definition on its terms for 32-bit words and compares the result with the terms
the registers hold. In the generalized state each of those words is a fresh unknown, and the verifier
records that the definition, applied to those things, gives exactly those words. When the specification
is evaluated later and reaches the same application, the recorded words are used. Two applications count
as the same when their arguments are the same terms, or are numbers that the known inequalities show
directly to be equal.

**Shifts to the left.** A 64-bit shift to the left can push bits out of the register. Where the known
inequalities show directly that the shifted number is small enough, the verifier takes the result to be
the number times 2^k. Where they do not, the proof says which case holds. `t exact` is followed by an
arithmetic proof that the number is small enough. `t wrap` tells the verifier to keep only the part of the
number that survives the shift: its remainder modulo 2^(64-k), times 2^k. Both answers are sound. A wrong
`t exact` fails at its arithmetic proof.

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

**Vector registers and 32-bit words.** BLAKE3 computes with 32-bit words: additions that wrap around,
exclusive-ors, and rotations. Linear inequalities cannot describe those. So the verifier describes each of
the four low words of a vector register by a *term*, which is an expression tree. Its leaves are words
that the function loaded from its input buffers, and numbers taken from general-purpose registers. An
inner node is the sum of some terms, the exclusive-or of two terms, a term rotated right by n bits, or a
term shifted left or right by n bits.
Terms are stored in a table and referred to by their index, and equal terms get the same index. A sum is
stored as the sorted list of everything added, so `(a + m) + b` and `(a + b) + m` are the same term. The
two operands of an exclusive-or are stored in sorted order.

The instruction table says how each vector instruction moves or combines words, and the verifier applies
that to the terms. A 16-byte load from a buffer of words gives the four terms "word k of this buffer as it
was at entry". A 16-byte store into a buffer that the function may write records which term each of the
four words now holds. A vector register can also be filled from a 64-bit general-purpose register. The
verifier then needs the low and the high 32 bits of the value separately, and it checks that what it
takes for the low part is below 2^32. The AVX-512 kernel's proof file holds two small arithmetic proofs and
nothing else. They show that adding the length byte to the flags byte shifted left by 32 bits gives a
number between 0 and 2^64 - 1, so the addition does not wrap around.

The SSE4.1 kernel differs in three ways. Its proof has one more line, `t wrap`: the kernel shifts the
whole flags register left by 32 bits, and its contract says nothing about the upper 32 bits of that
register, so the shift discards them. Its contract says that the caller keeps the length below 2^32
(`length: word`), because the kernel adds the whole length register to the shifted flags. And it has no
rotate instruction. It rotates a word by shifting one copy left and another copy right and combining the
two with OR, or, for rotations by 8 and 16 bits, by a byte shuffle with a constant. The verifier
recognizes exactly these two ways. An OR of one term shifted left by k bits and the same term shifted
right by 32 - k bits is that term rotated right by 32 - k bits. A byte shuffle by one of the two
constants that the kernel uses is a rotation by 8 or by 16 bits. The verifier rejects any other OR of
vector registers and any other byte shuffle. It accepts a blend of 16-bit halves where both halves of
each 32-bit word come from the same register.

At the return, the verifier evaluates the specification's expression (for the kernel,
`compress(h, m, t, length, flags)`) on terms, where the Lean model evaluates it on numbers. It uses the
same table. Each word of the result must be the same term as the one stored at that position of the
output buffer. The verifier knows no algebra beyond the normal form described above. So a function is
accepted only if it computes each word by the same additions, exclusive-ors and rotations as the
specification. The order of the additions is free. Hand-written kernels are built that way.

Each kernel's loop runs seven times, counted down in a one-byte register. The verifier follows that
counter as a known number, so it executes the seven iterations one after the other. No loop invariant is
needed.

## Reliance sets: who relies on what, and for what

A *reliance set* belongs to one reader and one conclusion. It is everything that must work correctly for
that reader's conclusion to be right. The term is Mark S. Miller's; [DESIGN.md](../DESIGN.md) section 2
says more. The conclusion here is: "the verifier accepted this function, so the function meets its
contract on a real processor". Two readers can have different reliance sets for it, because there is more
than one way to become confident in the verifier's rules.

**In every reader's reliance set.** No reader can avoid these two.

| A reader relies on | for | How it can be checked |
|---|---|---|
| The formal model: Table.lean (reads `../core/x86.tab`), Machine.lean (the effects on registers, flags and memory), and Contract.lean (the meaning of contracts and specifications). 830 lines of code. | what the soundness theorem says about the processor and the contract | Read it. The tests below compare parts of it with separate implementations. |
| The steps outside the theorem | what each entry of the second list below says | They are tested, not proved. |

**For the verifier's rules, the reader chooses.** The rules are Core.lean (1,844 lines of code) and the
arithmetic rule in Arithmetic.lean. All the clever parts are here or in the prover. The rules are relied on
for accepting only what the formal model implies.

| A reader who | relies on | and does not rely on |
|---|---|---|
| accepts Lean's kernel, the program that verifies Lean's proofs | Lean's kernel, for the soundness theorem above really being proved. An independent verifier of Lean proofs can check the proofs again. We have not yet run one on them. | his own reading of Core.lean. He need not read it. |
| does not accept it | his own reading of Core.lean and Arithmetic.lean | Lean |

Two more ways are planned and not built: a second verifier written independently, and a verifier written
in Ode that verifies itself ([DESIGN.md](../DESIGN.md) sections 7 and 12).

**In no reader's reliance set:** the prover, the compiler, the assembler and the author. Whatever they
produce is checked. They are in the *author's* reliance set, for another conclusion: "my function will be
accepted".

Tested but not proved:

- **The machine model against a second model.** `test_machine.py` compares Machine.lean with the Python
  model `../core/conc.py` on 86 instruction forms from random states. This includes the 512-bit forms
  used by P16, the 16-way kernel. `core/cross.py` compares the Python model with real processors.
- **The specification evaluator against a second evaluator.** `evalSpec` in Contract.lean is compared with
  `../kcheck/ode.py`: 2,700 evaluations of 18 definitions, 600 lists, 4,000 random expressions, 300
  sequence elements, and 2,040 evaluations of 17 further definitions that use the newer forms (words,
  records and so on). It is also run on BLAKE3 itself: evaluating `../kcheck/blake3.spec` in Lean
  reproduces the 105 official BLAKE3 test vectors (`test_spec.py`).
- **The arithmetic rule against a second implementation**, `../kcheck/varith.py`, on the 7,649 arithmetic
  proofs in the shipped files (`test_arith.py`).

Outside the theorem. Every reader relies on each of these today, for what its entry says:

- **Decoding bytes into instructions.** The theorem is about functions given as a list of instruction
  forms from the table. Turning the object file's bytes into that list is done by `statement.py` using
  `../kcheck/kdecode.py`. That code is Python. It also parses the ELF file and resolves the names of called
  functions.
- **Parsing the specification.** `statement.py` uses `../kcheck/ode.py` to parse the specification text,
  and writes the contracts and definitions in the line format that the Lean program reads. A sequence
  given by a first element and a step is written out as the recursive definition it stands for.
- **Reader.lean and the compiled program.** Reader.lean parses the input and proof files. The theorem is
  about the Lean function `verdictAll`. For the compiled executable computing that function, a verdict
  relies on Lean's compiler and runtime library (which includes Lean's array and hash map: the table of
  terms is an array, and a hash map says where a term may be found).
- **Processor features.** The machine model has every instruction in the table. A real processor has only
  the instruction sets it supports. So `statement.py` looks at the kind of each instruction: AVX-512, AVX
  or SSE4.1, recognized by the encoding prefix as in `kcheck`. It refuses a function that contains a kind
  missing from the `needs` lines of its contract. That check is Python, outside the theorem.
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
8-byte stores to a stack slot, 1-byte stores to an output buffer, and setting or decrementing the low
byte of a register (`mov al, 7`, `dec al`).

Taking the low 32 bits or the low 8 bits of a number normally makes two new unknowns, a quotient and a
remainder. Where the facts show at once that the number is already below 2^32 (or below 256), the low
part is the number itself, and no unknown is made. Where a number that the facts bound is divided, the
verifier also records the bound that follows for the quotient. So a byte taken out of a register by a
shift and a mask is one unknown, whichever 32-bit moves lie between the shift and the mask.

Two rules deal with numbers that are not sums of multiples of unknowns. For each of them the verifier
introduces one unknown and remembers what it stands for, so that the code and the specification refer to
the same unknown:

- an 8-byte read at a constant offset of a read-only buffer of fixed size (a field of a record). The
  buffer cannot change while the function runs, so one unknown stands for one offset. It is below the
  bound that the record's layout gives for that field;
- the bitwise OR of two registers. The result is at least as large as each operand. Where both operands
  are known to be below 2^8, 2^16 or 2^32, so is the result.

It also has rules for the 128-bit vector instructions that the two one-block kernels use:

- 16-byte loads and stores, and loading a constant;
- filling a register from general-purpose registers;
- addition, exclusive-or and rotation of 32-bit words;
- the instructions that only move words around (shuffles, blends, unpacks);
- shifts of 32-bit words by a constant, and OR, in the one combination that makes a rotation;
- byte shuffles by the two constants that rotate each word by 8 or by 16 bits;
- blends of 16-bit halves in which both halves of each word come from the same register.

**Contracts.** Arguments that are numbers, read-only input buffers, and write-only output buffers of a
fixed size; `returns`; `stack`; and `ensures BUFFER[lo .. hi] = LIST`. Also buffers of 32-bit words of a
fixed size, either read-only (`m: block`) or read and written (`h: cv`), with `ensures h = EXPRESSION`
saying which words the buffer holds at the return. A number argument can carry a bound or a width:
`length: word` means that the caller keeps the number below 2^32, and `flags: low word` means that only
the low 32 bits of the register are the argument.

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
that a caller's contract repeats every `needs` of the functions it calls. `statement.py` checks that a
function's own instructions are of kinds its `needs` lines name. It refuses a contract that promises that the execution trace is independent of a buffer's contents
(the constant-time property), because the model here does not define a trace. It refuses specifications that use a kind, a lemma, or a definition that can fail. A layout is read where an argument is a record of that layout.
A contract with an output buffer and another buffer must state `requires no_overlap` over all of them,
because the model demands that of the caller.

**Further than the verifier goes.** The Lean definition of the specification language (the evaluator
`evalSpec`) covers more than the verifier can reason about symbolically: `let`, 32-bit words and their
operations, counters, list comprehensions, slices, list update, records, "the least number such that",
"the greatest power of two such that", and conversion between bytes and words. That is everything
`../kcheck/blake3.spec` uses. This matters for facts about numbers: loop invariants, `returns`, and
`ensures` of bytes. There the verifier rejects a function whose verification would need to unfold one of
these forms. The message is "not here yet". For an `ensures` of a buffer of words, the verifier evaluates
most of these forms on terms, as described above. The exceptions are slices, records and the two "such
that" forms. For four kinds of 128-bit vector instruction the verifier has rules only for the uses
that the SSE4.1 kernel makes of them: byte shuffles, shifts, OR, and blends of 16-bit halves. The machine
model defines them in general.

**What is left out of the kernels' contracts.** The kernels' real contracts
(`../kcheck/proofs/inner.spec`) also promise that the execution trace does not depend on the data
(constant time). The model here does not define a trace, so that promise is not proved here. The
contracts used here (the two files in `examples/kernel/`) say so. `kcheck/` does check it.

### Known limitations

These are cases where the verifier rejects a correct function:

- A buffer can be passed to a called function only whole (same start, same length).
- The return value of a called function is known only as "the value of this call of this definition". It
  can be used where the caller's contract mentions the same definition with provably equal arguments.
- No rule yet for: AND with a constant that is not a mask, OR, shift by a register, a 4-byte load.
- Nothing may be written below the stack pointer.
- Output buffers of bytes: only single-byte stores; the function cannot read back what it wrote; what was written
  before a loop invariant is forgotten at the invariant; a called function cannot write to the caller's
  output buffer.
- `ensures` has one form for a buffer of bytes and one for a buffer of words, neither with a condition.
- Buffers of words: 16-byte loads and stores only, at constant offsets that are multiples of 4. A buffer
  that is read and written cannot be read after the first store to it. Bytes and words cannot both be
  stored to one buffer. Such a buffer cannot be passed to a called function.
- What is known about vector registers, and about words stored to a buffer, is forgotten at a loop
  invariant and at a call.
- Words are compared as terms. A function may compute the right words by other operations than the
  specification, for example `a + a` for `2 * a`. Such a function is rejected. Two exceptions are built
  in, because the SSE4.1 kernel needs them: a rotation done as two shifts and an OR, and a rotation done
  as a byte shuffle.
- A function whose contract bounds a number (`length: word`) cannot be called by another function yet.
- One contract that is true of the SSE4.1 kernel is rejected: the one with `flags: number` in place of
  `flags: low word`. The specification's `word(flags)` and the low 32 bits that the kernel takes from the
  flags register are the same value, but the verifier holds them as two different terms. A test records
  this (`test_kernel.py`).

The verifier can follow 512-bit register moves, broadcasts, adds, exclusive ORs, rotations and shuffles.
It must know all sixteen lanes before reading a wide register. A 128-bit write forgets the upper lanes
of its destination, and `vzeroupper` forgets the upper lanes of registers 0 through 15. The same load
and store rules cover both four and sixteen words. The 512-bit rules support unaligned instructions
at fixed offsets in a buffer. A load can add an index register if the resulting offset is still fixed.
A broadcast can read one word from a buffer and repeat it in every lane. A store forgets the old values
at exactly the words it replaces. These load rules reject a read from a buffer after a store to it.

A test verifies a six-instruction function from its object file against a contract that adds sixteen
pairs of words. It refuses a version that reads both operands from the same vector.

The verifier can also follow an `and` that rounds the stack pointer down to a 64-byte boundary. When
the exact offset from the entry stack pointer is unknown, the proof must show that the new pointer
stays within the frame and that any saved words stay at or above it. The verifier records those facts
rather than asking for the same proof at each instruction. A test checks the same proof with and
without 80 intervening instructions that do not change the stack pointer.

The verifier can also write and reload one 64-byte vector in the aligned stack frame. It checks the
whole slot, its alignment, and that the store ends before any saved scalar word. It remembers only the
most recent vector store. A scalar store, a call or exit from the aligned frame makes it forget the
saved vector. It verifies a copy from object bytes that clears the register between the store and
reload. Tests reject a reload from another slot, a store whose address lacks the required alignment,
and a stack adjustment that would leave the slot below the stack pointer.

`test_p16_one.py` combines those rules on a 418-instruction fixture taken from `../wide/p16.ode`: P16's
prologue, stack realignment, key broadcasts, 64-instruction input transpose, seven compression rounds with
four aligned stack spills and reloads, feed-forward XORs, output transpose, stores, and epilogue, with 16
contiguous block loads in place of the pointer array and outer block loop. The verifier accepts its
408-byte proof against sixteen `compress` calls from `../kcheck/blake3.spec` at the exact 367-byte stack
bound, and rejects a 366-byte bound as well as changed rotations, shuffles, spill slots, and store offsets.

A contract can now give a function a table of addresses. The table is a run of a fixed number of bytes.
Each eight bytes of it are the address of `n` blocks of 64 bytes that the function may read, where `n` is
another argument. The formal model asks the caller to keep those blocks in memory, apart from the stack
frame and from every run the function writes. A contract can also say that a number is at least some
value. In the specification the table's name is the list of its lanes, and each lane is the list of its
blocks, sixteen words each.

The verifier follows a 64-byte load through an address that it read from such a table. The proof must show
that the load lies within that lane's blocks. The offset may be a number that is only known through the
facts, such as 64 times a loop's count. The sixteen words become new unknowns, and the verifier records
which block of which lane they are. When the specification asks for a block of a lane, the verifier finds
the words that the function read at that offset.

`test_p16_table.py` uses the same instructions as `test_p16_one.py` and also keeps P16's sixteen pairs of
a table read and a block load. The 437-instruction fixture is verified against a contract that gives
sixteen lanes of `n` blocks with `n` at least 1. The proof is 760 bytes. The verifier refuses the same
code when the lower bound is missing, when the contract names another block, when the run is not declared
as a table, when one lane reads another lane's address, when an address is taken from between two table
entries, and when the load starts before the lane's blocks.

**The 16-way kernel is verified for every number of blocks.** `test_p16.py` verifies the shipped bytes
of `blake3_servil_avx512_p16` (460 instructions in `../kcheck/b3hashr.o`). Its contract is
`examples/kernel/p16.contract`: the contract of `../kcheck/proofs/inner.spec` with a `trace` line added,
as for the other kernels.
`statement.py` now reads the three kinds of argument that this contract uses. `16 inputs` is the table of
addresses described above. `16 cvs` is a buffer of sixteen chaining values, with one `ensures` that speaks
of each of them. `bytes flags start end length` is one register whose four low bytes have names;
`statement.py` writes each name as that byte of the register's low 32 bits. A contract can also say
`requires n >= 1` or `requires n < 2` of a number.

The kernel loops over the blocks of a chunk. Its loop invariant is in `examples/kernel/p16.places`, and
it is attached to the last instruction of the loop body before the block count is decremented:

    place +0x9a7 {
        name left = r13
        name off = r14
        fact left >= 1
        fact left <= n
        fact off == 64 * (n - left)
        lane i: zmm0 .. zmm7 = chunk(key, t, flags, start, end, length, n, inputs[i]) after n - left + 1
        decreases left
    }

`left` is the number of blocks still to do, counting the one just compressed. So `n - left + 1` blocks are
done. The `lane` line says that in each lane `i` the registers zmm0 to zmm7 hold the chunk's chaining
value after that many blocks. `chunk` is a sequence with a count in the specification; `after K` names
its value after `K` steps. `prove.py` writes that line for the verifier as a use of the definition
`chunk.h`, which is how `statement.py` writes the sequence. The prover also finds which registers the
loop leaves alone.

With that invariant the verifier accepts the contract as it stands, for every `n` from 1 up. The proof is
2,350 bytes and the verifier takes 1.1 s. It walks six paths: the first block with `n` equal to 1 and
with `n` greater; from the invariant to the return, twice; and once round the loop to a block that is
the last and to one that is not. Without the invariant the path goes round the loop without end, and a
test records that the prover gives up.

Two things in the verifier had to change besides the invariant itself. The blocks of a lane lie apart
from the eight bytes of the return address, so they end at least 64 bytes below 2^64; the verifier now
starts from that fact, which shows that `add r14, 64` does not wrap. And the blocks of a lane can be one
of the things a recorded application of a definition is applied to.

The tests change the contract in ten ways, the code in six and the invariant in fourteen, and the
verifier refuses each. Among the contracts: the first block's flags exchanged with the last block's, which
is false as soon as there are two blocks; one block fewer than the code compresses; another lane's blocks;
no lower bound on `n`. Among the instructions: the flags of the first block kept for every block; the
next block read two blocks on; the last block's flags or its length left out. Among the invariants: the
chaining value after one block fewer or one block more; two registers exchanged; nothing said of the
vector registers; no upper bound on `left`; a measure that does not decrease; a register kept that the
loop changes.

The same test file also narrows the contract by one line, `requires n < 2` or `requires n < 3`, and gives
no invariant. The verifier then follows each count of blocks as a path of its own. For one block a lane
the proof is 921 bytes and the verifier takes 0.20 s. For one or two blocks the proof is 1,440 bytes and
the verifier takes 0.66 s. Those tests refuse ten changed contracts and four changed instructions.

Two more rules were needed. A broadcast of a register's low 32 bits makes the word of the register's
number directly, so that the specification's `lo(t)` is the same term. And in the specification, numbers
that the verifier holds as sums of unknowns can now be added, subtracted, divided by a constant where the
state already holds that quotient, and compared. A comparison is decided only where the facts show at
once that the two numbers are equal, or that one is the greater.

One limit to know of: the verifier takes an OR of three numbers only in the grouping the code computes.
With one block a lane, a contract that exchanges the first block's flags with the last block's says the
same thing, since all three bytes go into one word. The verifier refuses that contract. It refuses a true
statement there; it does not accept a false one.

**`b3l_node_out`, the function that calls both kernels, is verified.** It reads a 120-byte node record
from memory, combines its flags with `or`, checks the processor platform argument, and calls either the
AVX-512 kernel or the SSE4.1 kernel.

- An argument can be a record in memory, described by a `layout` in the specification. `statement.py`
  writes the record out field by field. A field of eight bytes that holds a number is written with
  `number.le`, "the number that these bytes are, lowest byte first". No specification can define that name.
- What a layout requires of such a number (`length: number at 104 below 65`) becomes a line `mbelow`. The
  caller has to guarantee it, and the formal model's precondition says so.
- `needs avx512 if plat == 5` becomes a line `needsif`. At a call the verifier checks that the caller's
  contract allows every processor feature the callee needs on the current path.
- Calling a function that writes a buffer of 32-bit words for its caller (`symCallW` in Core.lean, proved
  sound in SoundCallW.lean): the verifier checks that the callee's stack frame fits, that its read-only
  buffer arguments lie inside the caller's fixed-size read-only buffers, that its read-and-written buffer
  is a read-and-written buffer of the caller whose words are all known, and that any numeric bounds on its
  arguments follow from the known inequalities. After the call, the buffer holds fresh unknowns for the
  callee's output words and the verifier records the callee's `ensures` equation as a held definition call.
- **One limit of the contract proved here:** in `examples/kernel/node_out.contract`, `out` is declared as a
  buffer the function may both read and write (`inout 32`), because the kernel it calls reads `out` after
  `b3l_node_out` copies the initial words into it. In `kcheck/proofs/inner.spec`, `out` is write-only
  (the function reads no byte of `out` before writing it); `kcheck/` proves that stronger contract, while
  the Lean verifier does not yet track which bytes of a write-only buffer have been initialized before a
  call.
- **Other limits of this call rule:** the callee must have one read-and-written buffer of words, no
  variable-length buffers, no `mbelow` requirements on its own arguments, and an `ensures` clause of the
  form `bytes_of(DEF(...))`. Mixing byte stores and word stores to the same buffer is rejected. Vector
  registers are forgotten across a call.

`test_node.py` checks both the meaning of the layout lines (evaluated in Lean on random bytes, and against
BLAKE3 on one-block messages) and the verifier itself: the stored 38-byte proof is accepted and reproduced
by the prover, changed proofs are rejected, 28 modified wrong versions of `b3l_node_out` and 10 wrong
contracts are rejected with the expected reasons, and valid variations are accepted.

## The two input files

**What is to be proved** is a text file written by `statement.py` from the object file's bytes and the
specification. (The code and file names call this file the "statement".)

    fn ode_common                 a function; its instructions and contract follow
    i 0 1 .push .rbx              an instruction: start offset, end offset, instruction form and operands
    arg a bytes n                 an input buffer of n bytes (`arg out out 10`: an output buffer of 10 bytes)
    returns (call common (name a) (name b))
    below length 4294967296       the caller keeps this number argument below the bound
    mbelow nd 104 65              the caller keeps the 8-byte number at offset 104 of the buffer `nd` below the bound
    needsif avx512 plat 5         the function needs AVX-512 if the argument `plat` is 5
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
    lane i zmm0 zmm1 = (call f …) in each lane `i` (0 to 15) the words of these vector registers are the
                                  list of words that the definition `f` gives of these things
    t open 1                      unfold this occurrence of a definition
    t held 0 / t carry 0          reuse a value already computed for an equal call of a definition
    t live / t dead               a branch is feasible / infeasible (followed by an arithmetic proof)
    t lt / t eq / t gt            how two values compare (followed by an arithmetic proof)
    t exact / t wrap              at a shift to the left: the number is small enough (an arithmetic
                                  proof follows) / only its low part is kept
    p 0 3 17  /  s 0 1 2 1 1  /  q       an arithmetic proof: which known inequalities it starts from
                                  (by index), steps that each add two inequalities, and the end

## The prover

`prove.py` finds proofs. A verdict does not rely on it: whatever it produces is checked by the verifier, so
a wrong or hostile prover can only produce something the verifier rejects, or nothing.

It works as a dialogue. It gives the verifier the proof so far; the verifier replies with the next thing
it needs (for example, "prove that these inequalities imply that one"); the prover finds it and appends
it. The prover finds arithmetic proofs by eliminating variables. When two rows can serve the same role,
it considers them in the order it received or derived them. That order does not depend on Python's hash
seed. The tests compare the stored proofs with what the prover finds. You can run them with either
CPython or PyPy: `ODE_TESTS=proof-core PYTHON=pypy3 sh tests.sh` from the repository root.

The verifier executable `odeverify` re-checks the whole proof from the first line every time it is asked.
For `ode_adler32_blocks4`, whose proof has 2,023 lines, that meant re-reading 1.2 million proof lines in
total and took 47 of the prover's 62 seconds. So the prover now talks to a helper, `odeprove`
(ProveMain.lean, driven by `session.py`). The helper runs the same verifier code but keeps its position:
when the verifier asks for a proof line that has not been supplied yet, the process forks. The child
continues as if the proof ended there and reports what the verifier says. The parent waits for the next
line. Backtracking to an earlier point is just terminating the later processes.

Time to find each proof, on a 64-thread Zen 4 machine, as measured on November 18. Since then the rules
for shifts to the left, for low parts and for quotients have changed, and the proofs are found with fewer
questions: 47, 202, 737, 2,075 and 76. The times have not been measured again:

| function | questions asked | with `odeprove` | with `odeverify` each time |
|---|---|---|---|
| `ode_common` | 47 | 0.16 s | 0.28 s |
| `ode_adler32` | 204 | 0.58 s | 1.26 s |
| `ode_adler32_blocks` | 763 | 5.3 s | 14.0 s |
| `ode_adler32_blocks4` | 2,101 | 15.2 s | 53.1 s |
| `ode_varint` | 186 | 2.2 s | 6.2 s |

Both ways find byte-for-byte the same proofs (`ODE_PROVE_FROM_START=1` selects the old way). The remaining
time is the prover's own search for arithmetic proofs. A verdict does not rely on `odeprove` either: `prove.py`
returns a proof only after `odeverify` has accepted it, and `test_session.py` checks that the two give
identical answers at every prefix of three stored proofs.

## Measurements (November 19, 2026)

**Speed of the verifier.** 3.5 ms for `ode_common`, 4 ms for `ode_adler32`, 14 ms for `ode_adler32_blocks`,
22 ms for `ode_adler32_blocks4`, 5 ms for `ode_varint`, 12 ms and 13 ms for the two BLAKE3 kernels. Each
figure is a whole run, including process start and reading three files, on an Apple M6 (the median of
eleven runs). The Python verifier in `kcheck/` takes 4, 4, 14 and 27 ms for the first four, 17 ms for
`ode_varint` and 7 and 8 ms for the kernels, not counting its start-up. So the Lean verifier is about as
fast as the Python one on the first four, three times faster on `ode_varint`, and one and a half times
slower on the two kernels.

The 16-way kernel was where this verifier was slow: one block a lane, a path of 1,070 instructions, took
4.1 s, and one or two blocks took 17 s. Three things took nearly all of that time, and each grew with the
square of the path's length. They are mended, and the same two runs now take 0.20 s and 0.66 s:

- **Finding a term in the table of terms.** The table was a list scanned from its start, and a new term
  was put at its end by copying it. It is now an array, with a hash map that says where a term may be
  found. The hash map is advice: the verifier takes a number from it only where it finds that term at
  that number in the array, and otherwise puts the term at the end. So no proof says anything about the
  hash map, and a wrong entry could cost a term a second number and nothing else.
- **Seeing at once that a fact gives a goal.** After every instruction the verifier asks of the stack
  pointer's bounds whether a fact gives each at once. It built the difference of the goal and every fact
  to see whether a number alone was left. It now compares the two lists of multiples where they stand.
- **Finding a quotient the state already knows.** The specification's `hi(t)` and the flag bytes are
  quotients. To find the unknown that is one, the verifier built a difference with every fact. Each
  division made is now noted, and only the unknowns noted for that number and divisor are looked at.
  The note is advice as well: the four facts that make an unknown a quotient are asked for as before.

The stored proofs did not change by a byte through any of the three. What takes the time now, for the
16-way kernel, is evaluating the specification: 81% of the run for every `n`. At the loop invariant the
verifier works out one block's compression for each of the sixteen lanes, on each of four arrivals there,
and each compression works out its final state sixteen times, as the definition is written.

For every `n` this verifier takes 1.08 s on the 16-way kernel, and the Python verifier in `kcheck/` takes
0.20 s. That is 5.4 times as long, which is over the limit of five times described below. The limit's
test does not include this kernel yet; removing the repeated work in the specification's evaluation is
the next change.

For the AVX-512 one-block kernel the specification works out the final state 16 times: twice for each
of the eight result words, as the definition is written.

**Two limits that are enforced by a test** (`test_limits.py`): every stored proof must be under 100 kB,
and a whole run of this verifier must take at most five times as long as the Python verifier takes for the
same function.

**Proof sizes.** A proof is mostly arithmetic. `ode_adler32`: 37 arithmetic proofs. `ode_adler32_blocks`:
two loop invariants and 154 arithmetic proofs. `ode_adler32_blocks4`: three loop invariants, 238 arithmetic
proofs, and 23 places where a definition is unfolded. `ode_varint`: no loop invariant (the loop is unrolled,
at most ten iterations) and one arithmetic proof; it had 111, in 8.7 kB, before the verifier recorded a
bound for each quotient. The two BLAKE3 kernels: two arithmetic proofs each, 131 and 137 bytes.
The `ode_adler32_blocks` proof was 135 kB when each arithmetic proof wrote out the inequalities it starts
from; it now names them by index.

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
| the AVX-512 kernel | 38 | in the specification: a rotation by 15 bits instead of 16, one constant, six rounds, two entries of the message permutation exchanged; in the code: the same kinds of change, a store past the end of the buffer, a store into the read-only block, reading back what was stored |
| the SSE4.1 kernel | 38 | the same changes to the specification; in the contract: no bound on the length; in the code: a left shift by 19 bits instead of 20, an OR with another register, one byte of a shuffle constant, a blend that takes half a word, the flags not shifted |
| the 16-way kernel, for every `n` | 30 | in the contract: the first and the last block's flags exchanged, one block fewer, another lane's blocks; in the code: the first block's flags kept for every block, the next block read two blocks on; in the loop invariant: the chaining value after one block more, two registers exchanged, nothing said of the vector registers |
| the 16-way kernel, one or two blocks | 14 | the last block's flags and its length exchanged; the next counter; a shift that takes the first block's flags from the wrong bits |

Also rejected: a caller listed before its callee, a function that calls itself, a missing callee, and two
functions with the same name.

**Wrong proofs are rejected.** The tests delete or alter single lines of the stored proofs: every line
for `ode_common`, `ode_adler32` and the two BLAKE3 kernels; every third line for `ode_varint`; every
seventh for `ode_adler32_blocks`; and every eleventh for `ode_adler32_blocks4`. The verifier rejects
every alteration that these tests try.

**The arithmetic rule.** All 7,649 arithmetic proofs in the shipped files (17,505 steps) check, in 0.3 s.
On 3,000 deliberately altered proofs, Lean and the Python implementation `varith.py` agree on every one.

**The machine model.** On 5,160 instances of 86 instruction forms, Machine.lean and `conc.py` agree on
registers, flags, memory and the next instruction address. The comparison checks all 16 lanes of each
vector register wherever the table specifies their values. Separate tests check that aligned 512-bit
loads and stores fault on a misaligned address. The single-instruction comparison does not cover
`lea_data`, `call`, or the four other 512-bit forms for memory-operand addition and masks.

**The BLAKE3 specification.** Evaluating `../kcheck/blake3.spec` (29 definitions) in Lean gives the 105
official test vectors (35 input lengths up to 102,400 bytes, in three modes) in 43 s. With one constant in
the specification changed (a rotation by 11 bits instead of 12), it does not.

**Code size.** The formal model: 830 lines. The verifier: 2,071 lines (Core.lean 1,912, Arithmetic.lean
159 including its proofs). The file parser: 179 lines. The proofs of the theorems: 11,697 lines.

## The files

| | |
|---|---|
| the formal model | `Table.lean`, `Machine.lean`, `Contract.lean` |
| the verifier | `Core.lean`; `Arithmetic.lean` (the arithmetic rule and its soundness lemma `refutes_sound`); `Reader.lean` and `Main.lean` (the program `odeverify TABLE STATEMENT PROOF`) |
| the soundness proofs | `SoundLin.lean` (arithmetic on inequalities), `SoundWord.lean` (terms for 32-bit words and their table), `SoundState.lean` (how the verifier's symbolic state relates to a machine state), `SoundStep.lean` (one instruction effect on general-purpose registers), `SoundVec.lean` (one instruction effect on vector registers; 16-byte loads and stores), `SoundSpec.lean` (symbolic evaluation of the specification), `SoundList.lean` (lists and `ensures`), `SoundPlace.lean` (the facts of a loop invariant), `SoundCall.lean` (calls of functions that return a number), `SoundCallW.lean` (calls of functions that write a buffer of words), `SoundSpecW.lean` (evaluation of the specification on terms; `ensures` of a buffer of words), `SoundLoop.lean` (what a loop invariant says of a machine state, vector registers included; first arrival at an invariant and return to it), `SoundTop.lean` (paths and loops: `explore_sound`, by induction on the termination measure; `verify_sound`; `verify_all_sound`) |
| writes the input file (a verdict relies on it for that file saying what the object file and the specification say) | `statement.py` |
| for someone verifying | `lean_verify.py`; the stored proofs in `proofs/`; `examples/equal/` and `examples/low/` (source, specification and object file); `examples/adler32/*.places` (the loop invariants the prover starts from); `examples/kernel/kernel.contract`, `kernel_sse41.contract` and `node_out.contract` (the two BLAKE3 kernels and `b3l_node_out` as they are proved here); `examples/kernel/p16.contract` and `p16.places` (the 16-way kernel and its loop invariant) |
| the prover (a verdict does not rely on it) | `prove.py`, `session.py`, `ProveMain.lean` (`odeprove`) |
| tests | `test_sound.py`, `test_verify.py`, `test_call.py`, `test_adler.py`, `test_blocks.py`, `test_blocks4.py`, `test_varint.py`, `test_low.py`, `test_limits.py`, `test_machine.py`, `test_spec.py`, `test_arith.py`, `test_session.py`, `test_kernel.py`, `test_node.py`, `test_p16_one.py`, `test_p16_table.py`, `test_p16.py`. `MachineMain.lean`, `SpecMain.lean` and `ArithMain.lean` are small programs that three of the tests run. `built.py` runs Lean's build tool once per process. |

The tests are skipped where Lean's build tool `lake` is not installed.
