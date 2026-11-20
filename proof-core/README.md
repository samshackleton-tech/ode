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
also enough for eight of the fourteen functions of the BLAKE3 hash: the two versions of the kernel that
compresses one 64-byte block (one written with AVX-512 instructions and one with SSE4.1 instructions);
`b3l_node_out`, the function that reads a node record and calls the kernel selected by its `plat`
argument; the 16-way kernel, which compresses sixteen chunks at once, block after block, in a loop; the
32-way kernel, which does the same for thirty-two chunks, through each of its two entries (one gives every
chunk the same counter; the other, which the hash calls, gives chunk `i` the counter `t + i`);
`b3l_pad`, which copies the last bytes of a chunk into a block and fills the rest with zeros; and
`b3l_chunk_node`, which calls a one-block kernel for each block of a chunk but the last, calls `b3l_pad`
for the last, and stores three numbers into the chunk's record.
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
    python3 lean_verify.py examples/table/table.spec proofs/ode_third.proof examples/table/odethird.o:ode_third
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
| `ode_third` | returns the third number of a table of constants that lies in its object file's read-only data | 3 instructions | 1 line, 14 bytes | 3 ms |
| `ode_second_block` | compresses the second 64 bytes of a message into a chaining value, by calling the SSE4.1 kernel with the address of those bytes | 8 instructions | 5 lines, 57 bytes | 6 ms with the kernel |
| `ode_absorb` | compresses two blocks into a chaining value kept in the second half of a 64-byte record, by calling the SSE4.1 kernel twice with the address of that half | 21 instructions | 1 line, 15 bytes | 6 ms with the kernel |
| `ode_tail` | pads the bytes of a message from byte 16 on into the 64-byte block of a record, by calling the hash's `b3l_pad` | 7 instructions | 5 lines, 49 bytes | 4 ms with `b3l_pad` |
| `ode_keyed` | copies a 32-byte key out of a 40-byte record, reads the flags that lie beside the key, and compresses one block from them, by calling the SSE4.1 kernel | 11 instructions | 1 line, 14 bytes | 6 ms with the kernel |
| `blake3_servil_compress_in_place_avx512` | BLAKE3's compression function on one 64-byte block: the hash's one-block kernel, written with AVX-512 instructions on 128-bit registers | 76 instructions, 1 loop of 7 iterations | 9 lines, 131 bytes | 5 ms |
| `blake3_servil_compress_in_place_sse41` | the same compression function for processors that have SSE4.1 and no more. It rotates a word by two shifts and an OR, or by a byte shuffle | 94 instructions, 1 loop of 7 iterations | 10 lines, 137 bytes | 5 ms |
| `b3l_node_out` | reads a 120-byte node record from memory, packs its flags, and calls the AVX-512 or SSE4.1 kernel | 18 instructions | 4 lines, 38 bytes | 7 ms with both kernels |
| `blake3_servil_avx512_p16` | the hash's 16-way kernel: sixteen chunks at once, each of `n` blocks read through a table of sixteen addresses, with AVX-512 instructions on 512-bit registers | 460 instructions, a loop over the blocks around a loop of 7 rounds | 204 lines, 2.4 kB | 0.12 s |
| `blake3_servil_avx512_p32` | the hash's 32-way kernel, entered where every chunk gets the same counter: thirty-two chunks at once, each of `n` blocks read through a table of thirty-two addresses | 699 instructions, a loop over the blocks around a loop of 7 rounds | 332 lines, 4.2 kB | 0.60 s |
| `blake3_servil_avx512_k32` | the same kernel entered where chunk `i` gets the counter `t + i`: the entry the hash calls. Six more instructions make the thirty-two counters, with compares into mask registers | 702 instructions, of which 699 are the function above | 332 lines, 4.3 kB | 0.59 s |
| `b3l_pad` | copies the `n` bytes of a chunk's last block into a 64-byte block and fills the rest with zeros; the bytes are secret | 39 instructions, 1 loop of 64 iterations | 38 lines, 451 bytes | 4 ms |
| `b3l_chunk_node` | for a chunk of at most 1024 bytes: compresses each 64-byte block but the last into the chaining value of a 120-byte record, by calling one of the one-block kernels; calls `b3l_pad` to write the last block into the record; stores the chunk's number, the last block's length and the flags there; the bytes are secret | 81 instructions, 1 loop of at most 15 iterations | 663 lines, 5.4 kB | 0.16 s with the three functions it calls |

`ode_equal`, `ode_low`, `ode_eighth`, the four functions of `examples/table/` (`ode_third` is one of
them), `ode_second_block`, `ode_absorb`, `ode_tail` and `ode_keyed` are small examples written for this folder. Five are shipped functions from `kcheck/programs/`. The last eight are eight of the fourteen functions in the shipped
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
  A function whose contract carries its object file's read-only data may read that data as well.
  Functions it calls obey the same limits.
- **Termination.** After finitely many instructions it returns to the return address its caller pushed.
- **Result.** At that point: the stack pointer is just above the return address; the callee-saved
  registers (rbx, rbp, r12 to r15) have their original values; memory outside the stack frame and the
  output buffers is unchanged; `rax` holds the value that the contract's `returns` line specifies; and
  every `ensures` line holds. An `ensures` line has the form `BUFFER[lo .. hi] = LIST` and says that those
  bytes of an output buffer equal a list defined by the specification.
- **Secrets (constant time).** The machine model keeps a mark on each general register, each flag and each
  byte of memory. The mark means "this may depend on a secret". The model moves marks as it moves values:
  a result is marked if any of its inputs is. A vector register always counts as marked. The marks change
  no value. The model *stops* where something marked would become observable: where it is part of an
  address, where it decides a conditional jump, and where it is the address a `ret` returns to. `Meets`
  says that the function never stops in this way. At the return, no general register is marked except
  the callee-saved ones, and memory outside the stack frame and the output buffers has the marks it had.
  The next section says what follows from this.

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
- the function's code is in memory;
- where the function uses constants from its object file's read-only data: the contract carries the bytes
  of that data (`Contract.data`), and the machine state has the address at which the data lies
  (`State.data`). The obligation (`Contract.dataAt`) is that those bytes are in mapped memory at that
  address, apart from the stack frame, the return address and every output buffer, and that none of them
  is marked. On a real machine the linker and the loader fulfil this, not the calling code. That they do
  is not proved here; it is listed below with the link step;
- about marks (`Contract.quietAt`): no general register is marked except the callee-saved ones (rbx, rbp,
  r12 to r15), which may hold anything; the return address is not marked; and no byte of an input buffer
  is marked, except in the buffers that the contract lists as `hidden`. A read-only buffer is `hidden`
  when the contract's `trace depends on` line does not name it.

### Constant time: what an observer can see

    theorem verify_all_trace (world : List Program) (defs : List Def) (fns : List Fn) :
        Linked world fns → verdictAll defs fns = none →
        ∀ f ∈ fns, ∃ p, findProgram world f.name = some p ∧
          ∀ a b, f.contract.pre p a → f.contract.quietAt a → f.contract.pre p b → f.contract.quietAt b →
            Alike a b →
            ∀ a' b', EndsP world p a.plain a' → EndsP world p b.plain b' → a'.trace = b'.trace

In words: suppose the verifier accepts a list of functions. Take one of them, and two machine states `a`
and `b` at its entry. Run the function from each to its return. Then the two runs have the same trace.
The conditions are these.

- Both states satisfy the caller's obligations listed above, including the ones about marks. The marks
  say which registers and bytes are secret, and the obligations limit them. The argument registers, the
  return address, the file's data and every input buffer that the contract does not list as `hidden` must
  not be marked. Anything else may be: the hidden buffers, the callee-saved registers, the flags, and
  memory that is not an input.
- `Alike a b`: the two states have the same marks, are at the same instruction, and agree on every
  register, flag and memory byte that is not marked. They may differ in everything that is marked.
- The *trace* of a run is the list of what the model takes to be observable: the address of each
  instruction executed, and each memory address read or written, with its size.
- The runs are runs of the *plain machine* (`EndsP`, in Plain.lean). The plain machine has no marks and
  forbids nothing: `a.plain` is the state `a` with its marks erased, and every memory access succeeds. So
  the marks appear in this theorem only as a way to say which inputs are secret. The machine that runs
  the function does not have them.

So the theorem says: what an observer of this kind sees does not depend on the secrets.

It is put together from three results, each checked by Lean.

- `ends_trace` (Trace.lean) is about the machine with marks alone, with no verifier and no contract in
  it. That machine moves the marks as it moves values, and it *stops* where something marked would become
  observable. The theorem: two runs of that machine from states that are `Alike`, each reaching the
  function's return, have the same trace.
- The soundness theorem above says that an accepted function never stops that machine.
- `runs_endsP` (Plain.lean) connects the two machines. Where the machine with marks runs a function to
  its return without stopping, every run of the plain machine from the same state is that same run with
  the marks left out. Two lemmas carry it: the marks change no value (`execQ_exec`, `exec_plain`), and
  an instruction that succeeds while only some memory may be touched does the same when all memory may
  be touched (`exec_all`).

Two more consequences are stated on their own. `runs_plain` and `runs_free` say that a run of the machine
with marks, to states of which a property `Q` holds, is a run of the plain machine to those states without
their marks: first with the same memory limits, then with none. So what the soundness theorem says a
function computes, it computes on a machine without marks and without limits.

A called function runs under the same rule. Across a call, the callee-saved registers get back the marks
they had before the call. That is justified because the called function must return them holding the
values they held.

What this does **not** cover:

- **Only this level of observation.** How long an instruction takes for given operands is outside the
  model. So are speculative execution, caches shared with other programs, power and frequency. Each needs
  assumptions of its own.
- **Things the verifier refuses although they are true.** A number passed to a called function in a
  register must not be marked, so `b3l_node_out` is verified with `trace depends on nd`: it loads the
  node's counter, length and flags into registers and passes them to a kernel. A value read back from the
  stack frame counts as marked unless the verifier knows its cell holds nothing marked. It knows that of
  eight bytes of the frame after a store there of a value that is not marked, until those bytes are
  stored to again, any other store to memory that is not such a store to the frame is made, the path
  comes to a loop invariant, or a function is called while the cell is below the stack pointer. So a
  function that keeps a public count in its frame across a call and then branches on it is verified
  (`test_call.py` has such a caller, and three that keep something secret there and are refused); a
  function that keeps it there across a store to an output buffer or around a loop is still refused.
- **A rule for the coder.** A general register that is not callee-saved must not hold anything marked at
  a call or at a return. A function that loads a secret into such a register has to clear it first.

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

An invariant can also say what the loop has written so far to an output buffer. The line names the buffer,
a position `lo` in it, and an application of a definition whose text is a list built element by element
(`[e for k in 0..hi]`). It says: every position `j` of the buffer from `lo` up to `hi` holds element `j`
of that list. On reaching the invariant the verifier checks the positions that are new since the last
time (at most 64 of them): each must be a byte it knows was stored, equal to the element's expression
evaluated at that position. A later single-byte store to the buffer must go below `lo`. At the return, an
`ensures` clause that names the same application of the definition is accepted if `lo` is 0. The verifier
never builds the whole list.

An invariant can also list registers that may be marked (may depend on a secret) when a path comes back
to it, although they were not marked the first time. Without such a line every register that was not
marked on first arrival must still be so on every later arrival.

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
caller's frame, and that each buffer passed lies in one of the caller's own buffers: the same buffer
whole, or a part of it. A part that the callee only reads must lie in one of the caller's read-only
buffers. A part that the callee writes must be whole 32-bit words of a buffer that the caller
may read and write. After the
call it keeps only what the callee's contract guarantees: the callee-saved registers, memory outside the
callee's frame, and the returned value in `rax`. All other registers and the flags become unknown.

Two theorems state the soundness of calls. `verify_sound` is about one function, assuming the functions it calls satisfy
their contracts. `verify_all_sound`, above, removes that assumption by going through the functions in
order.

**Constants in the object file.** A function can take the address of a constant in its object file's
read-only data, as `lea rdi, [rip + table]` does. The instruction table gives that instruction the value
`data(I)`: the address at which the file's data lies, plus the constant's offset `I` in the data. The
verifier keeps one unknown for the address of the data and accepts `data(I)` when `I` is inside the
data. A load of 1, 4 or 8 bytes whose address is the data's address plus a known number, and whose bytes
all lie inside the data, gives a known number: the one that the file's bytes make there. The verifier
reads those bytes from the input file. Such a load is not marked, because the constants of a file are no
secret. A store to the data is rejected. For such a function `lean_verify.py` prints, beside its verdict,
that the place of the data in memory is the linker's part and is assumed.

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
| The formal model: Table.lean (reads `../core/x86.tab`), Machine.lean (the effects on registers, flags and memory, and the marks), and Contract.lean (the meaning of contracts and specifications). 1,021 lines of code. | what the soundness theorem says about the processor and the contract | Read it. The tests below compare parts of it with separate implementations. |
| The steps outside the theorem | what each entry of the second list below says | They are tested, not proved. |

**For the verifier's rules, the reader chooses.** The rules are Core.lean (2,507 lines of code) and the
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
  model `../core/conc.py` on 90 instruction forms from random states. This includes the 512-bit forms
  used by the 16-way and the 32-way kernel, and the forms that use mask registers. `core/cross.py` compares the Python model with real processors.
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
  functions. Where a function takes the address of a constant, it also takes the bytes of the read-only
  data from the object file and works out which offset in that data the instruction refers to.
- **Parsing the specification.** `statement.py` uses `../kcheck/ode.py` to parse the specification text,
  and writes the contracts and definitions in the line format that the Lean program reads. A sequence
  given by a first element and a step is written out as the recursive definition it stands for.
  What is tested here: for each of the eight functions of the hash that are verified, and for four of
  the examples, the formal model in Lean evaluates the `ensures` line that `statement.py` wrote, on
  random inputs, and the result is compared with `../kcheck/ode.py`'s evaluation of the contract's
  expression, with each argument read by its kind by hand (`test_meaning.py`, `test_node.py`,
  `test_chunk.py`, `test_part.py`, `test_record.py`, `test_tail.py`, `test_keyed.py`). That is a test on
  some inputs. It
  is no proof that `statement.py` is right.
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
- **Linking** (the `Linked` assumption above). For a function that uses its object file's read-only
  data, also that the data's bytes are in memory where the function's instructions look for them. The
  model has one address for the data of all functions, which fits functions linked from one object file.
  For `../kcheck/b3hashr.o`, which holds code and constants in one section of 17,856 bytes, the data that
  `statement.py` gives is that whole section.

A proof file cannot change what is being proved. The input (what is to be proved) and the proof are two
separate files, and a line of an input kind inside a proof file is rejected. The only string in the input
that comes from the author is the name of a called function. The decoder rejects a name that is not a
single plain word, and `statement.py` rejects a line containing a line break.

## What is supported so far

**Instructions.** Instruction forms over the general-purpose registers, the zero and carry flags, and
memory operands of 1, 4 and 8 bytes; jumps; calls to functions in the same input. The verifier has rules
for: add, subtract, compare, shift left by a constant, shift right by a constant, AND with a mask of the
form 2^k - 1, taking the low 32 bits or low 8 bits of a register (`mov ecx, esi`, `movzx eax, dil`),
8-byte stores to a stack slot, 1-byte stores to an output buffer, 8-byte stores of a number into a
buffer of 32-bit words (as its two words), and setting or decrementing the low byte of a register
(`mov al, 7`, `dec al`).

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
the low 32 bits of the register are the argument. A contract can also carry the read-only data of the
function's object file. `statement.py` adds it for every function that takes the address of a place in
that data; no line of the specification asks for it.

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
function's own instructions are of kinds its `needs` lines name. A read-only buffer that the `trace depends on` line does not name becomes a `hidden` line: its bytes may be secret. This holds for a fixed-size buffer and for one whose length is an argument. (A function that calls another may hand it a hidden buffer only if the called function's contract hides it too.) It refuses specifications that use a kind, a lemma, or a definition that can fail. A layout is read where an argument is a record of that layout.
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

**The constant-time promise of the kernels' contracts is proved.** The kernels' real contracts
(`../kcheck/proofs/inner.spec`) have no `trace depends on` line: the execution trace must not depend on
the message block, the key or the chaining value. The contracts used here (the five kernel contracts in
`examples/kernel/`: the 32-way kernel has one for each of its entries) say the same, and the verifier
accepts each. `test_kernel.py` changes
each one-block kernel so that it branches on a word of the message block, and so that it leaves such a word
in a general register: both are refused. `test_p16.py` and `test_p32.py` mark the table of block addresses
as secret too: refused, because the blocks are read at those addresses. The contract of `b3l_node_out` still says
`trace depends on nd`, for the reason given above.

**A loop that fills a buffer: `b3l_pad`** (`test_pad.py`). The function copies the `n` bytes of a chunk's
last block into a 64-byte block, from the last position down, and writes zeros where the input has ended.
Its contract is the one in `../kcheck/proofs/inner.spec`, unchanged: `ensures block = padded(src)`, where
`padded` is `[if k < len(bytes) then bytes[k] else 0 for k in 0..64]`. The contract has no
`trace depends on` line, so the input bytes are secret; the function branches on `n` and on its counter
only. The loop invariant (`examples/hash/pad.places`) is four lines: the counter `i` is at most 64, the
block holds `padded(src)` from position `i` on, and `i` decreases. The prover adds that `rax` may be
marked on a later arrival (it holds the byte just copied). The proof is 451 bytes.

**Constants in the object file: `examples/table/`** (`test_table.py`). Four small functions take the
address of a table of eight 32-bit numbers in their object file and read from it: four bytes; eight
bytes; one byte, after moving the address on by four; and four bytes that then decide a jump. The
verifier accepts all four, and each proof is the one line that names the function. The tests change the
code in ten ways and the contracts in four, and the verifier refuses each. Among them: another number of
the table is read, a read ends past the end of the table, the table is stored to, the table holds another
number. The tests also change the input file itself. Without its `data` line, taking the address is
refused. With one byte of the data changed, the value returned is no longer the contract's. With the data
cut short, the read is outside it.

This is the first step of a new way to describe memory, in which each run of memory that a function may
touch is a declared *piece* and no address exists without its piece ([DESIGN.md](../DESIGN.md), section
5). The file's data is the simplest piece: read-only, with known bytes. The stack frame is to
follow, and then the buffers of a contract.

### Known limitations

These are cases where the verifier rejects a correct function:

- The object file's read-only data can be read by loads of 1, 4 and 8 bytes, at an address that is the
  data's address plus a known number. A table indexed by a register whose value is not a known number
  (`[table + 4*i]`) is rejected. Vector loads from the data have no rule of this kind yet. The forms that
  the kernels use (a constant repeated in every lane, a 16-byte constant, a 64-byte constant added) are
  still decoded with the constant's value written into the instruction, as before. A function whose
  contract carries data cannot be called by another function yet. The address just past the end of the
  data cannot be taken.

- A buffer that a called function only reads can be a part of one of the caller's read-only buffers. A
  buffer that it reads and writes can be a part of a buffer that the caller may read and write, in whole
  32-bit words; so can a buffer that it only writes. For a buffer of words the offset must be a known
  number. For a read-only buffer whose length is an argument the offset may be a linear expression that
  one known inequality bounds. A callee that writes more than one buffer, or that also returns a
  number, is not called yet.
- The return value of a called function is known only as "the value of this call of this definition". It
  can be used where the caller's contract mentions the same definition with provably equal arguments.
- No rule yet for: AND with a constant that is not a mask, OR, shift by a register, a 4-byte load.
- Nothing may be written below the stack pointer.
- Output buffers of bytes: only single-byte stores (and, into a buffer kept as 32-bit words, 8-byte stores
  of a number at an offset that is a known multiple of four); the function cannot read back what it wrote; single
  bytes written before a loop invariant are forgotten at the invariant, unless the invariant says what the
  buffer holds from some position on (one such line per invariant, growing downward, compared with a
  definition that is a list built element by element from 0); a called function cannot write to the
  caller's output buffer. A store to the stack frame, a vector store, or a call makes the verifier forget
  what an invariant said about an output buffer.
- A loop invariant's `lane` and `cell` lines are evaluated on values the verifier has already computed. A
  number that such a line names, and that the code does not compute on every path to the invariant, must
  also be named by a fact of the invariant (the 32-way kernel's invariant has two such facts).
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
An addition or an exclusive OR can take its second operand from memory (`vpaddd zmm, zmm, [mem]`). The
verifier reads the sixty-four bytes first, by the rules for a load, and then combines the lanes.

A test verifies a six-instruction function from its object file against a contract that adds sixteen
pairs of words. It refuses a version that reads both operands from the same vector.

The verifier can also follow an `and` that rounds the stack pointer down to a 64-byte boundary. When
the exact offset from the entry stack pointer is unknown, the proof must show that the new pointer
stays within the frame and that any saved words stay at or above it. The verifier records those facts
rather than asking for the same proof at each instruction. A test checks the same proof with and
without 80 intervening instructions that do not change the stack pointer.

The verifier can also write and reload 64-byte vectors in the aligned stack frame. It checks the
whole slot, its alignment, and that the store ends before any saved scalar word. It remembers every
vector stored, each with its slot's offset. A new vector store keeps the slots that it can see are 64
bytes or more away (their offsets differ from the new one's by a number alone) and forgets the others.
A scalar store, a call or exit from the aligned frame makes it forget all of them. It verifies copies
from object bytes that clear the registers between the stores and the reloads, with one slot and with
two side by side. Tests reject a reload from another slot (with two slots: each read back from the
other's, which is a false statement), a slot stored to twice and read as holding the first vector, a
store whose address lacks the required alignment, and a stack adjustment that would leave the slot
below the stack pointer.
A vector stored to such a slot can also be read by an unaligned 64-byte read at exactly the slot's
address. That address may be the sum of a register that points into the frame and a number that the
function read from a table of constants.

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
`examples/kernel/p16.contract`: the contract of `../kcheck/proofs/inner.spec`. It has no `trace` line,
so the trace depends on no byte of the blocks or of the key. The addresses in the table `inputs` are
treated as numbers passed to the function, like `n`: the trace does depend on them.
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
2,350 bytes and the verifier takes 0.12 s. It walks six paths: the first block with `n` equal to 1 and
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
the proof is 921 bytes and the verifier takes 35 ms. For one or two blocks the proof is 1,440 bytes and
the verifier takes 95 ms. Those tests refuse ten changed contracts and four changed instructions.

Two more rules were needed. A broadcast of a register's low 32 bits makes the word of the register's
number directly, so that the specification's `lo(t)` is the same term. And in the specification, numbers
that the verifier holds as sums of unknowns can now be added, subtracted, divided by a constant where the
state already holds that quotient, and compared. A comparison is decided only where the facts show at
once that the two numbers are equal, or that one is the greater.

One limit to know of: the verifier takes an OR of three numbers only in the grouping the code computes.
With one block a lane, a contract that exchanges the first block's flags with the last block's says the
same thing, since all three bytes go into one word. The verifier refuses that contract. It refuses a true
statement there; it does not accept a false one.

**The 32-way kernel.** `test_p32.py` verifies the shipped bytes of `blake3_servil_avx512_p32` (699
instructions in `../kcheck/b3hashr.o`) against the contract of `../kcheck/proofs/inner.spec` (here
`examples/kernel/p32.contract`). It does so twice: first with the contract narrowed by one line and no
loop invariant, then with the contract as it stands.

Narrowed by `requires n < 2`, for one block a lane, the proof is 1,270 bytes and the verifier takes 0.15 s.
Narrowed by `requires n < 3`, for one or two blocks, the proof is 2,127 bytes and the verifier takes 0.44 s.

This kernel differs from the 16-way kernel in two ways that needed new rules. First, it looks up the order
of the message words for each round in a table in the object file (the rule for constants, above). Second,
it keeps the message words in sixty-four-byte slots of its stack frame and adds them straight from memory:
`vpaddd zmm0, zmm0, [rsi + rax]`, where `rsi` points into the frame and `rax` holds the number just read
from the table. The formal model had no meaning for an operation with a memory operand. So the model
changed as well as the verifier: Machine.lean now says that such an operand is the sixteen words at that
address, and `test_machine.py` compares that row with the Python model.

The tests change the contract in twelve ways, the code in eleven and the data in two, and the verifier
refuses each. Among them: the two halves of the lanes exchanged; lane `i` given the counter `t + i`, which
is what the kernel's other entry computes; another message word added; sixty-four bytes read across two
slots; the table's address moved by four bytes; one number of the table changed.

The contract as it stands, for every `n`, needs a loop invariant, as the 16-way kernel's does. It is in
`examples/kernel/p32.places`:

    place +0xf44 {
        name left = r13
        name off = r14
        fact left >= 1
        fact left <= n
        fact off == 64 * (n - left)
        fact end <= 255
        fact length <= 255
        lane i: zmm0 .. zmm7 = chunk(key, t, flags, start, end, length, n, inputs[i]) after n - left + 1
        lane i: zmm8 .. zmm15 = chunk(key, t, flags, start, end, length, n, inputs[i + 16]) after n - left + 1
        cell [rsp + 2048]: word i = lo(t)
        cell [rsp + 2112]: word i = hi(t)
        cell [rsp + 2176]: word i = lo(t)
        cell [rsp + 2240]: word i = hi(t)
        decreases left
    }

Three things in it are new.

- There are two `lane` lines, one for each half of the thirty-two lanes.
- There are four `cell` lines. Before its loop the kernel stores the counter's low and high words in four
  sixty-four-byte slots of its stack frame, and it reads them back in every iteration. A `cell` line says
  what such a slot holds: word `i` of the sixty-four bytes at that distance above the stack pointer is the
  given word of the specification. On every arrival at the invariant the verifier checks the line against
  the vector it knows was stored there. In the iterations that follow it reads the slot as holding those
  words. Without the line it would know nothing about the slot: what it knows about stored vectors is
  forgotten at an invariant unless the invariant says it.
- There are two facts that look idle, `end <= 255` and `length <= 255`. The kernel computes the last
  block's flags and its length only when the block is the last one. The `lane` lines name both numbers on
  every path. The verifier evaluates a `lane` line on values that it has already computed, and it computes
  a number of the specification itself only where a fact names it. The two facts make it compute them.
  Without them the invariant is still true, and the verifier refuses it. That is a limit of the verifier,
  and a test records it.

One rule of the verifier changed. When the specification divides a number that is known at once to be
non-negative, the verifier now records the same facts about the quotient as it records when the code
divides: the quotient is non-negative, and it is bounded where the dividend is. Before, a quotient first
met in the specification was not recognized when the code computed it later. Two stored proofs
(`ode_adler32_blocks` and `ode_adler32_blocks4`) were found again because of this change.

With the invariant the verifier accepts the contract for every `n` from 1 up. The proof is 4,178 bytes.
The verifier takes 0.60 s, and the Python verifier takes 0.40 s for the same function. (It took 1.2 s
when this was first verified; the section on speed below says what was mended.) This function and its
other entry have the slowest ratio of any function here. The cause is known. The verifier stores an
inequality as a list with one entry for every unknown, this function has more than 1,300 unknowns by its
end, and the unknowns of a later iteration come last.

The tests change the contract in twelve ways, the code in seven and the invariant in fourteen, and the
verifier refuses each. Among the invariants: a slot said to hold the counter's low words where it holds the
high ones; a slot four bytes further on; the two halves of the lanes exchanged; nothing said about a slot;
nothing said about the upper half of the lanes. Among the instructions: the counter's low words read from
the slot of its high words; a message word stored over one of the counter's slots.

**The entry the hash calls.** The hash calls this code through its other entry,
`blake3_servil_avx512_k32`, which gives lane `i` the counter `t + i`. `test_k32.py` verifies it: 702
instructions, of which 699 are the function above, against the contract of `../kcheck/proofs/inner.spec`
(here `examples/kernel/k32.contract`). Its `ensures` line is
`out[i] = chunk(key, t + i, flags, start, end, length, n, inputs[i])` for the thirty-two lanes.

Entered here, the kernel executes six instructions that the other entry jumps over. They make thirty-two
counters from the one given.

- Two add the numbers 0 to 15 and 16 to 31 to the counter's low word (`vpaddd zmm2, zmm0, [rip + ...]`).
  The sixteen numbers are a constant in the file's read-only data, and the decoder puts them into the
  instruction.
- Two compare each sum with the low word and write the result into a mask register, one bit a lane
  (`vpcmpud k1, zmm2, zmm0, 1`). The bit is set where the sum is the smaller, which is exactly where the
  addition wrapped at 2^32.
- Two add one to the high word in the lanes whose bit is set (`vpaddd zmm5{k1}, zmm1, zmm4`).

The formal model had no mask registers. It has them now. Machine.lean gives a meaning to a compare into
one of the registers k1 to k7 and to an addition under one, and `test_machine.py` compares both rows of
the table with the Python model, together with the row that adds a constant of the file. The model keeps
a mask register's sixteen bits as sixteen lanes, beside the lanes of the vector registers. It gives no
meaning to an instruction that names k0: where an instruction is written under a mask, k0 tells the
processor "no mask".

The verifier got two new kinds of term for a 32-bit word: "1 if this word is below that one, else 0", and
"this word if that one is not zero, else a third". On the specification's side there are two new rules. A
number added to a counter gives a counter, so `t + i` can be evaluated. And the high word of such a
counter is looked up in the form in which code computes it: the high word of `t`, or that plus one,
chosen by whether the low word of the sum is below the low word of `t`. A lemma (`hiPlus_sound`) proves
that this is the high word of `t + i` for every 64-bit `t`, including the values at which the low word,
or the whole counter, wraps.

The loop invariant is the other entry's with the counters changed (`examples/kernel/k32.places`): lane `i`
of the first half has the counter `t + i`, lane `i` of the second half has `t + i + 16`, and the four
slots hold `lo(t + i)`, `hi(t + i)`, `lo(t + i + 16)` and `hi(t + i + 16)` in word `i`.

With it the verifier accepts the contract for every `n` from 1 up. The proof is 4,331 bytes. The verifier
takes 0.59 s, and the Python verifier takes 0.40 s.

The tests change the contract in ten ways, the code in fourteen and the invariant in five, and the
verifier refuses each. Among them: every lane given the counter `t`, which is what the other entry
computes; the kernel entered with the other entry's setting; two of the sixteen numbers exchanged; the
compare the other way round; no carry into the high word, which is wrong only for the few counters whose
low word is about to wrap; the first half's high words changed under the second half's mask; an addition
under a mask register that no instruction has set.

**A called function is given a part of a buffer: `examples/part/`** (`test_part.py`).
`ode_second_block(h, input, len)` compresses the second 64 bytes of a message into the chaining value `h`.
It adds 64 to the message's address and calls the SSE4.1 kernel. Its contract is
`ensures h = compress(h, words(input[64 .. 128]), counter(0), 64, 0)`, with `requires len >= 128`. Three
things were refused before:

- **A part of a read-only buffer whose length is an argument, passed as a callee's fixed-size buffer.** The
  verifier accepts it where the address is the buffer's address plus a known number, and where one known
  inequality shows that the part ends inside the buffer (here `len >= 128`). The soundness proof shows
  what the callee's contract requires of that part: it lies in memory, apart from the callee's frame, the
  return address and every buffer the callee may write; every memory cell in it holds a byte value; and
  the callee reads nothing the caller may not read.
- **The caller's own read-and-written buffer, passed on before anything was written to it.** Its words
  are then the words it held at entry.
- **`words(input[64 .. 128])` in the specification**, for a buffer whose length is an argument. The words
  of such a buffer are leaves of the term table, like the words of a fixed-size buffer.

The proof is 57 bytes: one arithmetic proof, that adding 64 to the address does not pass 2^64. The tests
change the contract in eight ways and the code in ten, each making the statement false, and each is
refused. Among them: `requires len >= 127` (the block could end one byte past the message); the contract
names another block; the code passes `input + 65`.

**A called function reads and writes a part of a buffer: `examples/record/`** (`test_record.py`).
`ode_absorb(r, m, m2)` keeps a chaining value in the second half of a 64-byte record `r`. The first half
is a tag that the function leaves alone. It calls the SSE4.1 kernel twice with the address `r + 32`: once
with the block `m`, once with the block `m2`. The contract names the record's fields by a layout:

    layout tagged 64 { tag: cv at 0, h: cv at 32 }
    ensures r = {tag: r.tag, h: compress(compress(r.h, m, counter(0), 64, 0), m2, counter(0), 64, 0)}

What is new:

- **A part of a buffer that the caller may read and write, passed to a callee that reads and writes it.**
  The verifier accepts it where the address is the buffer's address plus a known multiple of four, the
  part ends inside the buffer, and every 32-bit word of the part is known. After the call those words are
  the callee's output words. What was known of the buffer's other words stays known: the soundness proof
  shows that the callee can change memory only in its own frame and in the part it was given.
- **A buffer that has not been written to yet is first recorded as holding its entry words.** Before, the
  verifier kept one fact for such a buffer: "nothing has been written to it". After a call that writes a
  part, that fact is gone, and the words outside the part would be lost. So before the call the verifier
  records each word of the buffer as the word it held at entry (`Sym.touch` in Core.lean; `touch_carried`
  in SoundCallW.lean).
- **`ensures` of a whole record.** `statement.py` writes the record that the contract names as the
  record's words, one field after another. It takes a layout whose fields are chaining values or runs of
  bytes that fill the record without a gap. (A field that is a number: see `b3l_chunk_node` below.)

No arithmetic proof is needed: the stored proof is the function's name. The tests change the contract in
seven ways and the code in thirteen, each making the statement false, and each is refused. Among them: the
contract says that the tag becomes the old chaining value; the code passes `r + 36`, so that the last
word would lie past the record; the code passes `r`, so that the kernel overwrites the tag; one byte of
the chaining value is written between the two calls; the contract allows one byte less of stack.

**A called function writes bytes into a part of a buffer: `examples/tail/`** (`test_tail.py`).
`ode_tail(r, src, len)` calls `b3l_pad`, the hash's own padding function, as it lies in
`../kcheck/b3hashr.o`. The record `r` is 96 bytes: a chaining value, then a 64-byte block. `b3l_pad` is
given `r + 32` to write, and `src + 16` with the length `len - 16` to read. The contract:

    layout tailrec 96 { h: cv at 0, block: 64 bytes at 32 }
    requires len >= 17
    requires len <= 80
    ensures r = {h: r.h, block: padded(src[16 .. len])}

What is new:

- **A call of a function that only writes its buffer**, with a contract of the form
  `ensures block = padded(src)`: the buffer then holds, byte by byte, the list that a definition gives
  (`symCallB` in Core.lean; `symCallB'_sound` in SoundCallW.lean). The buffer must be whole 32-bit words
  of a buffer that the caller may read and write, each of them known. After the call those words are
  fresh unknowns, and the verifier records that the definition, applied to the callee's arguments, gives
  the bytes of those words.
- **A read-only buffer whose length is an argument, passed as a part.** The callee's buffer starts at an
  offset in the caller's buffer and has its own length. Offset and length are linear expressions. The
  verifier accepts the call where one known inequality shows that the offset is not negative, and one that
  the part ends inside the caller's buffer.
- **In the specification:** `src[16 .. len]` (a slice whose end is an argument) and `len(...)` of such a
  buffer or slice.
- **One new fact about the formal model: memory changes only by stores of bytes** (`runs_bytes` in
  Trace.lean). A contract says what a buffer holds as a list of numbers. The caller treats the buffer as
  32-bit words, so it needs each number to be below 256. The theorem says that after any run of a
  function each memory address holds what it held before or a number below 256. Together with "every
  word of the part was known before the call" this gives that each byte of the part is below 256
  afterwards.

The stored proof is 49 bytes. The tests change the contract in seven ways and the code in twelve, each
making the statement false, and each is refused. Among them: the contract says the block holds bytes 16
to 80, which a shorter message does not have; the code gives `b3l_pad` one byte more to read, a byte past
the message; the code gives it `r + 28` to write, so that it would overwrite the last word of the
chaining value.

**Two true statements are refused, and a test records them as limits.** With `requires len >= 16` the
statement is still true: `b3l_pad` is then given zero bytes to read. The verifier refuses it, because
`src + 16` could then equal 2^64, and its rule for an addition requires the sum to stay below 2^64. With
`requires len <= 81` the statement is also still true: `b3l_pad` is then given 65 bytes, and as it is
written it copies the first 64 of them, which is what `padded` gives. The verifier refuses it, because
`b3l_pad`'s contract allows at most 64 bytes, and a call is verified against the callee's contract alone,
whatever the callee's instructions would do. The second limit is by design.

Not yet: an offset that is not a known number (a loop invariant about a walk through a message would
need that).

**`b3l_chunk_node` is verified, with the two one-block kernels and `b3l_pad` that it calls**
(`test_chunk.py`). It is the function as it lies in `../kcheck/b3hashr.o`, 81 instructions, with the
contract and the layout of `../kcheck/proofs/inner.spec` as they are written there:

    layout node120 120 { h: cv at 0, block: 64 bytes at 32, counter: number at 96, length: number at 104 below 65, flags: byte at 112 }
    contract b3l_chunk_node(nd: node120, input: len bytes, len: number, t: number, flags: byte, plat: any) {
        requires no_overlap(nd, input)
        requires len <= 1024
        ensures nd = chunk_node(nd.h, t, flags, input)
        stack 256
        needs sse41
        needs avx512 if plat == 5
    }

A chunk is at most sixteen blocks of 64 bytes. The function gives each block but the last to a one-block
kernel, which compresses it into the first 32 bytes of the record `nd`. It has `b3l_pad` write the last
block into the record at byte 32. Then it stores three numbers of eight bytes each: the chunk's number,
the last block's length and the flags. The contract has no `trace depends on` line, so the verifier also
shows that the instructions run and the addresses touched depend on no byte of the input or the record.

**The loop has no invariant.** The length is at most 1024, so the loop runs at most fifteen times, and the
verifier goes through every number of iterations, each with the inequalities then known about the
length. (An invariant would have to say "the chaining value after `k` blocks" for an unknown `k`, which
the verifier's evaluation of the specification cannot follow yet.) The stored proof is 663 lines, 5.4 kB:
the arithmetic for each number of iterations and each way the comparison of `plat` with 5 can go.

What the verifier takes here that it refused before, each with its soundness proof:

- **Eight bytes of a number stored into a buffer the function may read and write**, at an offset that is a
  known multiple of four. Two 32-bit words of the buffer then hold the number's low half and its high
  half (`symStore8` in Core.lean; `symStore8_sound` and `store8_words` in SoundCallW.lean). A buffer that
  has not been written to yet is first recorded as holding its entry words, as before a call.
- **A callee may write a part of such a buffer while cells of the stack frame are known not to depend on a
  secret.** Before, the rule for secrecy at a call accepted only the whole buffer. Likewise, a store into
  such a buffer at a known offset inside it leaves those cells as they were.
- **`x | 0` in the code is `x`.** After the first block the function ORs the flags with 0.
- **In the specification:** `the least number n in a..b with …`, each candidate decided by an inequality
  the verifier already holds; `<` and `>=` between such numbers; `|` of such a number and a constant,
  where the code has ORed the same two.
- **A written record with number fields.** `statement.py` writes each number as the two words of its eight
  bytes, low word first, under the condition that the number is below what the layout requires (`below`;
  256 for a `byte`; otherwise 2^64). Where the number is not below that, the expression has no value,
  the `ensures` is false, and nothing is accepted. The record that the contract names is bound once, by
  a `let`, and each field is taken from it.

`test_chunk.py` checks three things. First, the meaning of the lines `statement.py` writes: the formal
model in Lean evaluates the `ensures` line on random inputs of 0 to 1024 bytes and gives the 120 bytes
that `../kcheck/ode.py` gives for `chunk_node`; and the node of a one-chunk message, taken as the root,
gives the BLAKE3 hash of the message. Second, the verifier accepts the stored proof and the prover finds
it again; a proof with a line removed is rejected. Third, 33 false statements are refused, each with the
expected reason: 12 changes to the contract and 21 to the code. Among them: the contract allows 1025
bytes; the contract says the length field is below 64, which a last block of 64 bytes is not; the code
marks no block, or every block, as the chunk's first; the code counts 60 bytes for a block, so that a
kernel would read past the input; the code stores the flags four bytes past the record; the code calls
the AVX-512 kernel where `plat` is not 5. Six changed versions that are still correct are accepted.

**A key and its flags, read from a record: `examples/keyed/`** (`test_keyed.py`). No rule of the verifier
is new here. The example is the first steps of a parent node as the hash's `b3l_take` and `b3l_subtree`
take them, and the test keeps what those two functions will rely on. `ode_keyed(out, m, kf)` copies the
key into `out` by two 16-byte moves through a vector register, reads the flags, and calls the SSE4.1
kernel, which reads and writes `out`. The record is the hash's own:

    layout keyed 40 { key: cv at 0, flags: byte at 32 }
    ensures out = compress(kf.key, m, counter(0), 64, kf.flags)
    trace depends on kf

The stored proof is one line. The tests change the contract in seven ways and the code in fourteen, each
making the statement false, and each is refused. Among them: the layout has the flags first; one half of
the key is not copied, or is stored four bytes late, past `out`; the flags are read from the key's last
eight bytes, or one byte past the record. Three changed versions that are still correct are accepted.

**One true statement is refused, and a test records it as a limit.** Without `trace depends on kf` the
record is hidden, and so are the flags read from it. The function would still be constant time in them:
the kernel's instructions and the addresses it touches do not depend on its flags. The verifier refuses
the call, because it accepts a call only where no register that the callee is given may depend on
something hidden. So today a function that hands the key's flags to a kernel must name the whole record
in `trace depends on`, and its theorem then says nothing about the trace and the key. Five of the six
functions of the hash that are still to be verified read the flags from such a record and hand them on
in a register (`b3l_wide32`, `b3l_wide128`, `b3l_take`, `b3l_part32`, `b3l_subtree`).

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
- Calling a function that only writes a buffer, whose contract says that the buffer then holds the list
  a definition gives (`symCallB` in Core.lean, proved sound in SoundCallW.lean): see `examples/tail/`
  above.
- Calling a function that writes a buffer of 32-bit words for its caller (`symCallW` in Core.lean, proved
  sound in SoundCallW.lean): the verifier checks that the callee's stack frame fits, that its read-only
  buffer arguments lie inside the caller's read-only buffers, that its read-and-written buffer
  is whole words of a read-and-written buffer of the caller, each of them known,
  and that any numeric bounds on its arguments follow from the known inequalities. After the call, the buffer holds fresh unknowns for the
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
    data 0200000003000000…        the bytes of the object file's read-only data, in hexadecimal
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
    cell 2048 i (call lo …)       word `i` (0 to 15) of the sixty-four bytes that lie 2048 bytes above the
                                  stack pointer is the word that this expression gives
    wrote block (index (call f …) (name i))            from position `i` on, the output buffer `block` holds
                                  the list that the definition `f` gives, position by position
    marked rax                    registers that may depend on a secret on a later arrival
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

## Measurements (November 19 and 20, 2026)

**Speed of the verifier.** 3.5 ms for `ode_common`, 4 ms for `ode_adler32`, 14 ms for `ode_adler32_blocks`,
22 ms for `ode_adler32_blocks4`, 5 ms for `ode_varint`, 5 ms for each of the two BLAKE3 kernels. Each
figure is a whole run, including process start and reading three files, on an Apple M6 (the median of
eleven runs). The Python verifier in `kcheck/` takes 4, 4, 14 and 27 ms for the first four, 17 ms for
`ode_varint` and 7 and 8 ms for the kernels, not counting its start-up. So the Lean verifier is about as
fast as the Python one on the first four, three times faster on `ode_varint`, and somewhat faster on the
two kernels.

The 16-way kernel was where this verifier was slow: one block a lane, a path of 1,070 instructions, took
4.1 s, and one or two blocks took 17 s. Three things took nearly all of that time, and each grew with the
square of the path's length. They are mended, and the same two runs then took 0.20 s and 0.66 s:

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

The stored proofs did not change by a byte through any of the three.

A fourth was in how the specification is written out for the verifier. `compress` ends with
`[s[7][i] ^ s[7][i + 8] for i in 0..8]`, and `s[7]`, the state after seven rounds, was worked out again
at each of its sixteen uses. `statement.py` now writes a `let` around the definition's value, so that
such a value is worked out once. With the loop invariant the 16-way kernel for every `n` took 1.08 s,
which was 5.4 times the Python verifier's 0.20 s and over the limit described below. It now takes 0.38 s,
1.9 times. (The secrecy marks, added later, had made it 0.42 s: the state before each statement was kept
while the statement was worked on, so the table of words was copied. The marks are now worked out from
the registers and the list of clean registers alone.) The two one-block kernels went from 12 and 13 ms to 5 ms each, and the two runs above to
0.06 s and 0.19 s. The Lean evaluation of the specification still gives the 105 official test vectors.

On November 20 three more things were mended. A sampling profiler found them on the 32-way kernel:

- **The table of terms was still copied** at every 512-bit operation that combines two registers. The
  state was held in two places while the new terms were added, so the first new term copied the whole
  table. The table is now taken out of the state for that moment, and the registers are looked up before
  the state is handed on.
- **Finding a quotient the state already knows** compared rows by the equality that Lean derives for the
  type, which is slow, and went through every unknown of the state. Rows are now compared number by
  number, and only the unknowns noted for that division are looked at.
- **Seeing at once that two numbers are equal** built two new rows for every fact. It now compares the
  lists of multiples where they stand.

The 16-way kernel for every `n` went from 0.38 s to 0.17 s, which is less than the Python verifier's
0.20 s. One block a lane went from 0.06 s to 35 ms, and one or two blocks from 0.19 s to 95 ms. The 32-way
kernel went from 0.40 s to 0.15 s for one block a lane, and from 1.25 s to 0.44 s for one or two. The
stored proofs did not change by a byte, and the proofs that the tests find for the 32-way kernel are the
same bytes as before.

For every number of blocks the 32-way kernel then took 1.2 s, and 1.4 s by the entry the hash calls: three
and three and a half times the Python verifier's 0.40 s. Later on November 20 four more things were
mended, again found with the sampling profiler:

- **An index of the table of terms was built again at every use.** Where the verifier evaluates the
  specification, it looks terms up by what they are. It built a hash index of the whole table for that at
  every line of a loop invariant that says what a vector register or a slot of the frame holds, at every
  `ensures` about words and at every call that writes words. The table carries such an index already, and
  the verifier now reads that one, in the way it does when it adds a term: a number from the index is
  taken only where that term stands at that number in the array. The soundness proofs of the
  specification's evaluation ask one thing of a lookup, that a number it gives holds that term, and no
  longer speak of a scan of the table.
- **Seeing at once that so many times a fact gives a goal** looked for the goal's last multiple once for
  every fact. It now looks for it once.
- **Finding a quotient the state already knows** asked, of each unknown noted for that division, whether
  the four facts that make it a quotient were among the facts. That built four rows and went through
  every fact four times. A division the state has made is now a thing it knows, in the way it knows a use
  of a definition or a block that was read: the soundness proof carries that the unknown is the quotient
  and the next unknown the remainder. Finding it again goes through no fact. (This section
  says above that the note of a division is advice. That was so until this change; now the proof speaks
  of it.)
- **The bounds of the stack frame were shown again after every instruction** in a function that aligns
  its stack pointer, though few instructions move the stack pointer or store into the frame. The state now
  notes the stack pointer, the frame's saved words and the spilled vectors as they were when the bounds
  were last shown. While they are the same, nothing is shown again. This note is advice: the step only
  adds facts it has shown, so a wrong note could leave a fact out and could add none that is false.

The 32-way kernel went from 1.2 s to 0.60 s, and by the entry the hash calls from 1.4 s to 0.59 s: one and
a half times the Python verifier's 0.40 s. The 16-way kernel went from 0.17 s to 0.12 s. The stored proofs
did not change by a byte through any of the four.

What takes the time now is evaluating the specification at the loop invariant (for each lane the
verifier works out one block's compression, on each arrival there), and the size of the rows: an
inequality is a list with one entry for every unknown, the 32-way kernel has more than 1,300 unknowns by
its end, and a term of the table that is such a row is hashed and compared entry by entry.

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
| the four functions of `examples/table/` | 14 | another number of the table read; a read that ends past the table's end; a store to the table; another number in the table |
| `ode_equal` (the caller) | 16 | keeping a value in a register that a call may change; passing part of a buffer; moving the stack pointer |
| the AVX-512 kernel | 38 | in the specification: a rotation by 15 bits instead of 16, one constant, six rounds, two entries of the message permutation exchanged; in the code: the same kinds of change, a store past the end of the buffer, a store into the read-only block, reading back what was stored |
| the SSE4.1 kernel | 38 | the same changes to the specification; in the contract: no bound on the length; in the code: a left shift by 19 bits instead of 20, an OR with another register, one byte of a shuffle constant, a blend that takes half a word, the flags not shifted |
| the 16-way kernel, for every `n` | 30 | in the contract: the first and the last block's flags exchanged, one block fewer, another lane's blocks; in the code: the first block's flags kept for every block, the next block read two blocks on; in the loop invariant: the chaining value after one block more, two registers exchanged, nothing said of the vector registers |
| `b3l_chunk_node` | 33 | in the contract: a chunk of 1025 bytes, the chunk's number and the flags exchanged, the length field's bound one lower, the flags any number, AVX-512 not said to be needed; in the code: no block or every block marked as the first, 60 bytes counted for a block, `b3l_pad` given the whole length, a number stored four bytes on or past the record, the flag for the chunk's end left out, a kernel told that a block is 63 bytes |
| `b3l_pad` | 19 | in the contract: less stack than the function uses; in the specification: padding with ones, one byte more or fewer of the input, a list of 63; in the invariant: one position more or fewer; in the code: a byte read past the end of the input, a jump on a byte of the input |
| the 32-way kernel, for every `n` | 34 | in the contract: the first and the last block's flags exchanged, one block fewer, the two halves of the lanes exchanged; in the code: the counter's low words read from the slot of its high words, a message word stored over a slot of the counter; in the loop invariant: a slot said to hold the low words where it holds the high ones, a slot four bytes further on, nothing said of a slot or of half the lanes |
| the 32-way kernel, one or two blocks | 25 | in the contract: the two halves of the lanes exchanged, lane `i` given the counter `t + i`; in the code: another message word added from the frame, sixty-four bytes read across two slots, the address of the table of constants moved; in the data: one number of that table changed |
| the 32-way kernel by the entry the hash calls | 29 | in the contract: every lane given the counter `t`, the counters of the two halves exchanged; in the code: entered with the other entry's setting, two of the sixteen numbers added to the low word exchanged, the compare the other way round, no carry into the high word, an addition under a mask register that no instruction has set; in the loop invariant: a slot said to hold the other half's counters, the low words where the high ones are |
| the 16-way kernel, one or two blocks | 14 | the last block's flags and its length exchanged; the next counter; a shift that takes the first block's flags from the wrong bits |

Also rejected: a caller listed before its callee, a function that calls itself, a missing callee, and two
functions with the same name.

**Wrong proofs are rejected.** The tests delete or alter single lines of the stored proofs: every line
for `ode_common`, `ode_adler32` and the two BLAKE3 kernels; every third line for `ode_varint`; every
seventh for `ode_adler32_blocks`; and every eleventh for `ode_adler32_blocks4`. The verifier rejects
every alteration that these tests try.

**The arithmetic rule.** All 7,649 arithmetic proofs in the shipped files (17,505 steps) check, in 0.3 s.
On 3,000 deliberately altered proofs, Lean and the Python implementation `varith.py` agree on every one.

**The machine model.** On 5,400 instances of 90 instruction forms, Machine.lean and `conc.py` agree on
registers, flags, memory and the next instruction address. The comparison checks all 16 lanes of each
vector register wherever the table specifies their values, and all 16 bits of each mask register.
Separate tests check that aligned 512-bit loads and stores fault on a misaligned address. The
single-instruction comparison does not cover `lea_data` and `call`, which Machine.lean states directly
(`lea_data` gives the address of the file's data plus an offset).

**The BLAKE3 specification.** Evaluating `../kcheck/blake3.spec` (29 definitions) in Lean gives the 105
official test vectors (35 input lengths up to 102,400 bytes, in three modes) in 43 s. With one constant in
the specification changed (a rotation by 11 bits instead of 12), it does not.

**Code size.** The formal model: 1,021 lines (Table.lean 152, Machine.lean 495, Contract.lean 374). The
verifier: 2,666 lines (Core.lean 2,507, Arithmetic.lean 159 including its proofs). The file parser: 178
lines. The proofs of the theorems: 16,842 lines, of which Trace.lean (two runs of the machine with marks; memory changes only by stores of bytes) is 1,032 and Plain.lean (the machine without marks, and two runs of it) is 632.

## The files

| | |
|---|---|
| the formal model | `Table.lean`, `Machine.lean`, `Contract.lean` |
| the verifier | `Core.lean`; `Arithmetic.lean` (the arithmetic rule and its soundness lemma `refutes_sound`); `Reader.lean` and `Main.lean` (the program `odeverify TABLE STATEMENT PROOF`) |
| the soundness proofs | `SoundLin.lean` (arithmetic on inequalities), `SoundWord.lean` (terms for 32-bit words and their table), `SoundState.lean` (how the verifier's symbolic state relates to a machine state), `SoundStep.lean` (one instruction effect on general-purpose registers), `SoundVec.lean` (one instruction effect on vector registers; 16-byte loads and stores), `SoundWide.lean` (512-bit registers; the stack frame rounded down to a 64-byte boundary and the vectors stored in it), `SoundMarks.lean` (the marks: what the verifier takes not to depend on a secret), `SoundSpec.lean` (symbolic evaluation of the specification), `SoundList.lean` (lists and `ensures`), `SoundPlace.lean` (the facts of a loop invariant), `SoundCall.lean` (calls of functions that return a number), `SoundCallW.lean` (calls of functions that write a buffer of words), `SoundSpecW.lean` (evaluation of the specification on terms; `ensures` of a buffer of words), `SoundLoop.lean` (what a loop invariant says of a machine state, vector registers included; first arrival at an invariant and return to it), `SoundTop.lean` (paths and loops: `explore_sound`, by induction on the termination measure; `verify_sound`; `verify_all_sound`; `verify_all_trace`), `Trace.lean` (two runs of the machine with marks, `ends_trace`), `Plain.lean` (the machine without marks: `runs_plain`, `runs_free`, `runs_endsP`, `runs_trace`) |
| writes the input file (a verdict relies on it for that file saying what the object file and the specification say) | `statement.py` |
| for someone verifying | `lean_verify.py`; the stored proofs in `proofs/`; `examples/equal/`, `examples/low/`, `examples/table/`, `examples/part/`, `examples/record/`, `examples/tail/` and `examples/keyed/` (source, specification and object file); `examples/hash/pad.places` (the loop invariant of `b3l_pad`); `examples/adler32/*.places` (the loop invariants the prover starts from); `examples/kernel/kernel.contract`, `kernel_sse41.contract` and `node_out.contract` (the two BLAKE3 kernels and `b3l_node_out` as they are proved here); `examples/kernel/p16.contract` and `p16.places` (the 16-way kernel and its loop invariant); `examples/kernel/p32.contract` and `p32.places` (the 32-way kernel and its loop invariant); `examples/kernel/k32.contract` and `k32.places` (the same kernel by the entry the hash calls) |
| the prover (a verdict does not rely on it) | `prove.py`, `session.py`, `ProveMain.lean` (`odeprove`) |
| tests | `test_sound.py`, `test_verify.py`, `test_call.py`, `test_adler.py`, `test_blocks.py`, `test_blocks4.py`, `test_varint.py`, `test_low.py`, `test_table.py`, `test_limits.py`, `test_machine.py`, `test_spec.py`, `test_arith.py`, `test_session.py`, `test_kernel.py`, `test_node.py`, `test_p16_one.py`, `test_p16_table.py`, `test_p16.py`, `test_p32.py`, `test_k32.py`, `test_pad.py`, `test_part.py`, `test_record.py`, `test_tail.py`, `test_chunk.py`, `test_meaning.py`, `test_keyed.py`. `MachineMain.lean`, `SpecMain.lean` and `ArithMain.lean` are small programs that three of the tests run. `built.py` runs Lean's build tool once per process. `ensures_meaning.py` has the formal model in Lean evaluate an `ensures` line of the verifier's input file; `test_meaning.py` (the kernels and `b3l_pad`), `test_part.py`, `test_record.py`, `test_tail.py` and `test_keyed.py` compare the result with a reading of the contract that does not go through `statement.py` (`test_node.py` and `test_chunk.py` do the same with their own copies). |

The tests are skipped where Lean's build tool `lake` is not installed.
