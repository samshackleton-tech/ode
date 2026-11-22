# The language: what a specification and a contract mean

A reader reads two kinds of text: a specification (definitions by equations: part 1) and a contract (what a
function in a binary does: part 2). This page is the whole meaning of both. It is the same for every
program; read it once. Here a **contract** is always the formal text. What a reader wants of the software,
which may still be changing, is his **intent** ([DESIGN.md](../DESIGN.md#3-bobs-intent-and-the-contract-his-verifier-decides)): verifying a
contract settles whether the bytes meet that text, and leaves to him whether the text says what he wants.

## Part 1. The specification language: what its texts mean

A specification is what a reader checks a binary against, so it is written for the reader: definitions by
equations, nothing that changes, nothing about memory. It is a language of its own, apart from the language
the code is written in (Ode) and smaller. This page is its whole meaning; `ode.py` is the program that reads
it (and reads contracts), and where the two differ the program is wrong. Part 2 of this page says what a
contract means.

A specification can be worked out on numbers: that is how each one here is checked against other people's
answers (BLAKE3's official vectors; zlib's Adler-32; an LZ4 decoder written another way; Sigil's vectors).
But it is not written as a way to compute, and a contract may use it in a way nobody could compute by
(`ensures lz4(out[0 .. r], n) == input`: what was written decodes to the input).

### Values

| value | written | meaning |
|---|---|---|
| number | `0`, `65521`, `0x40` | a whole number, not below zero, of any size. Numbers never wrap. |
| word | `word(n)` | 32 bits. `+` wraps, `^`, `|`, `>>>` (rotate right). |
| counter | `counter(n)` | 64 bits as two words; `+` a number; `lo(t)`, `hi(t)`. |
| list | `[a, b]`, `[]` | values in order. A list of numbers below 256 is bytes. |
| record | `{value: a, next: b}` | named values; `r.value`. |
| true, false | `a < b`, `!c`, `c && d`, `c || d` | only where a condition is asked for. |

### What can be said of them

- **Numbers**: `+`, `*`, `/` (whole division), `%` (remainder), `-`. A difference below zero has no meaning:
  see "No value" below. `pow(a, b)`, `bits(n)` (its length in bits), `==`, `!=`, `<`, `<=`, `>`, `>=`.
- **Lists**: `xs[i]` (place i, from 0), `xs[a .. b]` (places a up to b, b not among them), `xs ++ ys`,
  `len(xs)`, `[e for i in a .. b]` (e for each i from a up to b), `xs with [i: a]` (xs with place i
  replaced), `words(bytes)` (every four bytes a word, the lowest byte first) and `bytes_of(words)` (the
  other way). These two are the only place a byte order is said, and a specification may not define them.
- **Choice**: `if c then a else b`.
- **Search**, among numbers that can be listed: `the least number n in a .. b with C`,
  `the greatest power of two k with C`.

### Definitions

```
const NAME = E

def NAME(x, y) {
    fails REASON if C          (any number of these, and of `let`, in the order they are meant)
    let a = E
    E                          the value
}

sequence NAME(x) { s[0] = E   s[i + 1] = F }
```

- A **definition** is its value, with names (`let`) for parts of it. A name is given once. Nothing loops and
  nothing changes. A definition may be of itself on smaller things (`subtree` of a part of the bytes;
  `sequences` from a later place of the block).
- **`fails REASON if C`**: where C holds, the definition has no value, and REASON (a number) says why. They
  are read in order, with the `let`s between them, so each may rest on those before. Something that has no
  value gives none to whatever is made of it. `failed(E)`: E has no value. `reason(E)`: why.
- A **sequence** is values in order, each from the one before: `NAME(x)[k]` is the one at place k. (Adler-32's
  two sums; a match's copies in LZ4; a chunk's chaining values in BLAKE3.) Written with `for i in 0 .. n`
  after its two equations, `NAME(x)` is its value at place n. Inside a definition, `let s[0] = E` and
  `let s[i + 1] = F` make one without a name of its own.

### No value

Three things have no meaning: a place outside a list, a difference below zero, a search with no result. A
specification that comes to one of them is wrong there, and the reader stops; nothing is given in its
place. The verifier, reading on a path of the code, must be shown that it does not happen (the path's facts
show `i < len(bytes)`), or it refuses. So a specification that means to have no value somewhere says so with
`fails`, before it gets there.

### What is not in it, and why

- **Nothing that changes** (no assignment, no loop, no variable given twice). An auditor reading a state
  that changes must convince himself that an algorithm computes the thing; here he reads the thing. The
  earlier specification of BLAKE3 had a stack of subtrees in it; its own comment had to point to a proof that
  the stack was the tree.
- **No memory**: no addresses, no registers, no lengths in bytes of things. Those are the contract's.
- **No numbers that wrap**, but words, which are written `word(...)` and are of one size. A reader never has
  to ask whether `1024 * k` passes 64 bits.
- **No functions given to functions, no types with parameters, no modules.** None was needed for a hash, a
  checksum, a compression format or an encoding, and each makes "what does this name mean here" a longer
  question.
- **No search without bounds, no "there is" or "for all" over everything.** A search is among numbers that
  can be listed, so it has an answer that can be worked out.

## Part 2. What a contract means

A contract is the one thing, beside the specification it names, that a reader has to read about a function in
a binary. It is a Hoare triple with nothing left to be understood: what the caller must make true, and what
is then true when the function has returned. This page is the same for every function; read it once.

```
contract NAME(ARGUMENT: KIND, ...) {
    requires ...
    ensures ...
    returns ...
    writes ...
    trace depends on ...
    needs ...
    stack ...
}
```

**The arguments** are in the registers of the calling convention, in the order written: rdi, rsi, rdx, rcx,
r8, r9. An argument is a number (`number`: what a register holds, 0 to 2^64 - 1; `byte`: a number below
256; `any`: 64 bits of which nothing is asked) or the address of bytes in memory (`N bytes`; `len bytes`:
as many as the number `len`, another argument). The number a function returns is of the same size. (In a
specification a number is of any size and never wraps: part 1. It is only an argument or a result
that a register bounds.)

**`requires`**: what the caller makes true. `requires no_overlap(a, b, ...)`: no two of the things at those addresses have a
byte in common. Two things are required of every caller and not written. The stack is the machine's own,
and nothing an argument addresses lies in it. And the program is loaded: the constants that lie in each
of its object files beside the code are in memory where that file's code takes them to be, and nothing
the function may write (what an `ensures` or a `writes` names, its stack, the address it returns to) lies
over those constants or over the program's code. (What a function only reads may lie among the constants.)
Whoever puts the program into memory (a linker and a loader) sees to the first half of that; a caller that
writes only its own stack and what it was itself given to write keeps the second half for the functions it
calls. Of a call that does not keep
these, nothing is said.

**If the caller does that, the function returns**, and then:

- `ensures X = E`: the bytes at X are E, a value of the specification. `ensures X[a .. b] = E`: those of its
  bytes, and nothing is said of the rest of X, which may then hold anything. `ensures ... if C`: where C
  holds. On the right, a name means what was there when the function was called.
- `returns E`: the number it gives back. With no such line, nothing is said of that number. `returns r`,
  where r is no name of the specification's, gives the number that name, and other lines speak of it:
  `ensures lz4(out[0 .. r], n) == input if r != NO` (what it wrote decodes to the input, unless it said NO),
  `ensures r != NO if cap >= n + n / 255 + 16` (and with that much room it does not say NO).
- `ensures CONDITION`: something true or false of the result and of what is in memory.

Memory holds bytes and nothing else. Where a specification speaks of words, the contract says how bytes are
read as words: `words(X)` is every four bytes one word, the lowest byte first; `bytes_of(W)` is the other
way. Both are the language's own (part 1) and a specification may not define them otherwise.

**And it has done nothing else.**

- It has read no memory but what its arguments address, its own stack, and constants that lie in the
  program's object files beside the code. (No contract names constants: any function may read them, and
  none may write them.)
- It has written no memory but what an `ensures` or a `writes` names (`writes X`: X may hold anything
  afterwards), and at most `stack` bytes below the caller's stack pointer.
- The registers the calling convention says a callee keeps are as they were.
- It has run no instructions but those every x86-64 processor has, and those a `needs` line names
  (`needs F if C`: only where C holds). That the processor has them is the caller's to know.
- Which instructions it ran, and which addresses it touched, depend on the addresses it was given and on
  what a line `trace depends on X, ...` names, and on nothing else: not on another number it was given, not
  on a byte in memory, and not on what its caller left in a register that holds no argument. X is a
  number among the arguments, or something at an address among them: the bytes there. With no such line
  they depend on the addresses given alone.

So everything a function is given is hidden from its trace unless the contract names it. (An address
given is never hidden: the function reads or writes there, so the address shows. A table of addresses is
read as addresses: what it holds shows too.) A count that a loop goes round by, or a number that chooses
between two ways through the function, must be named; a number that is only stored, or handed on to a
function that hides it, need not be.

The trace property speaks of which instructions run and which addresses are touched. How long an instruction
takes on its operands, and every other effect of the processor, lie outside it: a promise about those needs
an account and assumptions of its own. Nor does it speak of what a function leaves behind in registers and
in its dead stack: between functions written in Ode, a function may rely only on what a contract says
about a register (its own contract at its entry, the called function's after a call). A verification
reports the property that was shown, by this name.

A function that does more, or promises less, says so in its contract. Silence always means the stronger
thing.

**What a specification's definition may be.** A definition has a value, or it `fails` with a reason
(`fails REASON if C`, in the order written). `failed(E)` says whether E has no value. A contract speaks of a
failing input through it: `returns if failed(lz4(input)) then NO else ...`.

**What the verifier does with it** (check_binary.py for the hash; programs/check_file.py for the others): it
shows all of the above from the binary's bytes, for everything the `requires` lines allow, or it refuses.
The contracts of the functions inside (proofs/inner.spec) are steps of that showing, in the same form, with
two lines of their own (`decreases`, `calls`); a reader need not read them.

One thing this folder's verifier does not tell apart: a number that `trace depends on` names from one
that it does not. It takes every number given as one the trace may depend on, and shows that the trace
depends on no byte in memory but those named. So that its "shown" is of what the contract says,
check_binary.py and check_file.py refuse a public contract that leaves a number it is given out of
`trace depends on`. Of an inner contract that leaves one out, this verifier shows the rest. The verifier
in `../proof-core` tells the two apart: there a number that is not named is marked as a secret is, and a
jump or an address that depends on it is refused. It also requires one thing more than this page does: the
number a function returns must be made of nothing hidden (so `ode_far`, which adds 2^63 to a number and
branches on nothing, has to name that number there). Whether a contract should say that is not decided.
