# The rules the verifier steps by

What the verifier does with one instruction, written down. This page covers the part that was taken out of
the verifier's code on November 17, 2026: what an instruction does is a row of `x86.tab`, and what the
verifier concludes from a row is the rules below (`step.py`, and the end of `one` in `../kcheck/kfn.py`).
The rules for memory, calls, places in loops, the return and the specification are still only code
(`../kcheck/kfn.py`, `kbyte.py`, `kspec.py`); section 5 lists them. Each rule here has a test that it can
fail: `meaning.py` puts random values of every form to every rule and compares the answer with the
operation's meaning on numbers (`conc.py`), and `cross.py` compares each row's effect on numbers with
processors.

## 1. What the verifier holds at a point of a path

A value of a 64-bit register is in one of these forms. Each form means a number, or some bits of one,
once every unknown has a value; `meaning.py` has the same list as code.

| form | means |
|---|---|
| `("n", k)` | the number k |
| `("l", L)` | a number that depends on unknowns, L a sum of unknowns with whole coefficients; the facts show it is from 0 to 2^64 - 1 |
| `("a", region, off)` | an address: `off` bytes into a region of memory (for `frame`, from where the stack pointer was at entry) |
| `("aligned", off)` | the frame's address at `off`, rounded down to a multiple of 64 |
| `("t", w)` | the 32-bit word w, zeros above it; `("lowt", w)`: the low 32 bits are w, of the rest nothing is said |
| `("pair", lo, hi)` | two 32-bit words side by side: lo + 2^32 hi |
| `("p", (b0 .. b7))` | eight bytes, lowest first; each is 0, a number, or a number or-ed with named unknown bytes |
| `("low", name)`, `("al", n)` | the low byte is the named byte, or the number n; of the rest nothing is said |
| `("q", name)` | an unknown word that has a name |

A lane of a vector register is a term over 32-bit unknowns (a constant, a sum modulo 2^32, an xor, a
rotation, a comparison, a choice), or half of a rotation (`("shl", w, n)` or `("shr", w, n)`). The zero flag
is `("zero", L)` (set exactly when L is 0), `("cond", (name, k))` (set exactly when the unknown word is k),
or unsaid; the carry flag is `("neg", L)` (set exactly when L is below 0), or unsaid. Beside these: the
facts in play (inequalities between unknowns), and memory, which is the machine's own (section 5).

## 2. One instruction

1. The instruction's row is the first row of the table whose ROW the decoded instruction is an instance
   of. With no such row the function is not verified.
2. The row's statements are done left to right. `PLACE = EXPRESSION`: the expression's primitives are
   answered by the rules of section 3, registers and memory read as they stand at that statement. `= unknown`
   makes the place unsaid. `jump T if FLAG`: the flag must decide (by the facts), or the path splits in
   two, one with each answer assumed. `call T`: the callee's contract is used, and nothing else of it.
   `return`: the stack pointer must be where it was at entry and the return address untouched.
3. A rule that has no answer refuses, and the function is not verified. A path may split only before the
   instruction has written anything.
4. Then section 4.

## 3. The primitives on symbols

Where a rule answers, the answer means the operation's result for every value of the unknowns that the
facts allow. Where no case below applies, it refuses.

| primitive | answers for | why that is right |
|---|---|---|
| `add64`, `sub64` | a word plus `(0, hi)`; packed bytes plus packed bytes with no two in one place; an address plus or minus a number; two numbers | nothing is carried between words or bytes that do not meet; a sum of numbers must be shown to stay below 2^64, and a difference that may go below zero splits the path (below zero it must be a known number, which wraps) |
| `shl64` | a word by 32; packed bytes by whole bytes; a number by less than 32, shown to stay below 2^64 | bits moved out are gone; no wrap |
| `shr64` | a known number; a pair by 32 (its high word); packed bytes by whole bytes; a number shown below 2^n (zero), or its quotient by 2^n, a named number q with 2^n q <= x <= 2^n q + 2^n - 1 | a number has one quotient |
| `and64` | two known numbers; a number and 1 (x minus twice its half), or a mask 2^k - 1 (`kbyte.py`); packed bytes and 0xFF (the low byte); the stack pointer's own value and -64 (`aligned`) | a remainder is the number less its quotient's multiple; only the stack pointer's own place may be rounded down to a boundary: from anywhere else it could be above the frame |
| `or64` | two known numbers; packed bytes with a number or packed bytes, byte by byte; a number and 0; a multiple of 2^k and a number below 2^k, as their sum (`kbyte.py`) | no bit in common, so nothing is carried |
| `low32` | a known number, packed bytes (the low four), a pair (its low word), a word | zeros above the low 32 bits |
| `low8`; a byte put in a register | a register whose low byte is known as a byte (`low`, packed bytes) | zeros above it |
| `setlow8`, `sub8` | a known number put in the low byte; one less of such a byte | the rest of the register becomes unsaid |
| `equal` | two numbers (`("zero", x - y)`); an unknown word and a known number (`cond`); a counted byte and 0 | the flag is set exactly when the difference is zero |
| `below` | two numbers (`("neg", x - y)`); otherwise unsaid | both are from 0 to 2^64 - 1, so x is below y exactly when x - y is below zero |
| `at`, `data` | an address and a displacement; the file's read-only data | a displacement is a signed number of bytes |
| `add32`, `xor32` | whole lanes | terms: sums modulo 2^32, xors |
| `ror32` | a whole lane, by 1 to 31 | a rotation by a multiple of 32 is refused, not answered |
| `shl32`, `shr32`, `or32` | a whole lane shifted by 1 to 31 is half of a rotation; the or of the halves `x << (32 - n)` and `x >> n` of one word is x rotated right by n | the two halves have no bit in common and together are the rotation; any other or is refused |
| `lanes`, `words`, `pick4`, `blend4`, `in_quarters`, `quarters`, `spread16`, `zeros16`, `words16` | whole lanes, numbers | lanes moved about, or numbers made lanes |
| `lanes_of64` | a pair; packed bytes that are two bytes, one in each word | the register's two words, zeros in the upper lanes |
| `shuffle_bytes` | a mask of constants that rotates each word's own bytes | that is a rotation of each word by whole bytes |
| `blend_halves` | a mask that takes both halves of each word from one source | then it is a blend of whole words |
| `lane32` | a word, a known number, one byte | a 32-bit value as a lane |
| `ult32`, `choose16` | whole lanes; a mask of comparisons | terms: a comparison, a choice |

## 4. After every instruction

- A jump back counts; a loop that has turned more than `TURNS` times on one path is not run further (a
  loop whose count the path does not fix needs a place: section 5).
- The stack pointer is in the function's own frame, a known number of bytes at or below where it was at
  entry (or, after being rounded down to a 64-byte boundary, in the part of the frame below that). Else
  the function is not verified. The stack used is counted from wherever it is.
- Nothing is remembered of the stack below the stack pointer: a call writes there, and so may whatever
  interrupts the program.

## 5. Not yet written down here

Rules the verifier follows that are still only its code: memory in pieces (`load`, `store`: what lies at
an address, bounds, what a contract gives to read or to write, `no_overlap`); a call by the callee's
contract (what it requires, what it leaves in each register, what it may have written); a path's facts
and how a split is assumed; a place in a loop and its induction; the return against `ensures`; the trace;
that a function comes to an end. Each needs its statement and its argument here before the verifier can be
said to follow a written list of rules.
