# The rules the verifier steps by

What the verifier concludes from the table `x86.tab`, and what it requires of memory, calls, paths, loop
places, returns, traces and files.

The table (`x86.tab`, November 17 and 18, 2026) states two things: how each instruction is written in
bytes, and what it does. The code carrying out these rules lives in `encode.py`, `decode.py` and
`step.py`, and under `../kcheck/` in `kfn.py`, `kbyte.py`, `klin.py`, `varith.py`, `kspec.py`, `kends.py`,
`kdecode.py`, `check_binary.py` and `programs/check_file.py`.

Each rule here has a test that it can fail. `cross.py` runs each row's bytes on processors and compares
what they leave with the row's effect on numbers (`conc.py`). `meaning.py` puts random values of every form
to every rule on symbols and compares the answer with the operation's meaning on numbers.

## 1. Which instruction the bytes are

1. Under each row the table has the ways an instance of the row (these registers, these numbers) is
   written in bytes. For a way and an instance `encode.py` writes one byte string, part by part:
   - the prefix the way names;
   - a REX prefix, only where the way says W, a register numbered 8 or more is named, or the low byte of
     rsp, rbp, rsi or rdi is named;
   - the opcode;
   - the ModRM byte, with a SIB byte only where the base is rsp or r12 or there is an index;
   - the shortest displacement that holds the number: none for zero (one byte of zero with rbp or r13 as
     the base), else one byte in the way's units, else four bytes;
   - the number, in as many bytes as the way says.

   A VEX prefix is the two-byte one wherever that says it. A bit the way does not name has the value that
   says nothing. No instruction so written is longer than fifteen bytes.
2. The bytes at a place are an instance of a row when rule 1, for a way of the row and an instance, writes
   those same bytes. The instruction is then those bytes and no more. The decoded row is written from that
   way and instance.
3. What finds the way and the instance (`candidates` in `decode.py`) is relied on for nothing. What it
   proposes is taken only by rule 2.
4. The decoded row must be an instance of that same row before any other row of the table. So the row the
   verifier steps by is the row whose bytes were read.
5. Four bytes may stand for a place in the file's read-only data, or for a function called. What they
   stand for is the file's to say (`../kcheck/kdecode.py`): by its relocations, or by the bytes themselves
   where its addresses are settled. A place outside the data read is refused.

Why this is right. A processor reads bytes in one way only. What the bytes of rule 1 do is compared with
the row's effect on processors, way by way, with random registers, numbers and displacements of every
length (`cross.py`). What an assembler writes for an instance is read as that instance (`decoder.py`).

A processor accepts other forms for the same instruction: a prefix that says nothing, a longer
displacement, a bit an encoding ignores. They are not read, so nothing has to be shown about them, and a
function written with them is not verified.

Not run on a processor: the call, the return and the address of the file's data. A jump is run only over
the next five bytes.

## 2. What the verifier holds at a point of a path

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

A lane of a vector register is a 32-bit term (constant, sum modulo 2^32, xor, rotation, comparison, or
choice), or half of a rotation (`("shl", w, n)` or `("shr", w, n)`). The zero flag is `("zero", L)` (set
when L is 0), `("cond", (name, k))` (set when the unknown word equals k), or unsaid. The carry flag is
`("neg", L)` (set when L is below 0), or unsaid. The state also holds linear facts and memory (section 6).

## 3. One instruction

1. The instruction's row is the first row of the table whose ROW the decoded instruction is an instance
   of. With no such row the function is not verified.
2. The row's statements are done left to right. `PLACE = EXPRESSION`: the expression's primitives are
   answered by the rules of section 4, registers and memory read as they stand at that statement. `= unknown`
   makes the place unsaid. `jump T if FLAG`: the flag must decide (by the facts), or the path splits in
   two, one with each answer assumed. `call T`: the callee's contract is used, and nothing else of it.
   `return`: the stack pointer must be where it was at entry and the return address untouched.
3. A rule that has no answer refuses, and the function is not verified. A path may split only before the
   instruction has written anything.
4. Then section 5.

## 4. The primitives on symbols

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

## 5. After every instruction

- A jump back counts; a loop that has turned more than `TURNS` times on one path is not run further (a
  loop whose count the path does not fix needs a place: section 6).
- The stack pointer is in the function's own frame, a known number of bytes at or below where it was at
  entry (or, after being rounded down to a 64-byte boundary, in the part of the frame below that). Else
  the function is not verified. The stack used is counted from wherever it is.
- Nothing is remembered of the stack below the stack pointer: a call writes there, and so may whatever
  interrupts the program.

## 6. Memory in regions (`load`, `store`, `no_overlap`)

1. Memory is divided into disjoint named regions:
   - `frame` is the function's stack frame, counted in bytes from the entry stack pointer `F`. At entry
     `frame + 0` holds the eight-byte return address, and the live frame is `[floor, 0)`, where `floor` is
     the stack pointer's offset (`<= 0`) or where it stood when rounded down to a 64-byte boundary.
   - `wide` (`kfn.py`) holds 64-byte cells in `[rsp, 0)` measured from `A = (F + w) & -64` while `rsp`
     stays rounded down from `F + w` (`w <= 0`). Because `A <= F + floor`, `wide` is disjoint from
     `frame`'s kept cells `[floor, 0)` and from `F` upward. Moving a `frame` address back into `rsp` drops
     `wide`.
   - `rodata` is the file's read-only data (`0 <= off` and `off + 4 <= len(data)`). Writes are refused.
   - Each address argument of the contract has its own region, and `N inputs` adds one region `(name, i)`
     of `64 * n` bytes per lane `i` in `0 .. N - 1` (`64 * n < 2^64`). A function that writes an address
     argument (`kbyte.py`) or takes two or more address arguments (`kfn.py`) must state
     `requires no_overlap(...)` over its address arguments. Arguments outside `writes` are read-only.
2. On entry, a read-only argument holds an arbitrary value of its kind with that kind's bounds:
   `0 <= x < B` on a layout's `number ... below B` field, and zeros in the upper seven bytes of a `byte`
   field. For an argument in `writes`:
   - in `kbyte.py`, `held[region]` begins empty (`0` bytes known from offset `0`), and reading any other
     byte yields a fresh unknown byte in `0 .. 255` (marked secret unless `trace depends on region`);
   - in `kfn.py`, a `layout` argument in `writes` initializes only the fields the contract's own entry
     expressions read, leaving every other field unwritten until the function writes it.
3. On reads and writes:
   - In `frame`, offsets must be plain integers with `floor <= off` and `off + size <= 0` (`frame + 0` is
     read only by `ret`). Writing `size` bytes clears raw eight- and sixteen-byte cells inside
     `[off, off + size)` and refuses any write across the edge of a typed record.
   - In an argument region of `kbyte.py`, every access is one byte at an offset `off` shown to satisfy
     `0 <= off < len(region)`. Writing one byte at `len(held[region])` extends the known prefix, and any
     other write drops `held[region]`.
   - In an argument region of `kfn.py`, each access must match the region's or field's kind and alignment
     (`field_at` shows `f.at <= off` and `off + size <= f.at + field_size`). Writing a bounded `number`
     field requires `0 <= v < B`, and writing a `byte` field requires zeros above the low byte.

Why this is right. On a processor with one flat address space, regions stay separate when the caller
guarantees `no_overlap` and the function's stack stays within its `stack` bound. Forgetting frame cells
below `rsp` after every instruction keeps values overwritten by a call or interrupt from being read back.
Leaving unmentioned fields of a `writes` layout unwritten keeps a callee from relying on `below` or `byte`
bounds the caller left uninitialized.

## 7. A call by the callee's contract (`call`)

1. `rsp` must be in `frame` (`wide` inactive), at offset `sp <= 0` (`sp == floor`).
2. Every `needs F` and conditional `calls G if arg == k` of the callee must be covered by the caller's
   contract and path conditions. A self-call (`kfn.py`; `kbyte.py` refuses self-calls) requires
   `decreases E` in the contract, with `0 <= E_callee < E_caller` shown on this path.
3. Scalar arguments in `rdi`, `rsi`, `rdx`, `rcx`, `r8` and `r9` must match the callee's kinds and fit the
   bit width the callee reads (`low byte` <= 255, `word` < 2^32, `byte` with zeros above the low byte).
4. Every address argument's span (read or written, mentioned in `ensures` or not) must be shown by
   `own_span` to lie in memory the caller owns:
   - in `frame` (`kfn.py`; `kbyte.py` passes only argument regions), `size >= 0`, `floor <= off`, and
     `off + size <= 0`, placing `[off, off + size)` at or above `sp` and apart from
     `[sp - (8 + callee_stack), sp)` where the return address and the callee's frame lie;
   - in an argument region, `0 <= size` and `lo <= off <= off + size <= hi` for that region's extent.
5. Every pair in the callee's `requires no_overlap(...)` (and in `kfn.py` every argument in
   `callee.writes` against every other argument) must have no byte in common. Spans in distinct argument
   regions rely on the caller's own `no_overlap` (`frame` is already separate from argument regions). Spans
   in one region require `o1 + s1 <= o2` or `o2 + s2 <= o1`.
6. Every read-only address argument, and every `writes` argument or `layout` field the callee's contract
   reads on entry, is read before the call and checked against its kind (including `below`, `byte`, and
   `asks` array clauses). Every `requires` inequality of the callee must hold on the caller's facts.
7. After the call:
   - Arguments with `ensures` receive the specification values ensured (in `kbyte.py`, replacing the known
     prefix of `held[region]`).
   - Arguments in `writes` without `ensures` become unknown (`held[region] = None` in `kbyte.py`, and
     cleared in `frame` or marked unwritten in `kfn.py`, adding no `below` or `byte` facts).
   - The caller's facts must remain consistent after what the callee ensures is added. A contradiction
     refuses the call instead of dropping the path.
   - `low` records `min(low, sp - (8 + callee_stack))`, using the largest stack the callee's contract may
     take on this call.
   - Each caller-saved register (`rax` unless `returns` sets it, `rcx`, `rdx`, `rsi`, `rdi`, `r8`..`r11`)
     gets a distinct fresh unknown `left in REG by call N`. Vector registers, mask registers and flags are
     cleared. `rbx`, `rbp`, `r12`..`r15` and `rsp` keep their values.

Why this is right. Calls among distinct functions form a DAG (section 10), and self-calls decrease a
natural number `E`, so induction over calls is well-founded. Steps 1 to 6 establish every hypothesis under
which the callee was verified, including separation from the callee's stack frame. Fresh names per
clobbered register keep two unknown outputs from comparing equal. Checking consistency after the call keeps
an impossible postcondition from erasing the code after the call. `writes` without `ensures` adds no value
invariant because `returned` checks none for it.

## 8. Paths, facts, and splits (`klin.py`, `varith.py`)

1. Linear facts are inequalities `L >= 0` over integer unknowns, together with `x < 2^k` (`below`) and
   `L != 0`. When both `L >= 0` and `-L >= 0` hold, a variable with coefficient `1` or `-1` is
   substituted out.
2. When a branch, a difference that may go below zero, or (`kbyte.py`) a contract guard or partial
   definition asks a question left open by the current facts, the path splits into two copies (`Fork`):
   `L == 0` vs `L != 0`, `L >= 0` vs `-L - 1 >= 0`, `(word_name, k)` true vs false, or defined vs failed.
   A branch assumption inconsistent with the path's facts is dropped because no input takes that branch.
   Everywhere else, contradictions come from what a proof supplied (obligations, not facts) and refuse verification.
3. Without `--search`, `varith.py` checks a carried witness: non-negative integer multipliers on known
   rows `>= 0` (dividing and rounding the constant down when coefficients share a factor) summing to
   `-1 >= 0`. No search runs during verification.

## 9. Loops with places, and lemmas (`kfn.py`, `kbyte.py`, `kends.py`)

### Bounded loops without a place

A backward jump on one path may run at most `TURNS` (`100`) times. A path between places in `kbyte.py` may
run at most `PATH` (`1000`) instructions, and a function at most `STEPS` (`400000`) symbolic steps.
Exceeding any limit refuses verification.

### Sequence induction at one place (`kfn.py` `check_place`)

For a contract leaving lane-wise the last value `h[n]` of a `for b in 0..n` sequence (whose state is first
shown to keep one shape across a turn):

- Base: from entry all executions must reach the place `P` on one path. One turn from `P` must return only
  where `n == 1` (leaving `h[1]`), and reach `P` again on one path `seen` where `n >= 2` and the state
  matches the proof at `b = 1` and `h[1]`.
- Step: from `P` with unknown `b` (`1 <= b <= n - 1`), arbitrary `h[b]`, and only the registers, vectors
  and `wide` cells the proof names (other registers fresh unknowns, non-`wide` memory as in `seen`), every
  path must either reach `P` with `b + 1 <= n - 1` and state matching at `b + 1` and `h[b + 1]` (non-`wide`
  memory unchanged), or return with `b == n - 1` and output `h[n]`.

Why this is right. If `n == 0` were consistent at entry, the single path to `P` could prove neither
`n == 1` nor `n >= 2` after one turn. For `n == 1` the base's return checks `h[1]`; for `n >= 2` induction
from `b = 1` to `n - 1` establishes `h[n]` in `n` turns.

### General places (`kbyte.py`) and specification lemmas

- A place `P` in a `.proof` file names registers and stack cells (`stack[K]`, required to satisfy
  `floor <= rsp + K` and `rsp + K + 8 <= 0`, inside the frame below the return address), `facts`, `memory`
  prefixes, `futures`, `ghost` witnesses, and `decreases` expressions each shown `>= 0` at `P`.
- On first reaching `P`, `start` builds a general state keeping only entry facts, place facts, and values
  `kept` shows equal on every arrival at `P`. Every arrival checks `holds` and, from any place to a place,
  strict lexicographic decrease of `decreases`.
- Each specification `lemma` (`prove_lemmas`) is checked by opening its definition once with recursive
  calls taken by their lemmas (requiring `0 <= d_inner < d_outer` on `decreases`), checking the declared
  result kind, and (`kends.py`) showing from the public contracts inward that every recursive definition
  reached meets its lemma's `requires` and no skipped construct hides recursion.

## 10. Return, trace, and whole-file rules

### Return (`returned`)

At `ret`, `rsp` must be `("a", "frame", 0)` and `frame + 0` must hold `("q", "return address")`. Every
callee-saved register (`rbx`, `rbp`, `r12`..`r15`) must hold `("q", "REG at entry")`. Stack use `-low` must
stay within the contract's `stack` bound (at the least `bits(...)` consistent with the path). `rax` must
equal `returns`, and every `ensures` clause must hold with every part of a returned value initialized.

### Trace (`kbyte.py`)

Every byte read from a region outside `trace depends on ...`, every unwritten byte read from a writable
region, and every sequence value built from secret inputs is marked `secret`. Any memory offset, branch
condition, place variable, or callee argument that depends on a `secret` symbol refuses verification, so
instruction and address traces depend only on public inputs.

### Whole-file rules (`kdecode.py`, `check_binary.py`, `programs/check_file.py`)

ELF tables must lie inside the file, and no loadable or executable section may combine write and execute
permissions. A relocatable object must have one linkable shape, and every symbol it gives a linker must be
verified. Distinct functions may not form a call ring (`ring_of`). Every instruction of a verified body
must belong to features its contract unconditionally `needs` (`kspec.fits`). Every public contract of the
reader's specification is printed, failing the verification if unverified while present in the file or in a
nameless file.

*Ode stands for Only Direct Execution.*
