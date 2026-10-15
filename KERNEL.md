# The proof-object kernel

`ode/kernel.py` checks explicit equational proofs and structural induction
over finite constructor-built data, including natural numbers and bit strings. Its first theorem is a loop transformation relevant to
BLAKE3: **processing two blocks per iteration gives the same state as
processing one block per iteration, for every iteration count**.

```sh
pypy3 -m ode.proof_cli \
  examples/proofs/batching.theory.sexp \
  examples/proofs/batching.goal.sexp \
  examples/proofs/batching.proof.sexp
```

The output identifies the theory and goal and reports 24 inference steps,
33 shared terms. There is no tested-length limit: `n` is a universally
quantified natural number. Checking never evaluates the loop at any `n`.

## What is proved

The owner supplies the theory and goal; the producer supplies the proof.
Read `batching.theory.sexp` and the goal before relying on the result:

```
chain(double(n), s, m, i) = pairs(n, s, m, i)
```

- `chain(n,s,m,i)` processes `n` blocks, starting with state `s` and block
  index `i` in block source `m`.
- `pairs(n,s,m,i)` processes two successive blocks in each of `n` iterations.
- `double(n)` is defined by zero and successor equations.
- `compress(state, block)` and `block-at(source, index)` are **arbitrary
  total functions**. Every interpretation of them satisfies the theorem.
  A block can include the counter, flags, and block length along with its
  message words; the theorem assumes no cryptographic law.

The induction hypothesis is deliberately generalized over state, block
source, and index. In the step case it applies to the state **after two
compressions**, at index `i+2`. An invariant restricted to the initial
state would not justify that step.

This is a theorem about mathematical loops. It does not yet identify
`compress` with `examples/blake3-compress.sexp`, prove bounds for memory
accesses, or verify the AArch64 implementation of either loop. Those
connections need their own proofs. In particular, acceptance by the
existing symbolic checker (`ode/check.py`) is not a kernel proof.

## Proof-producing arithmetic and loop composition

`ode/nat_proof.py` normalizes sums of **natural numbers** by emitting
proofs. It first supplies derivations of right identity, successor,
commutativity, associativity, and exchange from the two defining
equations of `add`; then it uses those proved lemmas to reorder and
reassociate sums. The kernel never runs the sorting algorithm or assumes
its answer. This is loop-counter arithmetic, not modular 32-bit arithmetic.

```sh
pypy3 -m ode.proof_cli examples/proofs/nat-add.theory.sexp \
  examples/proofs/nat-add.goal.sexp examples/proofs/nat-add.proof.sexp
```

The example proves `(a+b)+(c+(d+0)) = (d+c)+(b+a)`, with all five helper
lemmas checked. The producer may be replaced or corrupted without changing
the kernel's rules. `tools/make_nat_add_proof.py` regenerates the artifacts.

The same arithmetic proofs support an unbounded chain-splitting theorem:

```
chain(n+k, s, m, i) = chain(k, chain(n, s, m, i), m, n+i)
```

Processing `n+k` blocks is equivalent to processing `n` and then `k`,
starting the second batch at the updated state and index. Both batch
sizes are arbitrary naturals. Its proof generalizes the state/index
invariant and instantiates the proved addition-successor lemma.

```sh
pypy3 -m ode.proof_cli examples/proofs/chain-split.theory.sexp \
  examples/proofs/chain-split.goal.sexp examples/proofs/chain-split.proof.sexp
```

This takes 48 inference steps, including two arithmetic lemmas. It is a
composition law for sequential compression chains; it says nothing yet
about BLAKE3's binary hash tree or its native memory accesses.

## Bit semantics: a word rewrite proved from definitions

`examples/proofs/bits.theory.sexp` defines two data types, `Bit` and
`Bits`, and total functions for bit negation, bit XOR, list head/tail,
zero strings, bitwise XOR, and width. No word-operation axioms are used.
The same structural-induction rule used for naturals checks:

```
xor-bits(x, x) = zeros(x)
width(xor-bits(x, x)) = width(x)
```

Both hold for every finite width, including 32 bits. `xor-bits` takes the
width of its first argument; shorter second arguments are zero-extended,
and longer ones truncated. On equal-width inputs it is ordinary XOR.
The four one-bit results are checked separately in the tests.

```sh
pypy3 -m ode.proof_cli examples/proofs/bits.theory.sexp \
  examples/proofs/xor-cancel.goal.sexp examples/proofs/xor-cancel.proof.sexp
pypy3 -m ode.proof_cli examples/proofs/bits.theory.sexp \
  examples/proofs/xor-width.goal.sexp examples/proofs/xor-width.proof.sexp
```

Cancellation takes 24 inference steps, including the one-bit lemma; the
width theorem takes 40. `tools/make_xor_proof.py` reproduces both.
This establishes the mathematical identity behind one word-normalizer
rewrite. Linking the existing u32 representation and AArch64 EOR model
to this bit-string semantics remains a separate proof obligation.

## A checked export from the existing XOR normalizer

`examples/proofs/xor32.theory.sexp` defines `Word32` as one constructor
with exactly 32 `Bit` fields. It defines each projection and `xor32`
field by field using the same `xor-bit` definition from the bit-string
theory. Its equations fully specify a finite
32-bit domain; XOR's algebraic laws are not declarations or axioms.

`ode/xor32_proof.py` produces proofs of the Boolean laws, word
extensionality via projections, and the word-level identity,
commutativity, associativity, and cancellation laws. It then emits
normalization proofs for XOR expressions by using those proved lemmas.
The single entry point, `ode.arx_proof.export_normalizer`, runs the actual
`ode.check.Dag` normalizer and
constructs a kernel proof of its proposed result. Both that normalizer
and this proof producer sit outside the kernel's reliance set.

```sh
pypy3 tools/make_xor32_proof.py
pypy3 -m ode.proof_cli examples/proofs/xor32.theory.sexp \
  examples/proofs/xor32.goal.sexp examples/proofs/xor32.proof.sexp
# xor32(x, xor32(y, x)) = y
```

This checks all 48 supporting lemmas and the final normalization in
2,245 inference steps, using 938 shared terms. Supported exports are
variables, explicit Word32 literals, and XOR expressions: flattening,
reordering, zero elimination, cancellation, and constant folding. Constant
folds emit constructor-evaluation proofs from the same theory.

A randomized producer test found an omitted zero-elimination step after
suffix cancellation. The kernel rejected the incomplete proof; fixing
the producer required no kernel change. Another test replaces the
existing normalizer with a broken one: it cannot obtain a proof of the
wrong result. Attacks that change a bit selector, lie about the final
result, or introduce a `normalize` oracle are rejected too. A fresh-process
test blocks imports of the existing verifier, evaluator, native runner,
and proof producers; the exported proof still checks.

This is the first exported rewrite with explicit Word32 semantics. It
does not yet certify the complete symbolic execution of a native
program. Mapping the decoder's u32 values to these Word32 constructors
and proving the remaining word/ISA operations are still required before
existing native certificates can use this smaller reliance set.

## Rotation composition and distribution

The rotation export uses the same Word32/Bit definitions. `ror-0` through
`ror-31` are explicit permutations of the 32 bit fields: field 0 is the
least significant bit, and output field `i` reads input `(i+n) mod 32`.
These are immediate rotations, as used by BLAKE3's compression.

`ode/rotate32_proof.py` supplies bit-projection proofs for the common
exporter's rotation rewrites. It generates projection lemmas only
for counts used in that proof, and reuses the XOR proof algorithm at the
Boolean level. No kernel rule, oracle, or arithmetic axiom is added.

```sh
pypy3 tools/make_rotate32_proof.py
pypy3 -m ode.proof_cli examples/proofs/rotate32.theory.sexp \
  examples/proofs/rotate32.goal.sexp examples/proofs/rotate32.proof.sexp
```

The example proves that

```
ror16(x XOR y) XOR (ror8(ror8(x)) XOR ror16(y)) = zero32
```

The result comes from the existing normalizer; the kernel checks all
112 lemmas and 4,185 inference steps against the bit definitions.
Exports support variables, explicit Word32 literals, XOR, and immediate
rotations. Literal words project to their Boolean fields, so constants
inside symbolic expressions use the same parity proof. Addition and
machine-execution claims remain outside this fragment.

Tests check composition for every count, including wraparound, and
random combinations of distribution and cancellation. Separately, one
unfolding proof for each basis bit and count (1,024 cases) checks the
definitions against independently computed integer right rotations.
This matters: the same algebraic laws could hold for a mistakenly
left-rotating definition. A changed selector, count, conclusion, or
invented rotation rule is rejected. Verification also succeeds in a
fresh process that blocks all producer and old-verifier imports.

## Modular addition from ripple carry

`examples/proofs/add32.theory.sexp` defines Boolean AND, OR, and carry,
then 32 carry stages and the sum's 32 bit fields. Field 0 is the least
significant bit; carry into bit 0 is zero; carry out of bit 31 is
discarded. These equations specify addition modulo 2^32.

`ode/add32_proof.py` proves Boolean carry symmetry, each stage's
recurrence and symmetry, and each sum projection. Together with proved
XOR commutativity and Word32 reconstruction, these establish
`add32(x,y) = add32(y,x)` for every pair of words. All 104 supporting
lemmas and 1,257 inference steps use the existing kernel rules.

```sh
pypy3 tools/make_add32_proof.py
pypy3 -m ode.proof_cli examples/proofs/add32.theory.sexp \
  examples/proofs/add32.goal.sexp examples/proofs/add32.proof.sexp
```

Ground tests emit unfolding/congruence proofs for all Boolean carry
inputs, carry chains through every bit position, modular overflow, and
seeded random sums. The expected results use independent integer
arithmetic. These tests constrain the intended semantics beyond
commutativity alone. Changed carry equations, stage dependencies, sum
bits, and theorem conclusions are rejected by the kernel.

The same generator also emits `add32-zero.goal.sexp` and
`add32-zero.proof.sexp`: `add32(x, zero32) = x` for every word. Its proof
shows that each incoming carry stays zero, reduces each sum bit with
proved Boolean XOR identity, and reconstructs the word. Changed initial
carry and replacement of zero by one are rejected.

These milestones prove commutativity and right-zero identity of the
defined adder. The native ADD representation/refinement link remains
open; natural-number addition lemmas do not discharge word-level obligations.

## Word32 addition associativity

`ode/add_associativity_proof.py` proves
`add32(add32(x,y),z) = add32(x,add32(y,z))` from the same ripple-carry
definitions. The two successive additions have two incoming carry bits.
Their AND and OR encode the pair in sorted order, preserving its count
without requiring the individual carries to match across groupings.

Six five-variable Boolean identities establish that either grouping
produces the same encoded outgoing carries and sum bit from the encoded
incoming carries. `ode/carry_proof.py` produces these identities using
explicit constructor cases. The word proof establishes the carry relation
at bit 0, transports it through each of the remaining 31 positions, and
reconstructs the equal words from their sum bits.

```sh
pypy3 tools/make_add_associativity_proof.py
pypy3 -m ode.proof_cli examples/proofs/add32.theory.sexp \
  examples/proofs/add32-assoc.goal.sexp examples/proofs/add32-assoc.proof.sexp
```

The artifact contains 524 checked lemmas and 10,816 inference steps,
using 472,734 kernel work units within the existing limits. These are
proof-work counts, not timing measurements. Tests independently check
all six Boolean identities, reproduce the artifact, and reject changed
carry semantics, missing Boolean cases, and a dropped operand. A fresh
process verifies the artifact with producer imports blocked.

The theorem is modular Word32 associativity. Its symbolic-normalizer
export is described below; native instruction refinement remains open.

## Symbolic addition exports

`ode/add_normalizer_proof.py` supplies the common exporter's proofs for
expressions built from variables, explicit Word32 literals, and `add32`.
It proves flattening, reordering, zero elimination, and constant folding using the ripple-carry
commutativity, identity, and associativity theorems. Repeated operands
remain repeated: addition has no XOR cancellation law.

The producer reuses the same sorting/reassociation algorithm as XOR,
configured with the appropriate proved laws. Supporting theorem
libraries share equal statements, and unused lemmas are removed before
serialization. Neither operation changes the kernel's checking rules.

```sh
pypy3 tools/make_add_normalizer_proof.py
pypy3 -m ode.proof_cli examples/proofs/add32.theory.sexp \
  examples/proofs/add32-normalize.goal.sexp examples/proofs/add32-normalize.proof.sexp
```

The example exports `(x+y)+(z+x)` as `x+(x+(y+z))`, with all additions
modulo 2^32. Its 528 lemmas and 10,886 inference steps check within the
existing kernel limits. Tests include repeated operands, zero, random
expression trees, a deliberately broken `Dag.add`, and producer-free
verification in a fresh process. Mixed constant tests include modular
overflow to zero and a deliberately wrong normalizer constant component.

For both addition and XOR, literal operands sort after symbolic atoms.
The shared ground producer proves their folded value from constructor
definitions; congruence lifts that proof through the symbolic prefix.
When the value is zero, the proved identity removes it. This reuses the
same evaluation producer as the closed-expression export below.

## Concrete arithmetic exports

The common exporter also handles the existing normalizer's concrete
Word32 addition, XOR, and immediate-rotation results. Nonzero words are
explicit 32-bit constructors. `ode/ground_proof.py` evaluates the
owner's definitions while emitting unfolding and congruence steps;
repeated subterms reuse their derivations. The kernel receives only
these ordinary proof steps, with no evaluation callback or new rule.

```sh
pypy3 tools/make_constant_proof.py
pypy3 -m ode.proof_cli examples/proofs/add32.theory.sexp \
  examples/proofs/constant.goal.sexp examples/proofs/constant.proof.sexp
```

The example checks `(0xffffffff + 1) XOR 0xdeadbeef = 0xdeadbeef`
with modular overflow: 941 inference steps and two ground-evaluation lemmas.
The theory is the existing addition theory. Rotation exports use the
rotation theory. Each supplied theory must define the operations used.

These exports cover closed expressions. The symbolic exports above also
fold nonzero constants within expressions containing variables. Tests
include a broken old adder, changed carry definitions and
conclusions, shared-subterm reuse, and verification in a fresh process
that blocks imports of the old verifier and producers. The addition
semantic tests use this same ground-proof producer.

## Boolean case proofs

`ode/boolean_proof.py` proves small Boolean identities by emitting both
constructor cases for every variable. Each leaf uses the same ground
proof producer as concrete arithmetic exports. Each internal node uses
ordinary structural induction and earlier child lemmas. The kernel has
no truth-table rule or callback into the producer.

The producer accepts at most eight Boolean variables: enumeration has
2^n leaves, so its input bound states the cost explicitly. The tests
cover carry symmetry in all three inputs and five-input XOR parity,
and reject false identities, missing cases, and altered conclusions.
These finite identities provide building blocks for word-level carry
proofs; enumerating Word32 values is outside this producer's contract.

Repeated concrete Boolean operations use shared evaluation lemmas.
The producer derives each needed small Boolean evaluation from definitions,
then case leaves reference that earlier lemma. These are ordinary proof
entries, not a kernel truth table. A producer-supplied table that lies
about a lemma's result produces an invalid derivation and is rejected.
Regression tests bound the associativity and composed G-output artifacts'
bytes and kernel work; these bounds measure proof cost rather than time.


## Composed arithmetic expressions

`ode.arx_proof.export_normalizer` is the single exporter for addition,
rotation, and XOR (often abbreviated ARX), separately or combined in one
expression. Its supplied theory must define every operation used. Closed
local rewrites use ground evaluation; rewrites with symbolic parameters
use the corresponding algebraic proof producer. The combined theory
contains the same bit, Word32, carry, and rotation definitions as the individual fragments; the
producer checks that their shared definitions agree when assembling it.

For each operation, the existing `Dag` proposes a result. The producer
abstracts unrelated subexpressions into Word32 parameters, obtains a local
arithmetic proof, and instantiates its checked lemma with those actual
subexpressions. Congruence connects the local rewrite to the original
expression. Repeated source subexpressions reuse a derivation, and shared
supporting theorem statements appear once in the assembled library.

```sh
pypy3 tools/make_arx_proof.py
pypy3 -m ode.proof_cli examples/proofs/arx.theory.sexp \
  examples/proofs/arx.goal.sexp examples/proofs/arx.proof.sexp
```

The example proves

```
ror8(((x+y)+z) XOR w) XOR ror8(w) = ror8(x+(y+z))
```

All additions are modulo 2^32. The kernel checks the whole expression
from explicit definitions; no producer or old-verifier import is needed.

The tests also extract the four output expressions of
`examples/blake3-g.sexp` through the existing evaluator and certify each
normalization. Each proof fits the current byte and work limits. This
checks those exported equations, not the extraction's correspondence to
the source specification. That connection, complete symbolic execution,
and native ISA refinement remain separate obligations. The owner must
still select the theory and equation whose meaning they intend.

## Symbolic execution of a register program

`examples/proofs/register.theory.sexp` extends Word32 arithmetic with an
explicit abstract machine: six initialized registers (`a`, `b`, `c`, `d`,
`x`, `y`), register addition and XOR, 32 immediate right-rotation forms,
and a finite instruction list. Register reads and writes are exhaustive
constructor definitions. Each step reads its operands from the incoming
state, then writes the destination; source/destination aliasing is defined.
`run` recursively executes the instruction list in order.

```sh
pypy3 tools/make_register_proof.py
pypy3 -m ode.proof_cli examples/proofs/register.theory.sexp \
  examples/proofs/register-g.goal.sexp examples/proofs/register-g.proof.sexp
```

The theorem says the 14 register operations of BLAKE3 G produce its four
mixing equations and preserve the two message registers, for every initial
six-word state. The expected equations are written separately from the
instruction list. The proof composes two seven-instruction halves:
826 inference steps, four supporting lemmas, and 52,199 work units. The same reduction
producer handles closed arithmetic and symbolic register execution;
variables and arithmetic applications with symbolic structural arguments
remain terms until a constructor case is available.

Tests cover all 432 destination/source combinations for binary operations,
every rotation count with aliased and distinct source registers, and the
empty program. Wrong destination writes, skipped instructions, changed
instruction order, and corruption of a preserved register are rejected.
The expected equations are also cross-checked against extraction from
`examples/blake3-g.sexp`; this source-extraction correspondence is a test,
not a kernel theorem.

Program composition itself has a 20-step induction proof:
`run(append-program(p,q),s) = run(q,run(p,s))`, for all programs and
states. `tools/make_register_proof.py` emits this theorem as
`register-compose.goal.sexp` and `register-compose.proof.sexp`, alongside
the G execution proof. The tests check both the composed G proof and a
direct definition-reduction proof against exactly the same goal. The
composed proof has fewer bytes and uses fewer kernel work units; these
are deterministic proof costs, not runtime timing measurements.

This is a theorem about the declared abstract machine. It has no memory,
flags, uninitialized registers, byte decoder, or native calling convention.
Its correspondence with AArch64 execution remains an explicit refinement
obligation. The existing native certificates retain their larger reliance
set. File verification of this abstract execution proof needs neither the
old executor nor any proof producer.

## Execution to normalized outputs

`ode.register_proof.normalized_output` combines a checked state-execution
lemma with a checked arithmetic-normalization lemma and a register
projection. The resulting goal starts at `state-r(run(program,state))`
and ends at the normalized Word32 expression. Each goal states exactly
which register it proves; tests construct and check all six G outputs.

```sh
pypy3 tools/make_register_output_proof.py
pypy3 -m ode.proof_cli examples/proofs/register.theory.sexp \
  examples/proofs/register-g-normalized-b.goal.sexp examples/proofs/register-g-normalized-b.proof.sexp
```

The committed example is G's most complex output, register `b`: 905,436
proof bytes and 767,938 work units, within the existing
1,000,000-byte limit. The regression tests check it through the bounded
file reader as well as the kernel. More complex programs need further
proof decomposition or smaller derivations, rather than an assumption
that arbitrary whole-program expansion will fit.

The execution lemma remains part of the assembled proof. An invalid
execution derivation cannot be hidden by a valid normalization proof,
and changing the selected output is rejected. A fresh-process check
blocks all producers and the old executable verifier. The theorem still
concerns the abstract register machine; native ISA and memory refinement
remain separate obligations.

## Instruction encodings and exact bytes

`examples/proofs/encoding.theory.sexp` extends the abstract register model
with declared encodings for 32-bit unshifted ADD, EOR, and immediate ROR
(EXTR with equal source registers). Abstract `a,b,c,d,x,y` map to physical
W3 through W8. Five explicit register-bit functions and constructor bit
permutations define each instruction word. `encode-program` maps a finite
instruction list to a list of Word32 instruction words.

```sh
pypy3 tools/make_encoding_proof.py
pypy3 -m ode.encoding_cli examples/proofs/encoding.theory.sexp \
  examples/proofs/encoding-g.goal.sexp examples/proofs/encoding-g.proof.sexp \
  examples/proofs/encoding-g-execution.goal.sexp examples/proofs/encoding-g-execution.proof.sexp \
  examples/proofs/encoding-g.bin
```

The checker verifies both owner-selected equations, requires that they
name exactly the same instruction list, and binds the encoded words to
the exact 56 bytes read from the file. A valid execution theorem for a
different program is rejected. The encoding proof uses 280 inference steps; the
execution proof uses 864. The binary is an arithmetic fragment, **not a
callable function**: it has no loads, stores, or RET.

The owner-facing specification is `examples/proofs/g-definition.sexp`:
three declarative definitions state the first half-round, second
half-round, and their composition as `g`. They contain no register
instructions. The execution goal is `run(program,s) = g(s)` for every
State `s`; structural induction connects the named specification to the
proved register equations. The encoding theory carries those definitions,
so its owner pin fixes their exact meaning. Changing the specification's
final rotation invalidates the execution proof.

This named specification is directly inside the kernel's theory. The
older `examples/blake3-g.sexp` is still cross-checked as a separate source
representation; no theorem about translating that source syntax is claimed.

Program matching and byte binding rely on `ode/encoding_cli.py`, literal conversion in
`ode/word_literal.py`, and file I/O in addition to the kernel. The reader
compares literal instruction words in little-endian order and does not
execute the file. The owner still selects the theory and goal. File
verification blocks imports of all producers and the old executable
verifier in its independence test.

Tests cover all 432 binary register combinations, every rotation count
with aliased/distinct sources, and corruption of each byte. A separate
AArch64 test adds a load/store/RET wrapper and compares native execution
with the existing G specification on edge cases and 100 seeded random
inputs. This is a CPU cross-check; it is not an Arm ISA refinement proof.
The declared encoding model, the abstract instruction meanings, memory,
and calling conventions still need their formal native correspondence.

## Unbounded loops over register programs

`examples/proofs/register-loop.theory.sexp` gives two definitions of
repeated execution: `repeat-program(n,p)` concatenates a program `n`
times, while `iterate-program(n,p,s)` updates the state by running `p`
once and recursing on the remaining count. The kernel proves their
equivalence for every natural count, program, and state.

It also proves explicit register-program batching:

```
iterate-program(double(n), p, s)
  = iterate-program(n, append-program(p,p), s)
```

```sh
pypy3 tools/make_register_loop_proof.py
pypy3 -m ode.proof_cli examples/proofs/register-loop.theory.sexp \
  examples/proofs/register-iterate.goal.sexp examples/proofs/register-iterate.proof.sexp
pypy3 -m ode.proof_cli examples/proofs/register-loop.theory.sexp \
  examples/proofs/register-batch.goal.sexp examples/proofs/register-batch.proof.sexp
```

The two proofs take 38 and 47 inference steps, including the general
program-composition lemma. They use structural induction and the explicit
instruction semantics, with no length bound or evaluator callback.
Tests instantiate batching with G's instruction list and reject incorrect
count doubling, omitted repetitions, wrong goal counts, and missing cases.

These are state-equivalence theorems in the register model. They do not
yet specify native branches, memory traces, instruction timing, or the
performance of a loop implementation.

## The logic

Terms are sorted, first-order applications. Equality has its ordinary
meaning. A sort is either an arbitrary nonempty set or a datatype of
finite, freely generated constructor trees. `Nat` is the built-in
datatype with `zero` and `succ`; the standard finite natural numbers.
Declared function symbols denote arbitrary total functions of their
stated sorts. Variables in a goal are universally quantified.

A datatype's constructor fields may use earlier sorts or the datatype
itself. There must be a constructor with no self-recursive fields, so
values can be constructed. This first-order form has no negative type
occurrences, mutual datatype recursion, or hidden function-valued fields.

A theory introduces functions by **structural recursion** on their first
argument. It supplies exactly one case for each constructor. In a case,
every self-call must take a direct field of the same datatype as its
first argument. Other arguments may change. Definitions may use earlier
functions; they cannot refer forward. In a leaf case there are no
recursive fields, so no self-call is possible.

These restrictions give each definition a unique total interpretation:
by induction on the first argument's finite constructor tree, every
self-call uses a smaller value. Definitions add names for functions,
rather than assumptions about existing functions. There is no field for
axioms, admitted equations, solver verdicts, or evaluator callbacks.

### Objects and identities

The version-3 grammar uses positional s-expressions; every field and
arity is checked. Files may have formatting and `;` comments. Identities
are BLAKE3 hashes of the canonical forms from `ode/canon.py`.

```lisp
(theory 3
  (OpaqueSort (DataSort ((constructor (FieldSort ...)) ...)) ...)
  ((function (ArgumentSort ...) ResultSort) ...)
  ((defined-function ((subject DataSort) (parameter Sort) ...) ResultSort
     ((constructor (field-variable ...) body) ...)) ...))

(goal 3 #theory-hash
  ((variable Sort) ...)
  (eq left-term right-term))

(proof 3 #goal-hash
  ((lemma ((parameter Sort) ...) (eq left right) derivation) ...)
  derivation)
```

A term is a variable name or `(function argument ...)`. Constants are
zero-argument applications, such as `(zero)` and `(bit0)`. Definitions
are ordered. Sorts, functions, and parameters have unique names in their
respective scopes. Constructor names share the function namespace.

The structural parameter is unavailable in case bodies. A case sees the
remaining parameters and fresh field variables, with the sorts declared
by the constructor. Every self-call is checked to use one of the
recursive fields as its first argument.

The relying party selects the theory and goal independently of the
proof. A producer can know every hash and recompute hashes honestly;
this grants no ability to change the selected statement. Hashes fix
identity; the rules below establish truth.

### Rules

A proof block is a nonempty list of instructions. Each instruction
**infers** an equation, which is available to later instructions by its
zero-based index. The last equation must be exactly the required result.
A reference must identify an earlier step in this block.

| Instruction | Inferred equation or condition |
|---|---|
| `(refl t)` | `t = t` |
| `(sym p)` | `b = a`, from step `p: a = b` |
| `(trans p q)` | `a = c`, from `p: a = b` and `q: b = c`; the middle terms must coincide |
| `(cong f p ...)` | `f(a,...) = f(b,...)`, from argument equations `a = b, ...`; sorts and arity must fit `f` |
| `(unfold f arg ...)` | `f(arg,...) = body`, by instantiating a defining case; the first argument must visibly begin with that case's constructor |
| `(ih field arg ...)` | An instance of the hypothesis for that recursive field; the field itself is fixed, only the generalized parameters are substituted |
| `(lemma index arg ...)` | An instance of an earlier, completely proved lemma; substitution covers its parameters in declaration order |

There are two derivation forms:

- `(derive (instruction ...))` proves the goal directly.
- `(induct subject ((constructor (field ...) (instruction ...)) ...))`
  proves it by structural induction on a declared variable of a datatype.
  There must be exactly one case per constructor, with fresh field names.

For a goal `P(subject, parameters)` (where `P` is an equation), each
constructor case must prove `P(constructor(fields), parameters)`. It gets
one hypothesis **for all parameters, `P(field, parameters)`** per direct
field of the subject's datatype. A leaf case has no hypotheses. An `ih`
instruction names the recursive field, then supplies exactly the
generalized parameters, in their goal-declaration order with `subject`
removed. It cannot supply a new value for that field. Substitution is
simultaneous and sort-preserving; terms being substituted have no binders.

Natural induction is this same rule: the `zero` case has no hypotheses;
the `succ(k)` case has the hypothesis at `k`. For a binary tree, a node
with two recursive children has two hypotheses. Both forms are tested.

A proof carries an ordered list of lemmas followed by its final derivation.
Each lemma is a universally quantified equation proved in the same theory
using only earlier lemmas. Every lemma is checked, even if unused; it
becomes available only after its entire proof passes. Self references,
forward references, and exporting a local induction hypothesis are
rejected. Each derivation has either an equational block or a root
induction; this suffices to reuse inductive lemmas in later inductions.
Version 1 and 2 objects are rejected.

The rule does not invoke Python's evaluator, test sample counters, or
assume a conclusion because a producer calls it an invariant.

### Why the rules are sound

Reflexivity, symmetry, transitivity, and congruence preserve equality in
every sorted interpretation. Unfolding instantiates a defining equation
of a total function established by the structural-decrease check. In
an induction case, every hypothesis instance holds for a strictly
smaller constructor field, for arbitrary parameters. Checking all cases
therefore establishes the equation on every finite constructor tree.
Freshness and scope checks keep hypotheses out of other cases and out
of the final context. A proved lemma is universally quantified, so
sort-preserving simultaneous substitution preserves its truth in later
proofs. No theorem can depend on itself: publication follows verification.

This argument is written for human review; it is not a machine-checked
metatheorem about the Python implementation. The kernel's implementation,
the parser/hash code, Python, and its execution environment remain in
the reliance set.

## Efficient, finite checking

Terms are hash-consed in a local arena. Proof steps carry small term
identifiers internally; congruence and equation comparisons reuse shared
subterms. Substitution visits each reachable DAG node once per operation
and substitutes simultaneously. The 50-doubling test represents an
exponentially large expanded tree with 51 shared nodes.

Checking has explicit limits: 1,000,000 source bytes per object, syntax
and term depth at most 128, tokens at most 128 characters, and 1,000,000
work units per invocation (the caller can choose a smaller budget).
Syntax visits, rule visits, term construction, and substitution consume
work. Parsing and hashing are separately bounded by the byte and depth
limits. Exhaustion rejects; it never becomes a slower or partial proof.
These are certificate limits, **not bounds on the quantified counter**.

The implementation does not claim a near-linear bound for every proof:
repeated substitutions can revisit terms. Nor does it claim measured
speed or energy savings; timing measurements must use `clocks`. The
reported work counts are deterministic diagnostic counts, not clocks.

## Review and adversarial checks

```sh
pypy3 -m unittest tests.test_kernel tests.test_nat_proof tests.test_bits_kernel
pypy3 -m unittest tests.test_xor32_proof tests.test_rotate32_proof tests.test_add32_proof
pypy3 game/kernel_attacks.py
```

The corpus tests missing base/step proofs, hypothesis leakage, eigenvariable
capture, changing the predecessor, forward references, wrong sorts,
non-decreasing recursion, changed theories and goals with honestly
recomputed hashes, fake oracle rules, and exhausted resource budgets.
There is a positive control as well as negative cases. A temporary
mutant kernel with its transitivity check removed accepts `zero = succ(zero)`;
the real kernel rejects the same proof, showing that the negative control
distinguishes that broken rule implementation. A second mutant, with
constructor-case coverage removed, admits `bit0 = bit1` by vacuous
induction; the real kernel rejects it. The file-interface
test runs the command a recipient would run, then corrupts the proof.

The scripts `tools/make_batching_proof.py`, `tools/make_nat_add_proof.py`,
`tools/make_chain_split_proof.py`, `tools/make_xor_proof.py`,
`tools/make_xor32_proof.py`, `tools/make_rotate32_proof.py`, and
`tools/make_add32_proof.py`, and `tools/make_constant_proof.py` reproduce
the goals and proofs. The Word32
XOR and rotation exporters ask the existing symbolic normalizer for its
proposed result. All producers emit explicit proof steps. Generated
proof bytes are included here because this is the artifact Bob checks
without running the producer. The theorem statement travels separately.

## Delivery through the pinned bootstrap

The kernel fragment recipient in `game/kernel-base/` runs through the
existing hash-pinned root launcher. Owner pins separately identify its
code package, theory, encoding goal, and execution goal. Delivery may be
adversarial; the recipient checks the pins before checking the proofs and
matching the bytes. It uses the same in-memory objects it read, and
contains no symbolic verifier, native runner, or proof producer.

See `game/README.md` for the command and full reliance boundary.
`tests/test_kernel_bootstrap.py` tests honest and alternative-proof
controls, changed package code, changed owner claims, corrupt proofs and
bytes, and missing artifacts. `game/pin_ode_base.py` refreshes both
recipient packages; owner semantic pins remain explicit and unchanged.

## Place in Ode

This is the first small, precisely specified proof-object kernel for
option C. Sorted equality and structural induction express unbounded
loop laws and word identities with one mechanism, without a fixed-point
logic's additional machinery. This is not an implementation
of matching μ-logic, which the early design proposed.

The kernel is the intended destination for the existing symbolic
checker's work, not a second route to silently accept rejected program
certificates. Today it checks mathematical proof objects; `check.py`
still verifies executable programs using its larger reliance set. The
next connection is to combine the Word32 arithmetic exports with explicit
word/ISA execution semantics and make the symbolic checker **emit derivations**
for whole programs. Loop claims
then need invariants and refinement proofs in that same logic. Until
those connections are checked, the batching theorem and the native
BLAKE3 results remain distinct claims.
