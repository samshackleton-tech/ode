# The proof-object kernel

`ode/kernel.py` checks explicit equational proofs, including induction over
natural numbers. Its first theorem is a loop transformation relevant to
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

## The logic

Terms are sorted, first-order applications. Equality has its ordinary
meaning. `Nat` is the standard set of finite natural numbers, with
constructors `zero` and `succ`. Other sorts denote arbitrary nonempty
sets, and declared function symbols denote arbitrary total functions of
their stated sorts. Variables in a goal are universally quantified.

A theory can introduce functions by **counter-decreasing recursion**.
Each definition supplies its value at zero and its value at a successor.
In the successor equation, every self-call must have the predecessor as
its first argument. Other arguments may change. Definitions may use
previously declared functions; they cannot refer forward. The zero
branch cannot refer to the function being defined.

These restrictions give each definition a unique total interpretation:
by induction on the first argument, every self-call in the successor
body uses an already defined level. Definitions add names for functions,
rather than assumptions about existing functions. There is no field for
axioms, admitted equations, solver verdicts, or evaluator callbacks.

### Objects and identities

The version-2 grammar uses positional s-expressions; every field and
arity is checked. Files may have formatting and `;` comments. Identities
are BLAKE3 hashes of the canonical forms from `ode/canon.py`.

```lisp
(theory 2
  (ExtraSort ...)
  ((function (ArgumentSort ...) ResultSort) ...)
  ((defined-function ((counter Nat) (parameter Sort) ...) ResultSort
     zero-body
     (predecessor successor-body)) ...))

(goal 2 #theory-hash
  ((variable Sort) ...)
  (eq left-term right-term))

(proof 2 #goal-hash
  ((lemma ((parameter Sort) ...) (eq left right) derivation) ...)
  derivation)
```

A term is a variable name or `(function argument ...)`. Constants are
zero-argument applications, such as `(zero)`. Theory definitions are
ordered. Names of sorts, functions, and parameters must be unique in
their respective scopes. The counter parameter is unavailable in both
bodies; the predecessor exists only in the successor body. This makes
which count a recursive call uses explicit.

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
| `(unfold f arg ...)` | `f(arg,...) = body`, by instantiating the function's zero or successor equation; the first argument must visibly be `(zero)` or `(succ k)` |
| `(ih arg ...)` | An instance of the induction hypothesis; only available in the step block, with the predecessor fixed |
| `(lemma index arg ...)` | An instance of an earlier, completely proved lemma; substitution covers its parameters in declaration order |

There are two derivation forms:

- `(derive (instruction ...))` proves the goal directly.
- `(induct n k (base-instruction ...) (step-instruction ...))` proves the
  goal by induction on its declared `Nat` variable `n`. `k` must be a
  fresh name. Both blocks are checked, in separate scopes.

For a goal `P(n, parameters)` (where `P` is an equation):

1. The base block proves `P(zero, parameters)`, with no induction
   hypothesis. `n` and `k` are absent from its variable context.
2. The step block proves `P(succ(k), parameters)`, with arbitrary `k`
   and the hypothesis **for all parameters, `P(k, parameters)`**.
3. An `ih` instruction supplies exactly the generalized parameters, in
   their goal-declaration order with `n` removed. It cannot supply a new
   value for `k`. Substitution is simultaneous and sort-preserving; terms
   being substituted have no binders.

A proof carries an ordered list of lemmas followed by its final derivation.
Each lemma is a universally quantified equation proved in the same theory
using only earlier lemmas. Every lemma is checked, even if unused; it
becomes available only after its entire proof passes. Self references,
forward references, and exporting a local induction hypothesis are
rejected. Each derivation has either an equational block or a root
induction; this suffices to reuse inductive lemmas in later inductions.
Version 1 objects are rejected.

The rule does not invoke Python's evaluator, test sample counters, or
assume a conclusion because a producer calls it an invariant.

### Why the rules are sound

Reflexivity, symmetry, transitivity, and congruence preserve equality in
every sorted interpretation. Unfolding instantiates a defining equation
of a total function established by the counter-decrease check. In the
step block, every hypothesis instance holds at the fixed predecessor
for arbitrary state parameters, so ordinary equational reasoning
preserves it. The separately checked base and step establish the goal
for every natural number by induction. Freshness and scope checks keep
the hypothesis out of the base and out of the final context. A checked
lemma holds for all its declared parameters; sort-preserving simultaneous
substitution therefore preserves its truth in later proofs. No theorem
can depend on itself because it is published only after verification.

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
pypy3 -m unittest tests.test_kernel tests.test_nat_proof
pypy3 game/kernel_attacks.py
```

The corpus tests missing base/step proofs, hypothesis leakage, eigenvariable
capture, changing the predecessor, forward references, wrong sorts,
non-decreasing recursion, changed theories and goals with honestly
recomputed hashes, fake oracle rules, and exhausted resource budgets.
There is a positive control as well as negative cases. A temporary
mutant kernel with its transitivity check removed accepts `zero = succ(zero)`;
the real kernel rejects the same proof, showing that the negative control
distinguishes that broken rule implementation. The file-interface
test runs the command a recipient would run, then corrupts the proof.

The scripts `tools/make_batching_proof.py`, `tools/make_nat_add_proof.py`,
and `tools/make_chain_split_proof.py` reproduce the goals and proofs. They
import neither the kernel nor the existing program verifier. Generated proof
bytes are included here because this is the artifact Bob checks without
running the producer. The theorem statement travels separately.

## Place in Ode

This is the first small, precisely specified proof-object kernel for
option C. Ordinary sorted equality and natural induction earn their
place now: they express the first unbounded loop theorem without a
fixed-point logic's additional machinery. This is not an implementation
of matching μ-logic, which the early design proposed.

The kernel is the intended destination for the existing symbolic
checker's work, not a second route to silently accept rejected program
certificates. Today it checks mathematical proof objects; `check.py`
still verifies executable programs using its larger reliance set. The
next connection is to formalize the word/ISA semantics and make the
symbolic checker **emit derivations** the kernel verifies. Loop claims
then need invariants and refinement proofs in that same logic. Until
those connections are checked, the batching theorem and the native
BLAKE3 results remain distinct claims.
