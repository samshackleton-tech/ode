# The proof-object kernel

`ode/kernel.py` checks sorted equations, conservative definitions, and
structural induction over finite constructor-built data. The owner selects
the theory and goal; anyone may supply the proof. The checker performs no
proof search or program execution, and proof objects cannot introduce axioms
or call an evaluator.

This page specifies the logic, serialized objects, rules, soundness
argument, and checking limits. [PROOFS.md](PROOFS.md) gives runnable examples:
unbounded loop laws, bit/word arithmetic, symbolic register execution,
instruction encoding, and exact fragment-byte binding.

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
pypy3 -m unittest discover -s tests
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

Reproduction commands live with the examples in [PROOFS.md](PROOFS.md).
Producers emit explicit derivations. Generated proof bytes are included
because they are the recipient's checked artifact; the recipient does not
run the producer. Theory and goal identities are selected independently.

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

Sorted equality and structural induction express unbounded loop laws,
word identities, and register execution with one mechanism. Matching
μ-logic remains a possible richer foundation if a concrete obligation
requires it.

The kernel checks the declared arithmetic and register-machine models.
The fragment recipient also binds exact bytes through the declared
instruction encodings. Native ISA refinement, memory and calling-convention
proofs, and translation of the older source syntax remain separate
obligations. Until those connections are checked, the existing executable
verifier in `ode/check.py` retains its larger reliance set.
