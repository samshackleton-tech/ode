# Ode: definition and specification

This document defines Ode and specifies what an implementation of Ode must do. `DESIGN.md`
states why Ode is shaped this way; this document states what Ode *is*, precisely enough that
two teams can build it independently and their tools agree. Where this document and
`DESIGN.md` differ, this document governs.

## 0. Definition

**Ode is a tool that produces high-performance cryptographic software together with
machine-checked proofs of the properties its users rely on, where every relied-upon claim
beyond a small, enumerated reliance set (§1) carries a proof certificate that anyone can
check independently, efficiently, and offline.**

An Ode user writes a *specification* of what a program must compute and which properties it
must have. Ode produces machine code that runs as fast as the best hand-tuned code for the
target, plus certificates. A small checker — the only program in a relying party's reliance set —
verifies the certificates against the specification as written. Everything between the
specification and the checker (generators, compilers, solvers, AI agents, optimizers) is a
producer outside the reliance set: its output is believed exactly when its certificate checks.

Ode serves teams of many AI agents directed by a few human engineers (`DESIGN.md` §1). The
humans read specifications, property definitions, decisions, and the generated assurance map.
The agents read and write everything else. Generated proofs carry no reading duty.

## 1. The reliance set

**A word on the word (Miller).** This document says *rely* and *reliance*, never
*trust*: trust names a feeling about a person's or institution's character, while
reliance names a specific property of a specific mechanism that a specific claim
rests on — and points at the vulnerability when it fails. Ask of every sentence here:
what is relied on, for what guarantee?

A claim in Ode rests on the reliance set below, and on nothing else. Each entry earns its
place by being irreducible with the tools available; each carries the mitigation that keeps
it small, and the check that keeps it honest. The assurance map (§7) prints this set, in
full, beside every claim it reports.

| # | Reliance | Why it is irreducible | Mitigation and check |
|---|---|---|---|
| R1 | The checker program (§4) computes what §4 specifies | Every verification ends at some program that is run rather than proved | The checker is small enough to read in one sitting (target: 3,000 lines) and is implemented independently at least twice; the implementations must agree on every certificate in the conformance corpus (§9). A later Ode milestone proves the checker's specification in Ode itself, leaving this entry as the bootstrap checker alone |
| R2 | The canonical-form reader (§2) reads exactly the bytes a hash names | A certificate is about bytes; something must connect bytes to meaning | The reader is part of the checker (R1), is a few dozen lines, and is checked by round-trip and mutant tests (§9) |
| R3 | The specification and the property definitions (§5) say what their owners mean | A checker confirms that a proof establishes its statement; what the statement means is a human judgment (Kobeissi) | Specifications and property definitions are short enough for their owners to read in full, are written by those owners, and are the specification of record (§3.1). Their hashes head every claim |
| R4 | The target ISA model (§3.3) matches the silicon it names | A proof about machine code is a proof about a model of the machine | The model derives mechanically from the vendor's formal semantics (Arm's ASL through Sail, for AArch64); every instruction form the model covers is cross-checked against the physical CPU on random states, and each shipped program re-checks itself on the user's machine before its first use (§7). The assurance map states which forms rest on which check |
| R5 | The physical machine executes its ISA, and its timing promises (e.g. Arm's data-independent-timing list) hold as the vendor states | No proof about code reaches physics | Constant-time claims (§5) name their exact scope: instruction and address traces proved in the model, instruction timing taken from the vendor's promise, power and clock effects declared outside the claim, on the face of the assurance map |
| R6 | BLAKE3 is collision-resistant | Content addressing (§2) names definitions by hash | One hash function, used everywhere; a collision would have to be exhibited against the published, heavily analysed function |

Everything else a user relies on — a compiler's output, a generator's kernel, a solver's
verdict, an agent's proof, a measurement's provenance — arrives with a certificate checked
under R1–R2, or appears in the assurance map as unproved (§7).

## 2. Objects: definitions, canonical form, names

**2.1 Definitions.** Every artefact in Ode is a *definition*: a specification, a function, a
kernel, a generator, a proof certificate, a property, a measurement, a decision, an ISA
model fragment. A definition is immutable. A definition's identity is the BLAKE3 hash of its
canonical form, and its dependencies appear inside the canonical form as their hashes. A
hash therefore fixes a definition and, transitively, everything it depends on: source,
generator, compiler, flags, property definitions, ISA model. Two agents adding definitions
never conflict, because they only ever add hashes.

**2.2 Canonical form.** Ode's one syntax is the s-expression: symbols, integers, and byte
strings (`#hex`) in nested lists; a symbol never begins with a digit, so no token has two
readings. Each kind of definition has exactly one canonical form — its s-expression
written with one space between elements and no other whitespace — a deterministic byte
encoding with these properties —

- *Injective:* distinct definitions encode to distinct bytes (up to R6).
- *Self-delimiting and total to read:* the reader (R2) accepts a byte string as exactly one
  definition or rejects it; every accepted string has exactly one meaning.
- *Dependency-explicit:* every reference to another definition is its hash, in a fixed
  position determined by the kind.
- *Stable:* the encoding of a kind changes only by a new version of this specification, and
  a reader rejects versions it does not implement (contracts change everywhere at once;
  `AGENTS.md`).

The canonical form is the only form the checker reads. Text and graphical forms are
projections (§8) produced from it and parsed back into it; a projection is a view, never a
second source.

**2.3 Names.** A *name directory* maps human- and agent-chosen names (pet names) to hashes.
Names live outside definitions, carry no authority, and differ between projects and people.
Repointing a name is a reviewed act recorded as a decision definition (§7). Renaming never
changes a hash.

**2.4 Definitions carry no authority.** Loading, caching, copying, or checking a definition
confers no power to act. Authority exists only as capabilities at run time (§6).

## 3. The language: three layers and a binary

An Ode program is a tower of layers. Each lower layer implements the one above under a
proved correspondence (Rideau's hypo- and hyper-systems; contiguous layers compose). A
definition lives at exactly one layer.

### 3.1 The specification layer

The specification layer is a pure, strict, definite functional language (Hopwood's
Noether-0): every computation succeeds deterministically with one result or fails in finite
time; functions are given by equations. It has integers and exact fixed-point arithmetic as
its numeric base, no implicit coercions, no overloading, no undefined behaviour, and one way
to say each thing.

- A specification written here is *executable*: the same definition is the reference
  implementation, the generator of test vectors, and the statement of every theorem about
  the program. A standard (e.g. C2SP's BLAKE3) is transcribed once, by its owners, and that
  transcription is the specification of record: prose documents, implementations, and test
  suites are checked against it, never the reverse.
- Specifications are small by construction. The language offers the least expressiveness
  that states the domain (Kobeissi's rule of least power): a specification layer program
  that needs a feature outside the layer states that need as an obligation (§7), visibly.
- Termination and failure are part of the meaning: a definite function either returns its
  unique value or fails, and callers see which, in the type.

### 3.2 The generator layer

The generator layer adds staging — quotation and splicing in the style of MetaML — to the
specification layer. A staged definition means exactly its unstaged elision. Generators are
specification-layer programs run at generation time; their outputs are definitions at a
lower layer, each shipped with the certificate that the output meets the specification it
was generated from. Performance-critical code is normally *generated and proved*, never
hand-written and transcribed: a generator emits a data structure together with its theorem
(blake3-servil, lesson 2).

Generators run with no authority beyond the definitions they are given (§6), in a definite
language, so generation itself terminates or fails, deterministically, from hashed inputs:
same inputs, same output hash, on every machine.

### 3.3 The machine layer

The machine layer is typed, structured assembly for one named ISA. It makes speed a matter
of explicit choice:

- exactly the vendor's formally defined instructions for that ISA (for AArch64, Arm's ASL
  through Sail), each with its semantics given by the ISA model definition (R4);
- explicit registers, vector lanes, predicates, and matrix tiles; loops over counts the
  type system knows; straight-line code and structured control flow only;
- no computed jumps, no self-modifying code, no memory access except through the buffer
  capabilities the definition is handed (§6);
- types that state each buffer's length, alignment, and permissions, and each value's
  width and signedness, so a kernel's contract — which buffers it reads, which it writes,
  which lengths it covers — is a property of its definition, checkable before any proof.

A machine-layer definition plus its ISA model determines its execution completely. Glue
code (dispatch, tree walks, buffering) is specification-layer code lowered by a certifying
compiler: the compiler is a producer, and each output carries its refinement certificate
(§4), so no compiler is relied on, of any size, written in any language.

### 3.4 The binary

A deterministic emitter turns a machine-layer definition into bytes. Same definition hash,
same bytes, on every machine and every run; the emitter is itself a producer whose output
identity is established by re-emission and byte comparison, a check anyone can repeat. What
is proved is the bytes that run: a claim about a kernel names the hash of the machine-layer
definition and the hash of its emitted bytes, and the checker binds them.

### 3.5 Extension

A specification is extended by mixins: a new kernel, platform, or variant is a mixin on the
existing specification (`super` is the choice so far, `self` the final dispatch), and the
running library is the fixed point. Each mixin carries its contract, so extension happens
behind stable interfaces and changes exactly the hashes that depend on it.

## 4. The logic and the checker

### 4.1 One logic

The proof-object kernel uses sorted equational logic with structural induction over
finite constructor-built data, including naturals and bit strings. `KERNEL.md` specifies its current format, rules, semantics, and resource
limits; `ode/kernel.py` implements it. Checked theorems include loop batching and
chain splitting for arbitrary iteration counts, and XOR cancellation for every finite
bit-string width. Definitions must visibly decrease their structural argument. Lemmas become usable only after their complete derivations check;
proofs introduce no axioms, evaluator shortcuts, or solver verdicts.

The goal is one logical foundation for program certificates. Language and ISA semantics
must be formalized in it, and producers must emit proofs of refinement against those
semantics. The existing symbolic verifier (`ode/check.py`) has not yet been translated
into this foundation; its executable-code results still rely on its own evaluator,
normalizer, and instruction models. The first bridges export XOR and immediate-rotation normalization derivations
against explicit Word32 semantics (`ode/xor32_proof.py`, `ode/rotate32_proof.py`).
A separate ripple-carry definition has checked commutativity, zero-identity,
and associativity proofs (`ode/add32_proof.py`, `ode/add_associativity_proof.py`). Closed arithmetic expressions have evaluation-proof
exports (`ode/constant_proof.py`). Symbolic addition flattening, reordering,
and zero elimination have checked exports (`ode/add_normalizer_proof.py`);
nonzero constant folding within symbolic expressions remains open. The native representation and complete
instruction-semantics bridge remain open: these rewrite theorems alone do not prove
those executable bytes.

Matching μ-logic was the initial candidate. The current milestone needs equality and
induction, so the first kernel states these directly. Richer logic earns its place with
a concrete obligation the current rules cannot express, and an explicit soundness
argument. Its addition must preserve the meanings and guarantees of existing theorems.

### 4.2 Certificates

A *certificate* is a definition (§2) stating: the hashes it is about, the claim (a statement in
the logic, built from named property definitions, §5), and a proof object the checker
verifies. Ode has three kinds:

- **Correctness:** a definition meets its specification, in the stated property.
- **Execution:** a computation ran and gave its stated result, succinctly — a run by
  any agent or machine can be checked without being repeated; because the checker is
  small, a succinct proof that the checker accepted a certificate can stand in for the
  certificate itself.
- **Attestation:** an identified auditor's signed statement about a definition, carrying
  its recipe for rechecking. An attestation discharges an obligation at load time (§7) and
  ranks below a correctness certificate wherever both exist.

A certificate names its subject by hash over everything that shapes the subject's meaning
and machine code: source, generator and its inputs, compiler and flags, property
definitions, ISA model, and relevant initial state (blake3-servil, lesson 1). A change to
any of these is a new subject and needs its own certificate; there is no stored claim of
proof, only certificates and the records of their checking (§7).

### 4.3 The checker

The checker is one program, specified by this document and an accompanying formal
statement of the logic's rules, small enough to read in one sitting (target: 3,000 lines,
with the canonical-form reader of R2 inside it). Its contract:

- **Soundness-shaped interface.** It takes a canonical-form certificate and answers
  *accepts* or *rejects*, with a structured reason for every rejection. It has no third
  outcome and no silent modes: malformed input, unknown versions, and unsupported rules
  are rejections.
- **Determinism and offline operation.** Same input, same verdict, with no network, no
  clock, no randomness, and no ambient authority (§6). It runs in a confined process whose
  only inputs are the certificate bytes.
- **Efficiency.** Checking shares repeated terms and obeys explicit limits on input
  size, term depth, and work. Exceeding a limit rejects the certificate; it never
  weakens the claim. `KERNEL.md` states the implemented limits. A near-linear cost
  for arbitrary proofs, or checking always costing less than producing, requires a
  demonstrated bound; neither is assumed. Wall-time and cycle measurements follow §10.
- **Independence.** The checker is implemented at least twice, by different authors from
  this specification, in different implementation languages. Both must agree on the whole
  conformance corpus (§9). Either implementation alone suffices to rely on a claim.
- **Negative tests travel with it.** The checker ships with planted-error certificates —
  wrong conclusions, off-by-one steps, dropped hypotheses, mutant subjects — each of
  which it must reject (§9). A checker that has never been seen to fail is not evidence.

Producers (solvers, tactic engines, compilers, agents) carry no reliance and are interchangeable.
A producer's speed, cleverness, or reputation contributes nothing to a claim; only its
certificates count. A producer may be written in any language, including Ode itself.

## 5. The property library

Claims are stated with *property definitions*: named, versioned definitions of what a
property means — functional correctness against a named specification, constant-time
within a stated scope (R5), reads-and-writes-only-its-own-buffers, memory safety, bounds
on time and memory. Properties come from a small standard library:

- each property is defined once, in the logic (§4.1), reviewed in public, and versioned;
  a claim names the property and its version by hash, the way a protocol names
  AES-256-GCM (Kobeissi);
- the library grows by public argument and new versions, and a new version never changes
  an old version's meaning: old claims keep their hashes and their meaning, and the
  assurance map lists the claims a new version invites its owners to recheck;
- a need outside the library is stated as a bespoke property definition, which appears in
  the assurance map labelled as bespoke, with its own hash and reading duty — visible,
  priced, and never silently promoted to a standard name;
- every standard property ships with test definitions it must accept and attacks it must
  flag (a wrong rotation, a dropped flag, a secret-dependent branch), checked in the
  conformance corpus (§9).

Property definitions are part of R3: they are short, owned, and read in full by the people
who rely on claims stated with them. Their size counts against the reading budget of §8.

## 6. Authority at run time

**Memory safety and capability safety hold for all code Ode emits, proved or not.** This is
a property of the machine layer and its emitter, not of any proof:

- a reference is unforgeable; capabilities arise only from creation and are acquired only
  by being passed — only connectivity begets connectivity (Miller). There is no ambient
  authority: no global names for files, networks, clocks, devices, or other definitions'
  powers;
- invoking anything — calling a function value, sending a message, reading or writing a
  buffer, using a device — means holding a capability to it. A kernel receives exactly its
  input and output buffers as capabilities, so "reads and writes only its own buffers" is
  true by construction before any proof begins, and the proof of §5's property then covers
  the kernel's behaviour within them;
- code that arrives from outside Ode runs under a loader that gives any input a safe
  meaning (Fil-C's "garbage in, memory safety out", lifted to capabilities): whatever the
  bytes are, the loaded code acts only through the capabilities it is handed, and every
  possibly-unsafe operation is checked, in software or in hardware capabilities (CHERI);
- in proved code, the emitter erases exactly the checks a certificate shows unnecessary;
  elsewhere the checks stay. Erasure is thus a proved optimisation, recorded per check in
  the assurance map.

Definitions (§2) are inert: authority exists only in a running program, only as
capabilities created at its start and passed along its connectivity graph. Ode programs
are crash-only: state lasts until the process ends, and no code is written to shut down or
reclaim (with the usual test-suite exception; `AGENTS.md`).

## 7. Obligations, discharge, and the assurance map

Each specification generates *obligations*: the claims a relying party needs, stated with
property definitions (§5) over named hashes. Each obligation is discharged at exactly one
recorded stage —

| Stage | Discharge |
|---|---|
| before running | a correctness certificate (§4) |
| on loading code | an auditor's attestation |
| at a call boundary | a guard, which coerces or ejects, naming the party at fault (E's guards; Racket's contracts with blame) |
| inside a computation | a fail-stop assertion |
| at startup | a self-test against the actual machine: fixed inputs with known answers that together exercise every shipped kernel path, each case feeding the next, a wrong answer stopping the program before its first real input (R4) |
| afterwards | a monitor or sampler |

— and the record names the hash of what discharged it. A proof erases the corresponding
guard; a guard on a value known early is already a proof. Discharge at a weaker stage when
a stronger one was available is a visible fact, not a silent default.

**The assurance map is generated, never written.** For any hash, the map is computed from
checker records and discharge records, and it states, in the vocabulary of §5:

- every claim, with the hashes of its subject, its property definition and version, its
  certificate, and the checker implementation and version that accepted it;
- every obligation discharged at a stage short of proof, with its stage and its discharger;
- every gap: unproved obligations, bespoke properties, ISA forms resting on CPU checks
  rather than vendor-semantics proofs, timing scope limits (R5) — each as a first-class entry
  with its reason, beside the proved claims, in the same type size.

A sentence about what is proved exists only where a record generates it (blake3-servil,
lessons 4 and 9; Kobeissi on verification theatre). Hand-written assurance prose is a
projection of the map (§8) with no sentences of its own. Decisions — who decided what,
when, why, with what evidence — are definitions attached to what they decide, and promotion
of a shared name requires the evidence the project's policy names (certificates,
measurements, reviews), recorded with the name's new hash.

## 8. Surfaces for humans

Humans read projections, never canonical forms, and each projection is generated from the
hashes it describes:

- **Specifications**, as precise mathematics in plain notation, sized for reading in full
  (§3.1, §5): the reading budget of a claim — the specification plus each property
  definition it invokes — is stated on the assurance map as a count the owners can weigh;
- **the assurance map** (§7), including the reliance set (§1) printed in full;
- **decision prompts**: at a real trade-off, the options with their numbers, the decision
  recorded as a definition;
- **measurement reports** (§10);
- **projections** of any definition, proof step, counterexample, or rejected certificate,
  for the exceptional investigation.

## 9. Conformance: what makes an implementation Ode

An implementation may call itself Ode when it meets every clause of this section. Each
clause is a test, and the corpus that runs them is public and versioned with this
specification.

1. **Checker agreement.** Both independent checker implementations accept exactly the
   conforming certificates and reject every planted-error certificate in the corpus:
   wrong conclusions, invalid rule steps, certificates about mutant subjects (a rotation
   off by one, a dropped root flag, a flipped constant), unsupported versions, and proofs
   resting on admitted steps presented as proved. (§4.3)
2. **Determinism.** Canonical encoding, generation, emission, and checking are
   deterministic: equal inputs give byte-identical outputs and identical verdicts on
   every conforming implementation and machine.
3. **Binding.** Every accepted claim is re-derivable from its named hashes alone: fetch
   the definitions by hash, re-check the certificate, regenerate the assurance-map entry,
   and obtain the stated claim — offline, without the producer.
4. **Confinement.** The checker and every emitted program run with only the capabilities
   they are handed; the conformance suite runs both in a capability-confined harness with
   no ambient authority and observes no attempt to exceed it.
5. **Self-knowledge.** The implementation reports its own version, the specification
   version it implements, and the checker-cost constants of §4.3, as definitions any user
   can hash and cite.
6. **Cost of checking.** The checker enforces its declared input, term, and work limits;
   the corpus includes exhaustion tests. Reported cost counts describe the actual
   checking algorithm. Speed claims require measurements under §10. (§4.3)

Speed of the *produced code* is specified separately (§10): it is a property of a
definition on a machine, measured and recorded, never asserted by the toolchain.

## 10. Performance and measurement

Performance is part of correctness (a right answer too late or too costly is wrong;
`AGENTS.md`), and Ode's machine layer exists so that the fastest known technique for a
kernel — explicit instruction choice, lanes, tiles, staging through generators — is
expressible without leaving the proved world. Two rules keep speed honest:

- **Speed is a property of a hash on a machine.** A measurement is a definition keyed by
  (code hash, benchmark hash, machine, conditions), recording wall time and the thread's
  core cycles per core kind as integers, through the team's `clocks` crate. Comparisons
  take pairs of runs, one of each side, back to back in alternating order, judged by their
  pairs' ratios (run means, median beyond the margin, exact sign test; `clocks::summary`).
  A measurement taken while the machine was busy is no evidence.
- **No speed claim without a measurement definition, and no silent regressions.** A claim
  that one definition is faster than another names both hashes and the measurement hashes
  backing it, and appears in the assurance map's neighbourhood as a computed report. A
  change that slows a shipped hash is a bug of the same rank as a wrong answer.

## 11. Bootstrapping

Ode is built in stages, each stage's reliance coming from the stage before:

1. The checker's specification and first two implementations, written in existing tools,
   reviewed as R1 demands — the one place existing tools are load-bearing, and the last.
2. The canonical-form tools, generator layer, and certifying compilers, built as producers:
   believed per-output through certificates from stage 1, in aggregate through the
   conformance corpus.
3. The BLAKE3 milestone (`DESIGN.md` §14): the C2SP specification at the specification
   layer, the AArch64 semantics for one compression's instructions, one generated kernel,
   its correctness certificate checked by the small checker, and the hash of the emitted
   bytes — reproducing what blake3-servil proves with Lean, Aeneas, Z3, a Python executor,
   and Isla, with one checker and every seam either inside it or printed on the map.
4. Ode hosting itself: the checker and emitter re-implemented as Ode definitions, proved
   against their specifications, with stage 1's checkers verifying the certificates. R1
   then rests on the bootstrap checker and the re-implementation's read — a few thousand
   lines, twice written — and on nothing else.

## 12. Open decisions

These are open, stated here so their absence is a decision rather than an oversight. Each
has the criterion that will close it.

1. **Computation inside proofs.** How decision procedures (normalizers, solvers) get their
   power inside the logic: reflection verified once, or a certificate per decision.
   *Criterion:* whichever keeps the checker inside its size and cost bounds on the
   milestone's certificates.
2. **The hash for proofs of execution.** BLAKE3 addresses definitions at rest; succinct
   execution proofs prefer field-friendly hashes. *Criterion:* one hash serves both, or
   the execution layer names its own and the binding between the two is itself a
   certificate.
3. **Memory management above the machine layer.** Regions per vat, garbage collection,
   or capability-confined manual memory with proofs. *Criterion:* the milestone's glue
   code, measured; kernels already live without this choice.
4. **The next logical fragment.** The kernel covers equations and structural
   induction, with sorts checked directly. *Criterion:* extend it for a specific
   refinement obligation, with semantics and a soundness argument. Completeness
   results for matching logic do not establish completeness of this different calculus.
5. **Which standard properties come first.** The library of §5 starts with the properties
   the milestone needs — functional correctness, constant-time, own-buffers — and grows by
   public argument. *Criterion:* a property joins when two independent projects need the
   same meaning.
