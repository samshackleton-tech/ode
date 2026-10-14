# Ode: an initial design

Ode is a tool for building software whose correctness is proved, whose speed matches the best
hand-tuned code, and whose authority is bounded by construction, written by loosely-coordinated
teams of many AI agents directed by a few human engineers. This document states what Ode is for,
what it leaves out, and the design that follows. It is a first draft, from the experience of
blake3-servil (a BLAKE3 implementation proved correct on AArch64 with Lean, Aeneas, Z3, and Isla),
and from the work of Mark S. Miller (E, Endo), Daira Hopwood (Noether), François-René Rideau
(*Lambda: The Ultimate Object*), Grigore Roşu and Xiaohong Chen (K, matching logic), the Unison
authors, Filip Pizlo (Fil-C), the Lurk authors, and Nadim Kobeissi (*Nobody Will Read the Lean*).

## 1. Who Ode is for

Ode has one target user: a swarm of loosely-cooperating teams of AI agents (Claude Opus 5.5 and
peers and successors) and a few experienced human engineers, at their best, with the right context
loaded and attention on the right things.

- **The agents** read, write, prove, measure, and review code. Their scarcest resource is context;
  their best work comes from fast, exact feedback; their typical mistakes are slips of scope (an
  operation that touches more than intended), slips of claim (stating more than was checked), and
  lost commitments across sessions.
- **The humans** decide what should be true and which trade-offs are acceptable, and notice when a
  specification is wrong. In blake3-servil the human director read specifications, decisions,
  measurements, and the assurance document, and essentially never the source code.

So Ode keeps two kinds of legibility: code legible to agents, and meaning legible to humans.
The checker settles whether a proof establishes its statement; people settle whether the
statement says what they mean (Kobeissi). Specifications therefore stay short enough for their
owners to read in full, and generated proofs carry no reading duty at all.

## 2. What Ode leaves out

Excluding scope is how Ode does its main job well.

- Surface syntax designed for human authors: sugar, alternative notations, formatting choices. The
  source is a structured graph; humans see projections of it.
- Beginner ergonomics, gradual learning curves, tutorials.
- Compatibility with existing languages, binaries, or calling conventions, beyond a confined
  foreign-call boundary.
- Verification of code written elsewhere: Ode code is written in Ode. Code that arrives from outside
  runs confined (§7), with memory and authority safety and nothing more.
- More than one way to say one thing.
- Undefined behaviour, implicit coercions, overloading, ambient authority, global mutable state,
  reflection that breaks encapsulation.

## 3. Principles

Ode inherits the team's principles (`AGENTS.md`), which govern this document too:

- **Every piece earns its place.** One mechanism wherever it serves.
- **Design by contract, fail-stop.** Contracts are expansive and simple; a broken one stops the
  program with a clear message.
- **Crash-only.** Everything lasts until its process ends; nothing is written to shut down or
  reclaim.
- **Integers first.** Measurements and statistics are integers or exact fixed point.
- **Wall time and cycles, a run's mean, compared over pairs of runs.**

And three of its own:

- **Design for the team at its best, and make its worst inexpressible.**  An agent at its best needs
  power and fast truth; the tool has no way to express the slips it would make at its worst.
- **Producers are untrusted; one small checker is trusted.** Every producer of code or proof (a
  person, an AI, a generator, a compiler, a solver, a prover of execution) is outside the reliance
  set: what it emits is accepted only with a certificate the checker accepts.
- **One obligation, discharged at whichever stage knows enough.** A specification is stated once; a
  proof, an audit, a guard, an assertion, a self-test, or a monitor discharges it, and the tool
  records which.

## 4. Definitions, hashes, and names

Everything in Ode is a **definition**: a specification, a function, a kernel, a generator, a proof,
a measurement, a decision. Each definition is immutable and identified by the BLAKE3 hash of its
canonical form, with its dependencies referred to by their hashes (as in Unison). A hash fixes
exactly what a definition is and everything it depends on.

**Names are pet names** (as in Miller's petname systems and Endo): each agent and each human holds
its own local names for hashes and for capabilities. A shared project is a directory of names that
its members can repoint, with review. Renaming is metadata; two agents adding definitions never
conflict; an update repoints a name, and the tool lists exactly the definitions and certificates
whose hashes depend on the old one.

**Definitions carry no authority.** A hash says what a definition computes, never what it may touch,
so definitions are safe to share, cache, and load anywhere. Authority exists only as capabilities
(§7).

## 5. Layers and refinement

An Ode program is a tower of layers (Rideau's hyper- and hypo-systems): each layer is a computing
system, and each step down is an implementation with a proved correspondence to the system above it.

- **The specification layer** is definite (Hopwood's Noether-0): pure, strict functions whose every
  computation succeeds deterministically or fails in finite time, and their equations.  A standard
  such as C2SP's BLAKE3 is written here, executable, so the same text is the reference
  implementation, the generator of test vectors, and the statement of every theorem about it.
  The specification is the specification of record: its owners write it, and prose, test vectors,
  and implementations are checked against it.
- **The generator layer** adds staging (MetaML brackets and escapes) and generative macros. A staged
  program means exactly its unstaged elision.  Generators produce lower layers: blake3-servil's
  fastest kernels were generated (`tools/gen_neon_hybrid.py`) and their outputs proved, and Ode
  makes that the normal way to write performance-critical code.
- **The machine layer** is typed, structured assembly for one ISA: straight-line code, loops over
  counts the type system knows, explicit registers, lanes, predicates, and matrix tiles, and exactly
  the vendor's formally defined instructions (Arm's ASL through Sail, for AArch64). It has no
  computed jumps, no self-modifying code, and no memory beyond the capabilities passed in. Speed
  comes from choosing the instructions, explicitly.
- **The binary** is emitted from the machine layer by a deterministic emitter, so what is proved is
  the bytes that run, and a hash of a machine-layer definition fixes its bytes.

Glue (dispatch, tree walks, buffering) is specification-layer code compiled by a certifying
compiler: the compiler is a producer, and each output carries its refinement certificate.

**Extension.** Following Rideau, a specification is extended modularly: a new kernel for a platform
is a mixin on the platform's specification (`super` is the choice so far, `self` the final
dispatch), and the running library is the fixed point. Each extension carries its contract, so
agents extend behind stable interfaces.

## 6. One logic, many producers

**The trusted base is one small checker** for proof certificates, in a logic with a minimal rule set
and least fixed points. Matching μ-logic is the leading candidate: patterns denote sets of elements,
its Hilbert system has a handful of rules, its certificates are checked in a few hundred lines
(Metamath), Lean's proof objects translate into it, and equality, sorts, functions, constructors,
separation, reachability, and type systems are theories inside it. Chen and Roşu (2026) prove its
fixpoint-free basic fragment, in one-sorted form, globally complete and the definedness extension
conservative there, so theories added as libraries keep each other's meanings; with fixpoints it
is, like every logic strong enough for induction, incomplete, which costs nothing for the theorems
we prove.

**Operational semantics is the definitional base** (as in K): each layer's language, including each
ISA, is defined by rewrite rules, and correctness between layers is reachability or simulation,
proved in the same logic. Symbolic execution is proof search; loop invariants are circularities;
constant-time is a relational (two-run) reachability property.

**Producers above the checker are untrusted and interchangeable:** symbolic executors, SMT solvers,
normalizers (verified once, or emitting certificates), tactic engines, AI agents. Three kinds of
certificate:

- **correctness**: a proof that a definition meets its specification;
- **execution**: a succinct proof that a computation ran and gave its result (as in Lurk), so a run
  by an untrusted agent or machine is checked without being repeated; and since the checker is
  small, a succinct proof that the checker accepted a certificate can stand for the certificate
  itself;
- **attestation**: an auditor's signed statement about a definition, carrying its recipe for
  rechecking.

A certificate is a definition like any other, named by its hash, and states exactly which hashes it
is about. It is checked once and recognized by anyone thereafter.

## 7. Authority

**Memory safety and capability safety hold for all Ode code, proved or not.** A reference is
unforgeable; capabilities arise only from creation and are acquired only by being passed (Miller:
only connectivity begets connectivity). There is no ambient authority: no global names for files,
networks, clocks, or other definitions' powers. Code loaded from outside runs under a loader that
gives any input a safe meaning (Fil-C's "garbage in, memory safety out", lifted to capabilities):
whatever it is, it can act only through the capabilities it is handed. In proved code, the checks a
proof shows unnecessary are erased; elsewhere they stay, in software or in hardware capabilities
(CHERI).

**Invoking anything means holding a capability to it**: calling a function value, sending a message,
reading a buffer, using a device.  Kernels receive exactly their buffers as capabilities, which is
the "reads and writes only its own buffers" property by construction.

## 8. Obligations and assurance

Each specification generates **obligations**, and each obligation is discharged at one stage,
recorded with the hash of what discharged it:

| Stage | Discharge |
|---|---|
| before running | a proof certificate |
| on loading code | an auditor's attestation |
| at a call boundary | a guard, which coerces or ejects, naming the party at fault (E's guards; Racket's contracts with blame) |
| inside a computation | a fail-stop assertion |
| at startup | a self-test against the actual machine |
| afterwards | a monitor or sampler |

A proof erases the corresponding guard; a guard on a value known early is already a proof. The
**assurance map** (what is proved, what is checked when, and what each claim rests on) is generated
from these records for every hash, and is the human-facing account of correctness.

**Property definitions come from a small, standard, versioned library** (Kobeissi): each property
an obligation can claim — constant-time, reads-and-writes-only-its-own-buffers, forward secrecy in
a protocol — has one public definition, formalized once and reviewed by the whole community, and
claims name the definition and its version, the way a protocol names AES-256-GCM. A checker record
is the only source of a claim: an admitted or assumed proof appears in the assurance map as
unproved, with its reason. When a definition's new version appears, the map lists every claim
resting on the old one, and rechecking those claims is mechanical.

## 9. Working together

- **Immutable definitions, names as pointers, contracts as interfaces.**  An agent works on a
  definition knowing only its dependencies' contracts, so the context it loads is the definition
  plus those contracts.
- **Coordination is data in the store**: claims (who is working on which hash), promises between
  agents, reservations of shared resources (a measurement machine kept idle), and their release.
- **Decisions are definitions** attached to what they decide: who decided, when, why, and with what
  evidence. The reason for a design travels with it.
- **Promotion repoints a shared name**, with the evidence the project's policy requires
  (certificates, measurements, reviews), recorded with the name's new hash.

## 10. Feedback

- **Checking is incremental, parallel, and cached by hash**: a change rechecks exactly the
  obligations whose hashes it reaches.
- **Errors are structured data**: the failing obligation, its context, and a counterexample where
  one exists.
- **Every run's duration is recorded per hash**, so the tool estimates a check's time from its
  history.

## 11. Measurement

Speed is a property of a hash on a machine. Measurements are definitions keyed by (code hash,
benchmark hash, machine, conditions); each records wall time and cycles per core kind, as integers;
comparisons take pairs of runs in alternating order and judge by their ratios. "Has this exact code
been measured on the Mac?" is a lookup, and a regression report is computed.

## 12. Surfaces for humans

- **Specifications**, projected as precise mathematics in plain notation.
- **The assurance map** (§8).
- **Decision prompts**: when an agent meets a real trade-off, the tool presents the options with
  their numbers and records the decision.
- **Measurement reports**, computed from §11.
- **Projections** of any definition, proof step, or counterexample, for the exceptional
  investigation.

## 13. Open questions

1. **The logic**: matching μ-logic as the certificate logic, and how computation inside proofs
   (Lean's strength) is provided: reflection verified once, or certificates for decision procedures.
2. **ISA semantics**: Arm's ASL through Sail for AArch64 (blake3-servil's probe proved BLAKE3's G
   against it); which subset; the questions it raised (memory as plain memory, decoding, UNKNOWN
   values).
3. **The hash for proofs of execution**: BLAKE3 addresses definitions at rest; succinct proofs
   prefer field-friendly hashes (Poseidon). Whether one hash serves both.
4. **Memory management**: regions per vat, garbage collection, or capability-confined manual memory
   with proofs.
5. **Bootstrapping**: the first checker, emitter, and store, written in existing tools, and how Ode
   comes to host itself.
6. **The canonical form** agents read and write: its text serialization, and how projections for
   humans are produced.

## 14. A first milestone

BLAKE3 again, in Ode: the C2SP specification in the specification layer; AArch64's semantics for the
instructions one compression needs; one compression kernel in the machine layer, produced by a
generator; a certificate that the kernel computes the specification's compression, checked by the
small checker; and the hash of the emitted bytes. This reproduces, with one checker and no seams,
what blake3-servil proves today with Lean, Aeneas, Z3, a Python executor, and Isla.

## References

- Mark S. Miller, *Robust Composition: Towards a Unified Approach to Access Control and Concurrency
  Control*, PhD thesis, Johns Hopkins, 2006.
- Endo: <https://github.com/endojs/endo> (HardenedJS, CapTP, OCapN, the Endo daemon's hosts, guests,
  pet names, and mail).
- Daira Hopwood, *Noether: Symmetry in Programming Language Design*, Strange Loop 2013.
- François-René Rideau, *Lambda: The Ultimate Object*, 2026.
- Xiaohong Chen and Grigore Roşu, *Completeness and Incompleteness of Basic Matching Logic*,
  arXiv:2608.13306, 2026; the K framework.
- Unison, *The Big Idea*: <https://www.unison-lang.org/docs/the-big-idea/>.
- Filip Pizlo, Fil-C: InvisiCaps and GIMSO, <https://fil-c.org/>.
- Nada Amin et al., *Lurk: Lambda, the Ultimate Recursive Knowledge*, Journal of Functional
  Programming 36, 2026.
- Nadim Kobeissi, *Nobody Will Read the Lean: A Case for High-Level Cryptographic Languages*,
  Cryptology ePrint Archive, Paper 2026/2441, 2026.
- blake3-servil's `QUALITY.md`: what a proved, fast BLAKE3 needed, and where its seams were.
