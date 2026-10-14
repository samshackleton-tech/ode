# Lessons from verifying blake3-servil

What proving the servil BLAKE3 fork correct taught us (October 2026),
written for the design of Ode. That work proved the following, from C2SP's
specification (in Lean) down to the AArch64 machine code:

- the assembly kernels, with Z3, through an executor of our own;
- the safe-Rust tree and Hasher logic, in Lean via Aeneas;
- whole compiled calls, symbolically at fixed lengths.

Each lesson ends with what it suggests for Ode.

## 1. Name the proof's object exactly

A proof is about one program, and that program has more coordinates than
its source:

- **The build.** The kernels were proved on a build without std, while
  users run the default build, whose paths differ (thread-local scratch, a
  feature cache, a timer).
- **The compiler.** Rust 1.99 emits `ccmn` where 1.98 did not, so CI
  and the VM were proving different programs until the verify crate pinned
  its compiler.
- **The process state.** A rebase renumbered `Platform`'s
  discriminants, and a literal `1` in two tools silently changed from
  "SME2 absent" to "Portable".

*For Ode:* an obligation's subject is a content address over everything
that shapes the machine code: source, compiler, flags, and initial state.
Names stand in for magic numbers wherever a value crosses a tool boundary.

## 2. Generate from the specification; never transcribe it

Each hand transcription of the standard joined the trusted base:
`whole.py`'s 40 lines of tree rules, an earlier Python compression
function. Both left the trusted base when Lean computed the artifact from
the proved definition:

- the compression as a term graph (`compress.json`);
- the hash as a schedule of compressions (`schedules.json`), with a
  theorem, `run_eq`, that performing the schedule is the specification's
  output.

What stays trusted is a printer and a reader of a few dozen lines, checked
together against the specification's own sample outputs.

*For Ode:* generators emit data structures together with their theorems.
The trusted surface is the format's reader, small and stated.

## 3. Every checker needs a check that it can fail

These planted errors kept the proofs honest:

- mutants (a rotation off by one, the root flag dropped, an IV bit
  flipped), each of which the proofs must reject;
- wrong instruction models, which Isla must reject;
- a planted `sorry`, which must fail the Lean build;
- random-state runs of every instruction form on the real CPU.

That CPU cross-check found a real model bug, an addition's carry when an
operand is 0. A mutant once ran on the wrong path (Portable instead of
NEON) and still "passed", which shows mutants must be aimed at the code
under test.

*For Ode:* every verifier ships with its own negative tests, and they run
with it. A check that has never failed is unproven.

## 4. Claims drift from proofs unless they are computed

Our documentation overstated the work in three ways:

- "every assembly kernel is proved", while one 5,180-line kernel had no
  proof;
- "306 lengths", which counted two platforms' 153 lengths twice;
- counts of instruction forms that went stale after each tool change.

Each was a sentence typed by hand beside a proof that said otherwise.

*For Ode:* every claim about what is proved is generated from the
checkers' records: which objects, which obligations, which tool hashes.
A claim with no record behind it cannot be written. A map from each piece
of code to its proof status, made from the same records, shows the gaps
(issue #24 did this by hand, and found the unproved kernel).

## 5. Representation decides whether a solver answers

- **The multiplies.** Isla's traces gave Z3 its definitions as equations,
  and `mul` (64 bits of a 128-bit product) ran for hours. With the
  definitions substituted, Z3's simplifier settled each form in seconds.
  The first fix, substituting at every step, made other forms slower,
  because its cost grew quadratically with the trace.
- **The IV.** Whole-call results failed to match because the constant IV
  folded differently on the two sides; a normalizer that folds constants
  in sums and xors fixed every length.

*For Ode:* normal forms and substitution are part of the checker's design,
each with a measured cost. Keep one canonical form per term class.

## 6. Compose with contracts, guarded by identity

Whole-call proofs stay tractable when each kernel call is replaced by
the statement its own proof established. Two guards keep that sound:

- the library's bytes for the kernel must equal the bytes that were
  proved;
- the call's counts must lie inside a proof that always runs. A group
  count of 1 to 2^40 is covered by an induction over the loop; an
  enumeration up to 8 covered only what it listed.

Inductions over loop counts replaced hours of enumerated cases, and
reached further.

*For Ode:* a contract is usable exactly where a live proof covers it, and
the system checks this mechanically, with no stored claim of proof.

## 7. Seams between tools are where trust hides

Z3 proved the machine code, and Lean proved the algorithms and the
specification. The joints were:

- a schedule printer;
- a JSON reader;
- byte-identity checks;
- process-image assumptions (POSIX contracts for `malloc` and pthread
  keys).

Every one was a place an error could pass unseen, and naming each one in
the documentation was what made the guarantee explainable.

*For Ode:* one checker kernel (the μ-logic candidate) with every other
tool as an untrusted producer of certificates. Until then, list every seam
in the assurance map.

## 8. Resources are part of the proof design

- **Hosted CI.** GitHub's runner (16 GB, 6 hours a job) could hold neither
  the whole-call proofs nor the SME2 inductions. Splitting into 14 jobs
  and sizing workers by memory added machinery that a 98 GiB VM never
  needed.
- **The forms record.** Records keyed by the hash of every tool were
  sound and simple, but any tool edit invalidated hours of proofs.
- **Editing under a run.** Worker processes import tools from disk, so
  editing a tool during a run changed the code mid-run.

*For Ode:* proof jobs declare their memory and time. Caches key on exactly
the inputs a result depends on, the producer's own code included. A run
pins its tools and reads none from a live working tree.

## 9. State tool limits plainly, in the place readers look

Isla cannot run `addv`, `cnt`, or one form of `tbl`, and four ZA moves
exhaust its memory. Those forms stay checked against the CPU, which the
documentation says beside the count (322 of 325, 19 of 23). Readers trust
a count that shows its gaps.

*For Ode:* "unproved, and why" is a first-class status in the assurance
map, beside "proved".

## 10. Lean, practically

- `congr` and `rfl` near a large definition (the compression function)
  ran out of heartbeats. Rewriting the structure's fields one by one
  (`Node.mk.injEq`, then each field) finished in seconds.
- Stating each subtree's invariant once, over the specification's own
  recursion, proved the whole schedule in about 370 lines with Lean's
  three standard axioms only.

*For Ode:* proof producers benefit from a library of rewriting lemmas
for the specification's own structures, written once and reused.

## 11. Working beside other agents

A second agent landed six PRs while our branch was in flight; the rebase
was clean in text and wrong in meaning (lesson 1). What helped:

- notices on a shared issue before and after each long run;
- rehearsing merges in a separate worktree;
- rerunning the whole chain after any merge.

*For Ode:* a merge invalidates every proof whose subject's address
changed, and the system reruns them on its own.
