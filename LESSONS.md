# Lessons

What the work has taught, in the order it was learned. Each lesson ends with
what it asks of Ode. [DESIGN.md](DESIGN.md) is where the lessons are applied.

# Part 1: from verifying BLAKE3-Servil with general tools (October 2026)

That work proved the following, from C2SP's specification (in Lean) down to
the AArch64 machine code:

- the assembly kernels, with Z3, through an executor of our own;
- the safe-Rust tree and Hasher logic, in Lean via Aeneas;
- whole compiled calls, symbolically at fixed lengths.


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

Each hand transcription of the standard joined the reliance set:
`whole.py`'s 40 lines of tree rules, an earlier Python compression
function. Both left the reliance set when Lean computed the artifact from
the proved definition:

- the compression as a term graph (`compress.json`);
- the hash as a schedule of compressions (`schedules.json`), with a
  theorem, `run_eq`, that performing the schedule is the specification's
  output.

What remains relied upon is a printer and a reader of a few dozen lines, checked
together against the specification's own sample outputs.

*For Ode:* generators emit data structures together with their theorems.
The relied-upon surface is the format's reader, small and stated.

## 3. Every verifier needs a check that it can fail

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
verifiers' records: which objects, which obligations, which tool hashes.
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

*For Ode:* normal forms and substitution are part of the verifier's design,
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

## 7. Seams between tools are where reliance hides

Z3 proved the machine code, and Lean proved the algorithms and the
specification. The joints were:

- a schedule printer;
- a JSON reader;
- byte-identity checks;
- process-image assumptions (POSIX contracts for `malloc` and pthread
  keys).

Every one was a place an error could pass unseen, and naming each one in
the documentation was what made the guarantee explainable.

*For Ode:* one small verifying core with every other
tool as a producer outside the reliance set. Until then, list every seam
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
documentation says beside the count (322 of 325, 19 of 23). Readers can assess
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

# Part 2: from building a verifier of binaries (November 2026)

The work moved from general tools to a verifier made for the purpose: it
reads a binary's bytes, runs them on symbols, and compares the result with
a declarative specification (`kcheck/`).

## 12. A proof about a build's bytes dies at the next build; a proof written by hand falls behind

- **Rebuilds.** Machine-code theorems are about one build's bytes. At a
  lower optimization level 32% of the core crate's instructions stayed the
  same; across a minor compiler release, about 36%; with whole-program
  optimization, none.
- **Hand proofs.** Whole-hash theorems in Lean over a machine model took
  days a function and rested on about 2,500 solver axioms that an
  independent Lean verifier refuses. Proofs about source translated from
  Rust had been removed in October for slowing every change.

*For Ode:* ship fixed bytes. Write code to be proved; have the compiler
write the proof with the code. A verifier that re-runs instructions
answers in seconds, so a changed program is verified again.

## 13. A verifier's shortcuts are where false things get shown

One day's reading of the verifier as an attacker (November 17) found six
faults, each "shown, of something false". Each had one shape: something
became a fact because the implementation represented it that way.

- The stack pointer could be set to an argument's address, and a push was
  still taken to go to the function's own frame.
- The decoder wrote "the address of the file's data" as the same row as a
  number moved into a register, and the model took such a number for the
  address.
- Stack cells below the stack pointer were remembered across a call.
- Every register a call may change was one unknown, so two of them were
  equal.
- A layout in the proof could have fields that overlap or a bound no
  number meets; a callee whose contract promised the impossible deleted
  its caller's path.
- A sequence was named by the shape of its first value.

A copy of the shipped hash with one branch added passed verification
against the reader's own specification, and on a processor gave a wrong
digest for a message of one byte. It is kept (`kcheck/backdoor.o`).

*For Ode:* nothing becomes a fact because a clever part represents it so.
Every fact follows from a small explicit rule whose soundness is
established (DESIGN.md, section 7).

## 14. Audits by single changes are blind to faults that need several

The sweep of every single-bit change of every verified function ran clean
(355,704 changes, 18,278 accepted, each accepted one run as the
specification on a processor, none without a verdict) on a tree that
still held two of the six faults. Each fault needed several instructions,
a layout, a contract or a specification changed together.

*For Ode:* read as the attacker: of each instruction and each part of the
model, what does the verifier take to be so that the processor, the linker
or the arithmetic does not? Keep every attack found as a test with
evidence from a processor. Run the sweeps as background soaks.

## 15. Nothing in a proof is to be relied on without checking, and neither is a line printed from it

- A line told the reader "its definitions come to an end" by counting
  lemmas; a lemma that required the impossible was shown, of nothing, and
  made the line say it.
- A lemma's stated kind was taken as said where it ensured nothing.
- A proof that left a function out got exit status 0.

*For Ode:* an annotation creates an obligation; facts come only from
what the verifier has shown. Whatever
is printed to the reader is shown from the contract inward. Of every line
ask: could a maker's proof make this say something false?

## 16. A gate must be short enough to run every time

- The whole audit takes three and a half to four hours. A rule that
  nothing merges without it delayed the work and caught none of the
  faults above.
- The gate (`kcheck/gate.py`) takes under three minutes on 64 threads and
  fails if the kept bad binary is accepted.
- Seven steps of a five-hour audit failed in a tool of the audit's own
  that had never run on that machine. An audit's "judged on nothing" was
  read as "harmless" and hid a fault.

*For Ode:* gate every merge with what takes minutes, and time each step
before adding it. Try an audit's tools small, on its machine, first.
Change nothing a sweep covers while it runs.

## 17. A contract can be true and worth nothing

- `ensures decode(out) == input` is true of an encoder that always answers
  NO. The contract must say when NO is ruled out.
- A line of a contract whose removal changes nothing was promising
  nothing.
- A contract whose `requires` no call can meet is true of every binary.

*For Ode:* test each line of a public contract by leaving it out, and each
contract by exhibiting a call that meets it. Read a contract for what it
leaves unpromised.

## 18. Bending a specification toward the code costs every reader

The LZ4 specification first carried a capacity and a margin that only the
decoder's loop needed. The plain specification, with four lemmas carried in
the proof, verifies the same binary; a prover finds those lemmas from the
specification alone in about two seconds.

*For Ode:* the reader's text says what the thing is. What the code needs
beyond it is a lemma, shown by the verifier and read by nobody.

## 19. The file is part of what is verified

- A file held two functions of one name, the verified one local and
  another global. The verifier found the first by name; a linker gave
  callers the second.
- Tables that a file's header points at could lie outside the file.

*For Ode:* a file is read in one shape. Every name it gives a linker is
verified, and every table it points at lies within it.

## 20. Running and paths are the load; arithmetic is small

Counted over the verified functions: a shown arithmetic fact uses three
or four of about thirty facts in play, and a function's arithmetic proofs
come to 0.1 to 6 kB compressed. Proofs that write out every step of
running were estimated in megabytes and set aside.

*For Ode:* the verifier replays instructions and opens definitions
itself. A proof carries what would otherwise be searched for: places,
lemmas, the arithmetic's derivations.

## 21. "Checker" hides the question that matters

One word for finding a proof and for deciding whether a proof is one
blurred which code a reader relies on.

*For Ode:* the **prover** finds or writes a proof and is relied on for
nothing. The **verifier** decides, and is what the reader relies on.

*Ode stands for Oh, Don't Exaggerate.*
