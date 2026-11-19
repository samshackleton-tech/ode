# Ode: design

This page states what Ode is for and how it is built to get there. It holds commitments, including work
that is still ahead; section 13 says what exists today. It unifies three earlier bodies of design: Ode 0.1
(this repository's tag `v0.1.0`), the Lean experiments of November 11 to 14, 2026, and the verifier of
binaries built since November 14 (section 16 says where each lives).

Other pages: [README.md](README.md) (what is here and how to run it), [kcheck/VERIFY.md](kcheck/VERIFY.md)
(the page for a person verifying a binary), [kcheck/LANGUAGE.md](kcheck/LANGUAGE.md) (the specification and
contract language), [NAMES.md](NAMES.md) (names and identities), [LESSONS.md](LESSONS.md) (what the work
has taught), [kcheck/README.md](kcheck/README.md) (the dated record of evidence).

## 1. The goal

**Bob can establish, with his own tools, that a substantial, useful, fast native binary does what he
requires of it, while relying only on a short list of named things (section 2).**

The first use case, and the one everything is judged by today: Bob the auditor scrutinizes the security
of some code by reading its contract and running his verifier, to which he gives the binary, the proof and
the contract. He leaves the implementation unread. Other uses (maintaining the code, building on it) are
separate use cases, taken up after this one.

Two requirements are hard:

1. **Soundness.** If the verifier says "shown", the binary meets the contract. "Shown" for something false
   defeats the project.
2. **Verifiable soundness.** Bob can come to justified confidence in the verifier while believing only a
   small part of it (section 7).

Four more are goals, pursued in this order, each yielding to the two above:

3. little for Bob to read and rely on;
4. native code as fast as the best written for the machine;
5. programs with proofs that are practical to produce at scale;
6. verification that is fast, local, and needs no network.

Of a true statement the verifier should seldom say "not shown"; of a false one it should be able to say
"false, and here is an input"; and it should answer fast. These three are goals as well.

**The test of the design** is a program people already depend on. The current target is
BLAKE3-Servil's core crate (`blake3-servil-core`: the hash on one thread), written in Ode, as fast or
nearly as fast as its 0.10 release, verifiable by its user. BLAKE3 is the first example;
Ode is a project of its own. A decompressor of the zstd family and a verifier shown to meet a verifier's
contract are the examples after it.

**What Ode leaves out, on purpose.** Narrow scope is how Ode can go further than general tools:

- programs that already exist: code is written anew, in Ode, to be fast and to be provable;
- arbitrary mathematics and arbitrary computation in specifications and proofs;
- arbitrary assembly: the coder writes within the instruction forms Ode gives an account of;
- proofs for every program the language can express: the coder writes code to be provable, as to be fast;
- comfort for unaided human coders: surface sugar, tutorials, names that are easy to remember;
- existing languages, and existing proof assistants as a requirement (Lean may help; nobody must run it).

**Who takes part.** Each may be a person, an AI agent, or a team of both.

| | what they do | what they are relied on for |
|---|---|---|
| the coder | writes Ode source: the code, its machine decisions, the structure of its proof | nothing |
| the maker | ships a binary with its proof and specification; may be the coder; may be an attacker | nothing |
| Bob | decides what he requires, chooses a contract that says it, runs his verifier | his own judgment of what he wants |
| Bob's verifier | a deterministic program: decides whether a proof shows that these bytes meet this contract | R1 and R2 of section 2 |
| Carol | maintains the code; sees what Bob has no use for (inner names, the terms of a refusal) | nothing |

The setting is hostile. A maker may be an attacker who looks like any other maker; keys are stolen;
auditors compare notes with strangers. Every design question about what is sent to Bob is asked twice: how
does a good maker use this, and how does an evil one?

## 2. What Bob relies on

We say *rely*, after Mark S. Miller: reliance names a property of a mechanism that a conclusion rests on, and
points at what breaks if the property fails. We do not use the word "trust". In ordinary life it names
something good; in security writing a "trusted" part is one that can hurt you; and it draws attention to
the nature of the part and away from the question that matters: relied on *for what*? Two sentences take
its place, and they state one fact from two sides. (Miller defines "relies upon" as dependence that a
specification allows, on top of the plain fact "is vulnerable to"; the two uses below follow him.)

- **"A relies on X for P"** is for what the design is built on by intention: P is something X is there
  to deliver, and the reader is asked to examine X or to have a reason for believing P. The table below is
  of this kind. It is never written without the "for what".
- **"A is vulnerable to X"** is for what is left open: X is in a position to do harm and nothing checks
  it, as with a step that no proof covers yet, or a party who may be an attacker. It is written with the
  harm, and with what would close it where that is known.

"Relies on" used for an exposure nobody chose would make a risk look like a decision. "Vulnerable to" used
for the small core that Bob is asked to examine would hide the open exposures among alarms. A negative
takes the first form: "the verdict does not rely on the prover" claims exactly what the verifier's
checking gives, while "Bob is not vulnerable to the prover" would claim more than is so, since a prover
can still withhold a proof.

Everything an actor relies on for a conclusion is that actor's **reliance set** (Miller, *Robust
Composition*, 2006, section 5.1: "We will refer to the set of all elements on which P relies as P's
reliance set"). Two actors can have different reliance sets. The maker relies on the prover for getting a
proof at all; Bob relies on the prover for nothing. Two Bobs can differ as well: section 7 gives each Bob
a choice of what to rely on for the verifier's soundness. What lies in the reliance sets of all of them
is, in Miller's words, a central point of failure, and is what most needs to be small and checkable. The
older term "trusted computing base" is used for a reliance set, for a platform, and for that
intersection, and does not say which.

The table below lists the properties every Bob relies on. For R1 the things that deliver the property
differ from Bob to Bob (section 7), and their reliance sets differ with them. Bob's conclusion "this
binary does what I require" rests on the entries below and on nothing else. The compiler, the assembler, the linker, the prover, the coder and
the maker are absent from the list: whatever they produce is accepted only where the verifier accepts it.

| | Bob relies on | why it cannot be removed | what keeps it small and honest |
|---|---|---|---|
| R1 | the verifier decides as its rules say | every verification ends at some program that is run | a small core with explicit rules and a soundness argument; several independent ways to justify it (section 7) |
| R2 | the readers read the bytes they are given: the binary's file format, the contract's text | a proof is about bytes, and something must connect bytes to meaning | part of the core; one shape of file accepted; every name the file gives a linker must be verified |
| R3 | the contract says what Bob requires | only Bob knows what he wants (section 3) | contracts short enough to read whole, in a language made for the reader; a closed world |
| R4 | the account of the machine matches the processors it names | a proof about machine code is a proof about a model of the machine | one authoritative account; each instruction form compared with real processors; accepted changes judged by a processor (sections 8, 11) |
| R5 | the physical machine runs its instruction set | no proof about code reaches physics | each promise names its exact scope: a contract's `trace` line speaks of instructions and addresses, and of nothing else |
| R6 | BLAKE3 is collision-resistant | things are named by the hash of their content (section 10) | one hash function everywhere, whole digests, compared by the tool |

Entry R1 is where the present prototype is furthest from the design: section 13.

## 3. Bob's intent and the contract his verifier decides

**Bob's intent** is what Bob wants of the software: his evolving view, including concerns he has yet to
think of and trade-offs he has yet to settle. It may be vague, incomplete, or at odds with itself, and it
may change. Nobody else knows it, and no tool can, until Bob makes up his mind. It is an input to the
process; there is no hidden formal contract behind it waiting to be recovered.

A **public contract** is a precise statement about a function in a binary: what the caller owes
(`requires`) and what the function then does (`ensures`, and the closed world of section 4). A **full
contract** is a public contract together with every definition it uses, directly or through others.
"Contract" always means the formal thing. A full contract is a candidate reading of part of Bob's intent.

Two questions stay apart:

- *Does this contract say what Bob wants?* Bob's judgment, made alone, with help, or by a policy he has
  chosen to delegate to.
- *Do these bytes meet this contract?* A question for a deterministic verifier, answered the same for
  everyone, with no judgment of the maker's or an assistant's in it.

The intended use is a conversation. Bob tries a candidate contract and asks: "if *this* is what I require,
does *that* library provide it?" His tools answer quickly and cheaply; the answer teaches him something;
he revises the candidate, or his intent. For example, Bob first cares only that a function hashes a
message correctly. An assistant raises timing. Bob decides whether the message is secret, and so whether
he requires that the instructions run and the addresses touched depend on the message's length alone. The
tools can show which libraries provide each choice. Which choice he ought to make is his.

What makes the answers quick and reliable is that they are verifications of evidence:

- the binary carries a proof of one public contract for each function. Two promises can be incomparable:
  one asks more of the caller and gives more (below 2^32 bytes, the trace depends on the length alone),
  another asks less and gives less, and neither can stand for the other. So a promise may carry its
  condition (`ensures X if C`), and the contract holds every promise its maker stands behind. Whatever
  she can prove is one contract, and Bob receives it;
- Bob says what he, as the caller, will guarantee, and his tool shows what the contract then promises
  him: a promise whose condition follows from his guarantees applies, and the others fall away. Where he
  drops a promise or adds a guarantee, the tool decides it from the two texts. Where his candidate takes
  reasoning (the same thing defined another way), it has a proof of its own.

Each answer is one of three, kept distinct: **shown**; **refuted**, with evidence such as an
input on which the binary breaks the contract; **not shown**. "Not shown" is silence about the program: no
proof was found or carried, and nothing follows about whether the binary fails. An answer about one
contract stays an answer about that contract when Bob changes his mind.

Finding a proof of an arbitrary new contract quickly is outside the promise: that is the prover's work,
and the coder's. Exploring contracts interactively and verifying implications between contracts are
design goals; the present tools verify one carried proof against one given contract.

## 4. The specification and contract language

What Bob reads is written in a language of its own, apart from the code language, smaller than it, and
made for the reader. [kcheck/LANGUAGE.md](kcheck/LANGUAGE.md) defines it. The rules that shape it:

- **The specification is declarative.** It says what a hash, a checksum, a format or an encoding *is*, by
  definitions given as equations, with no mutable state and no memory. It can be evaluated on numbers (the
  official test vectors are run this way, and a tester looks for refuting inputs this way), and a contract
  may also use it in a way that gives no algorithm, such as "decoding the output gives back the input".
- **A contract is a Hoare triple under a closed world.** `requires` says what the caller owes. Everything
  else is the function's promise: what it returns and writes, and that it reads and writes nothing more,
  comes to an end, keeps within a stated stack, preserves the registers its convention says, and lets its
  trace depend only on what the contract names. Silence is the stronger promise; a function that needs to
  do more must have the contract say so.
- **Memory holds bytes.** Byte order is said in one place, by the words `words` and `bytes_of`.
- **Failure is a value.** A specification says `fails REASON if C`, and the contract says what the
  function does then. A contract that is no way to compute must also say when the answer NO is ruled out,
  or an encoder that always says NO meets it.
- **Every line earns its place.** Each line of a public contract is tested by leaving it out; a line
  whose absence changes nothing is removed.
- **A name has one meaning.** A name is declared once; the language's own words cannot be redefined; a
  proof may declare no name the reader's text writes.

Two more rules are decided and ahead of the tools:

- **A contract must be able to hold.** A contract whose `requires` no call can meet is true of every
  binary. The reader is shown a call that meets it, or told that none was found.
- **One language page, named by its hash.** A full contract names the version of the language it is
  written in by the hash of that page, so a later change to the language cannot quietly change an old
  contract's meaning.

Bending a specification toward the code that implements it moves cost onto every reader. Where the code
needs a fact the plain specification leaves implicit, the fact is a **lemma**: a contract of a definition,
carried in the proof, shown by the verifier, and left unread by Bob.

## 5. The coder chooses the machine implementation

Most language design aims to take the coder's portable description and have a compiler find a fast
implementation of it. **Ode gives that aim up.** The coder states the machine decisions: which
instructions, which registers hold what, how vectors and their lanes are used, the order of instructions,
where every buffer lies and on what boundary, what is saved and where, how functions pass arguments to one
another. What Ode automates is **the proof that the chosen implementation meets the contract.** The
discoveries of programming-language research (types, ownership, refinement, certifying compilation) are
taken up for that purpose.

Consequences:

- **The compiler does what is written, or refuses.** It expands the coder's macros, resolves labels and
  distances, and writes the proof beside the code. It adds no instruction, moves none, and picks no
  register or layout as an optimization. Where a choice is left open, it stops and says so.
- **The coder can predict.** The same source for the same target gives the same bytes, and one function's
  bytes depend on that function's source alone. Both are tests.
- **Generators, macros and searching agents are welcome on the coder's side.** They may propose and
  measure thousands of candidates. The source that is accepted records the decisions, so that compiling
  it makes none afresh.
- **One kind of input.** Everything is Ode source. Its instruction layer is where a kernel's instructions
  are written one by one; hand-written assembly beside it is a reference for bytes and speed and is no
  second source.
- **Speed is carried across machines by people and agents, and assurance by the tools.** A specification,
  a contract, a proof method and a template serve every target. A fast implementation for another
  instruction set is another piece of chosen code.
- **The chosen code's speed is still measured.** Writing the instructions down fixes what runs; how fast
  it runs on a given machine is a measurement (section 11).

Memory and calls follow the same rule (decided in November 2026; partly built):

- **Memory's cost is what is touched**: cache lines, pages, and what is shared between threads. A size in
  bytes is no measure of it.
- **Nothing is allocated at run time.** The memory a call needs is set aside beforehand, stated exactly in
  the contract (the stack line), and shown.
- **The coder lays memory out, and the compiler does what is written or stops.** Proposed in detail and
  awaiting decision: buffers lie in the order written, each on the boundary written; `line` and `page` are
  the target's names for its sizes; the coder may state what a layout is for (two things on one line; two
  things on separate lines), and the compiler verifies the statement.
- **Calls between Ode functions need no fixed convention.** Where arguments are, what a callee may change,
  and whether it has a frame of its own are stated in the callee's contract and shown. The C convention
  stays at the boundary where C or Rust calls in.
- **Code the proof shows unreachable is removed.** So is a check that cannot fail; where a caller is
  unproved, the check belongs to a separate checked entry.

The nearest relatives are Jasmin (the programmer controls instruction selection and scheduling), Vale,
typed assembly language and proof-carrying code: section 15.

## 6. The coder supplies the proof's structure

The coder knows why the code is right. Ode has the coder say it where the decisions are made, and
carries it to the bytes. Three means, each taken from existing practice:

- **Types that speak of values**: a buffer of `64 * n` bytes; a register that holds `n - b`; a vector
  register that holds the specification's `h[b]`; a function's contract, which is its type; a place in a
  loop, which is the type of the machine's state there.
- **Ownership and permission for memory**: which ranges may be written, which only read, that two ranges
  share no byte.
- **Proof-only values**: quantities such as "the number of turns so far" that exist for the proof and
  cost nothing at run time.

For the sixteen-lane BLAKE3 loop the coder writes, at the loop's head: these registers are kept; this
one holds `n - b`; this one `64 * b`; these eight hold `h[b]`. That one annotation serves speed (the
chosen registers, the aligned scratch) and proof (the bounds, the invariant, the end of the loop).

Two rules bound this:

- **An annotation creates an obligation; facts come only from what the verifier has shown.** The verifier relies on
  nothing in a proof (inner contracts, layouts, lemmas, kinds, places) before it has shown it. It may use
  each of them only after showing it, and describing an impossible thing gives the verifier no value of that thing.
- **The final verdict is about the binary.** A proof about source says nothing of a compiler that emitted
  something else. A verifier of Ode *source* is wanted as the coder's tool, for exact messages early; the
  verifier of the binary stays Bob's.

Dependent types for the coder's side and the form of proof the verifier accepts are separate choices
(section 14).

## 7. What the verifier establishes, and why it can be believed

**The obligation.** If the verifier accepts a proof of a contract for some bytes, then every call that
meets the contract's `requires` satisfies the contract, under the stated account of the machine: the
result, the memory read and written, the registers preserved, termination, the stack, the processor
features needed, and the trace.

**The proof is relied on for nothing, and is carried in the binary.** The specification the maker used travels there too,
as a convenience: Bob verifies against his own copy, or reads the carried one first.

**The verifier's own contract.**

- It answers "shown" or "not shown", with a reason for every refusal. Malformed input, an unknown version
  and an unsupported form are refusals.
- It is deterministic and works offline: the same bytes give the same answer, with no network, clock or
  randomness.
- It works within stated limits of input size and work, and reaching a limit is a refusal.
- It only verifies. Guessing (where a loop's place is, which lemma helps, which facts add up) is the
  prover's work, and the prover is outside what Bob relies on.
- Whatever it prints to Bob rests on the contract inward. A line that rests on text from the proof is
  shown first. In Bob's mode it prints nothing the maker chose that Bob has no use for.
- It travels with tests it must fail: binaries and proofs that are wrong in known ways (section 11).

**The way to a verifier Bob can believe: shrink the core he relies on, and make that core provable.**
Today's verifier runs the binary on symbols with machinery that is clever and large. Each of the faults
found in it had one shape: something became a fact because the implementation represented it so (one name
for two unknowns; independent fields for bytes that overlap; a sequence named by the shape of its first
value; a number taken for an address). The rule against that shape:

> Nothing becomes a fact because a clever part of the implementation represents it that way. Every fact
> follows from a small, explicit rule whose soundness is established.

So the design separates three things:

1. **The account**: what a contract promises, what the machine does, what a specification's text means.
   Written once, in a form a reader and a proof can both use.
2. **The core**: a small verifier that accepts a proof only by explicit rules, each justified against the
   account. It may replay instructions and open definitions itself, so a proof stays small: it carries
   what would otherwise be searched for (places, lemmas, arithmetic derivations) and leaves out what is
   merely computed.
3. **The prover's abstractions**: regions of memory, summaries of loops and calls, knowledge of kernels.
   These stay as clever as they like, and they produce proofs for the core.

Assumptions and unknowns are scoped exactly: each register a call leaves is an unknown of its own; a fact
learned on a branch holds on that branch; an induction hypothesis is available only under the rule that
justifies it.

**The bottom is a disjunction.** No single foundation is asked of every Bob. The core is correct if any
one of these holds, and each Bob chooses:

1. he reads the core himself (it is small enough);
2. a second core, written apart, accepts the same proof;
3. the core is proved correct in a system he already relies on (Lean, HOL Light): an option for those
   who want it;
4. the core is written in Ode, specified in Ode's specification language, and shown by Ode's own verifier
   to meet that contract. Alone this is circular; with any one outside check it is strong.

Therefore the core is designed so that it *could* be written in Ode: small, plain data, no cleverness.
Bob himself need not read the account of the machine or the soundness argument. He needs a justified
route, of his choosing, from his question to his tool's answer.

**A first core exists (November 18, 2026): `proof-core/`.** It is a verifier in Lean 4 that decides by a
proof it is handed, with a theorem that Lean checks: whatever the proofs are, if the verifier says yes of
the functions of a statement, every one of them meets its contract on the machine the table describes
(`verify_all_sound`). The account it is about is 731 lines; the verifier's own 1,463 lines are under the
theorem and need not be read. It reads a first part of what the full verifier reads: instructions over the
general registers, the flags and memory; loops by places (several a function), by induction on a place's
number; a call, by the contract of a function the verifier has shown before, after showing what that
contract asks of a caller; a contract with runs of bytes that are only read, `returns` and `stack`; and
a run of bytes the function writes for its caller, with an `ensures` that says what list of the
specification those bytes are. Five
shipped functions are shown by it: `ode_common` from a proof of 646 bytes in 4 ms, the Adler-32 checksum
from one of 3 kB in 5 ms, the Adler-32 that reduces its sums once a block (two loops, shifts and masks)
from one of 19 kB in 40 ms, and the Adler-32 that takes four bytes a turn (the fast one, at 87% of the
usual C) from one of 26 kB in 80 ms, and the varint encoder, which writes up to ten bytes for its caller,
from one of 9 kB in 35 ms; and a function that calls the first, from 77 bytes more. The account's reading of the
specification language covers the whole of `kcheck/blake3.spec` (words, lists, records, sequences): worked out
by it, the specification gives the 105 official test vectors. One function of the hash is shown by it (November 19,
2026): the one-block kernel `blake3_servil_compress_in_place_avx512`, 76 instructions, from a proof of 189 bytes
in 17 ms. The verifier follows each 32-bit word of a vector register as a term over the words read at entry, and
at the return works the specification's `compress` out on the same terms; what the kernel's contract promises of
its trace is not in the account and is not shown there. This is the third way of the disjunction, begun. Reading
the file's bytes and the specification's text is outside the theorem, as are the link step, what a processor must
have (`needs`), and loops that write for the caller: `proof-core/README.md` says what a yes there rests on. Lean is the language of that
implementation and is asked of no reader: the proof is text that a verifier in any language can read.

## 8. The account of the machine

- **One authoritative account** of each instruction form Ode uses, from which every reading is taken. The
  decoder (bytes to instructions), the model (what an instruction does) and the proof rules are separate
  responsibilities, and no reading may erase a distinction another needs (the address of the file's data
  and a number that happens to equal it are different things).
- **The account is a table, not code** (`core/x86.tab`, since November 17, 2026). One row an instruction
  form: how an assembler writes it, how the decoded instruction is written, and its effect as a few
  statements over primitives (`D = add64(D, S); zf = unknown; cf = unknown`). A row states what the
  instruction does in general; `= unknown` leaves a part of the state unsaid, which the verifier may then
  not rely on. Three things read the same row: the verifier, which does the effect on symbols; the
  comparison with a processor, which does it on numbers; and an auditor. What the verifier can conclude on
  symbols is a partial rule for each primitive, by operation: it refuses what it has no answer for, and
  where it answers it must agree with the primitive's meaning on numbers, which is tested on random
  values. No line of the verifier is about one instruction.
- **The bytes are in the table too** (since November 18, 2026). Under each row are the ways its instances
  are written in bytes, in the processor manuals' notation (`REX.W 01 /r`, with which operand is in which
  field). One small function writes an instance's bytes in a way, in one form only. The bytes of a file are
  read as an instance of a row only if that function writes those very bytes for it. So reading is the
  inverse of writing by construction: whatever proposes what the bytes might be is relied on for nothing,
  and no form is read that the table does not write (a prefix that says nothing, a displacement longer
  than needed, a bit an encoding leaves unused: each was a question of its own for a reader written by
  hand). The same function is the assembler of the one language (section 14, item 5): `core/asm.py`
  writes every function of the sources with it, and no outside assembler stands between an Ode source
  and its bytes (for each of the 27 functions it gives the bytes clang gives: `lang/test_asm.py`).
- **Compared with processors.** Each form is run on real processors on random states and compared
  (Ode 0.1 did this for its AArch64 subset, and the Lean experiments for x86-64). Each change to a binary
  that the verifier accepts in an audit is run on a processor against the specification.
- **Only the forms needed.** The dream is a subset of x86-64 and of AArch64 sufficient for almost any
  program at full speed. A form outside the subset is refused.
- **Invariants the account keeps**, each adopted after a fault: the stack pointer stays within the
  function's own frame; nothing is remembered of the stack below the stack pointer; flags mean exactly
  what the instruction that set them defines; an instruction is at most fifteen bytes; a file is read in
  one shape, and every table it points at lies within it.

## 9. Composing functions

- **A call is taken by the callee's contract and by nothing else.** Each callee is verified apart against
  the same text. A ring of calls among functions is refused; a function that calls itself shows a
  quantity that decreases.
- **After a call the caller's facts must still be consistent.** A contract that promises the impossible
  cannot delete a path of its caller.
- **A loop whose count the path does not fix is taken at a place, by induction** against one turn of the
  specification's sequence. The place is written in the source and carried by the compiler.
- **State across calls** (an incremental hasher's `update` and `finalize`) is the next composition to
  build: a contract speaks of a state the caller keeps between calls.
- **Capabilities at the boundary** (proposed, unbuilt): a contract's piece of memory is a capability held
  in the proof, and no address exists without its piece. Where an unproved caller hands memory in, a
  checked entry makes the capability real, in the manner of Fil-C. Inside proved code the checks are
  erased because they are shown unnecessary.
- **One obligation, discharged where enough is known.** A requirement is stated once. It is shown before
  the program runs wherever possible; at a boundary with an unproved caller it is a check that stops the
  program; for a processor feature it is a test at startup. The record says which.

## 10. Names and identities

[NAMES.md](NAMES.md) has the requirements, which are binding, and the proposal, which is not yet decided.
Every readable name a maker sends is a possible ploy, and only names Bob assigns are hints he can lean
on. So a thing's name is the BLAKE3 hash of its content, whole, compared by the tool. A word is what
one named party calls a thing. A contract is hashed with the maker's words replaced by counted letters,
and her words travel beside it as a glossary. Code is named by its place in a file that is named by its
hash. A contract names no code: the verification joins the two.

## 11. Evidence beside proof

An unverified verifier is worth what its audits are worth, and a verified one still needs R4. So:

- **The game.** A maker playing the attacker wins when Bob's verifier says "shown" and the binary then
  breaks the contract on a processor. Every win found stays in the repository as a test the verifier must
  refuse (`kcheck/test_kholes.py`, `kcheck/backdoor.o`), with evidence of the break.
- **Reading as the attacker.** Of each instruction and each part of the model: what does the verifier take
  to be so that the processor, the linker or the arithmetic does not? This reading found the six
  faults of November 17, 2026, on a tree whose single-change audits had run clean.
- **Audits by change.** Every single-bit change of every verified function; each change the verifier
  accepts is run on a processor against the specification. Lemmas and specifications are changed too and
  judged on numbers. These find faults in instruction forms and are blind to faults that need several
  instructions, a layout or a contract changed together.
- **A gate short enough to run every time** (`kcheck/gate.py`, under five minutes, with a control that the
  kept bad binary is refused), and long sweeps as background soaks.
- **Claims are computed.** A sentence about what is shown is generated from the verifier's records, with
  the hashes of what it is about. A number typed by hand drifts from the proof beside it.
- **Blame is pinned.** A refusal says what is at fault where it can: an input that refutes the contract
  (the code or the contract), the source keeping the contract where the bytes break it (the compiler), a
  named clause the proof fails at (the proof), or the limit reached (no verdict).
- **Speed is measured**: a property of particular bytes on a particular machine, compared over pairs of
  runs, on a machine that is otherwise idle. A slower result is a bug of the rank of a wrong answer.

## 12. Bootstrapping

1. A first verifier in an existing language (today: Python), justified by audits and reading.
2. The small core, apart from it, with its soundness argument and a second implementation.
3. The core written in Ode and shown by the first verifier and by itself to meet a verifier's contract.
4. A launcher small enough to read, held by Bob, that admits the verifier by the hash of its bytes and runs
   exactly those bytes: a program cannot vouch for its own copy.

## 13. Where it stands (November 18, 2026)

What is built is a prototype of the outer architecture. The part Bob relies on is still large and
unproved.

| the design asks | today |
|---|---|
| a substantial program verified from its bytes | the one-shot BLAKE3 hash for x86-64 with AVX-512: 14 functions from Ode source, shipped as one file, against a specification of 185 lines and a contract of 7. About a tenth of the target crate's x86-64 kernels by bytes; no incremental hasher, no extendable output, no AVX2, no AArch64 |
| other programs than BLAKE3 | twelve functions in eight files: Adler-32, an LZ4 decoder and two encoders, a framed format that calls two of them, UTF-8 validation, base-64, variable-length integers, the Internet checksum |
| as fast as the best | 97% of the library's speed at 1 MiB, 60% at 16 to 32 KiB (a 16-lane path for 2 to 16 chunks is unwritten) |
| a small core with justified rules (R1) | the verifier is about 3,290 lines of unverified Python for the hash and a table of 93 rows with 150 ways of writing them in bytes, 1,200 lines more to show its definitions end. What an instruction does, and what bytes are one, is in the table; the rules for memory, calls, paths, places, returns, traces and files are now written down with their arguments in `core/RULES.md`, though still carried out by the full verifier rather than a small proof-replaying core. Only arithmetic is decided by a carried proof, in a core of 58 lines with a second implementation in C. Eight faults of the kind "shown, of something false" were found by reading on November 17 and 18, and closed; its soundness is not established. Beside it, since November 18, stands a first small core whose soundness is a theorem checked by Lean (`proof-core/`: 1,057 lines under the theorem, an account of 586 lines the theorem is about); it shows five shipped functions, the fast Adler-32 and one that writes memory for its caller among them, and a function that calls one of them, and does not yet read vector registers or a loop that writes for its caller |
| the coder chooses the machine code | every function is now its instructions in the source, and nothing is chosen between source and bytes (since November 18, 2026: the word-level layer and its compiler are gone). The five kernels were written so, and are the reference kernels byte for byte. Of the nine other functions of the hash one is written by hand (`node_out`: 18 instructions where the compiler printed 58); the other eight and the thirteen of the programs are, for now, what the old compiler last printed, with each old statement as a comment: longer than they need be, to be written again by hand |
| the coder's types carried to the bytes | a place in a loop (three forms), inner contracts, layouts, lemmas. No type system for Ode source; no verifier of source |
| the verifier's own contract | deterministic and offline; 22 kept cases it must refuse, and a gate that fails if the kept bad binary is accepted. Its limits are partial: a wrong lemma can take minutes to refuse |
| three answers | "shown" and "not shown" from the verifier; "false, with an input" from a tester that runs the binary on a processor (x86-64 Linux) |
| a contract shown able to hold | unbuilt: the tester makes calls that meet `requires`, and the reader is not yet shown one |
| exploring contracts; implications between contracts | unbuilt. `ensures` and `needs` lines can carry a condition today; `trace`, `writes` and `stack` lines cannot yet |
| names by hash, glossaries, Bob's own list | whole BLAKE3 digests of files and specifications are printed; the rest is a proposal |
| one account of the machine | what each instruction does and how it is written in bytes is one table (`core/x86.tab`: 93 rows, 150 ways of writing them), which the verifier reads code and steps by. 90 rows as an assembler writes them, and 147 ways as the table writes their bytes, are run from random states and compared with three processors (a Zen 4, a Zen 5, an Ice Lake Xeon), none differing (not run: the address of the file's data, the call and the return). Each of the 35 rules on symbols is tested against its primitive's meaning on numbers. Before the reader of code written by hand was taken out, the two read alike every instruction of every shipped file, and over every single-bit change of them never read two different rows. Changes the verifier accepts are judged by processors in audits |
| claims computed from records | a machine-readable record of each verification exists; the pages' numbers are still typed by hand |
| one driver for every binary | the hash's file has a driver of its own that knows its functions' names; the other programs share one |

## 14. Open decisions

Each is open on purpose, with what will close it.

1. **The core's proof format.** A small system of explicit inference rules, possibly in sequent style, is
   the candidate; Ode 0.1's kernel (sorted equations and structural induction, no search, a written
   soundness argument) is a working example of the kind for equations. *Closes when* one slice of the hash
   (a loop, a call, a memory boundary) is verified through a core with a soundness argument, and the
   proof's size and the verification's time are measured. *A first step is taken:* the machine's account
   is out of the verifier's code and into a table (section 8), and code is read by it in the way wanted of
   the whole core: something not relied on proposes, and a small written rule decides. The rules for
   memory, calls and places are next: to be written down once, each with its argument, and then carried
   out by the core from the written form.
2. **Types for Ode source.** Dependent or refinement types with ownership are the direction. *Closes
   when* a kernel and its caller are written with them and the compiler carries them to a proof the core
   accepts.
3. **Where computation in proofs lives**: a verified procedure in the core, or a derivation per decision
   from the prover (as arithmetic is today). *Criterion:* whichever keeps the core small on the first
   example's proofs.
4. **Data and file layout**: how code, constants, proof and specification are shipped, and how names of
   files and contracts follow the naming rules. *Decided so far (Sam, November 17, 2026):* a proof is a
   file of its own beside the binary, not a section inside it. The tools still read a proof carried in a
   binary (`.ode.proof`), and the shipped examples still carry theirs; that way is no longer maintained or
   extended, and is not being taken out either, since something like it may return. The rest (whether
   the specification a binary carries goes the same way; the files' names) is undiscussed.
5. **The word-level layer.** *Decided (Sam, November 17, 2026), and done (November 18):* one language.
   Every function, kernel or not, is written as its instructions, where each instruction, register and
   stack byte is the coder's choice. The word-level layer and its compiler are gone: its 22 functions
   stand in the sources as the instructions it last printed (the shipped files' bytes did not change),
   and are to be written again by hand (the first is: `node_out` by hand is 18 instructions where the
   compiler printed 58, and the same verifier takes it against the same contract). The assembler goes by the table
   (section 8): no outside assembler stands between source and bytes. *Open:* the conveniences.
   The one language will grow a compiler, of this
   kind only: it may check what the coder declares, expand a convenience in a fixed and documented way
   (a name bound to a register, an `if` over a flag the coder sets), and carry the coder's types and
   places down to the proof. It may not choose. What it would choose it asks the coder for; the test of a
   convenience is that the coder can tell the exact bytes from the source without running the compiler.
   The coder's information is kept for making proofs. It could serve speed or porting too, as a
   suggestion the coder accepts into the source; nothing relies on it for either, and nothing takes the
   control of the machine code from the coder.
6. **Succinct proofs of verification** (Lurk and its kind): an optional further leg, "a proof that the
   core accepted". *Criterion:* what Bob must read to rely on it is shorter than the core.
7. **The second instruction set**: AArch64 needs a decoder, an account and kernels of its own.

## 15. Relatives

Described from memory except where a reading is dated; each is to be read again against this design.

- **Proof-carrying code** (Necula and Lee; Appel's foundational form) and **typed assembly language**
  (Morrisett and others; with indices, Xi and Harper): the arrangement here. Binary and proof go to a small
  verifier; the compiler is outside the reliance set.
- **DML and ATS** (Xi and Pfenning), liquid types: types that speak of values from a decidable domain,
  annotations in place of proofs.
- **Vale** (Bond and others) and **Jasmin**: assembly-level languages for fast cryptographic code with
  contracts, the programmer in control of instructions. Nearest in subject. Each rests on a general proof
  assistant or solver, where Ode aims at a small verifier made for the purpose.
- **RefinedC** (Sammler and others): refinement types verified by a search-free procedure that produces
  proofs. Nearest in method.
- **Noether** (Daira-Emma Hopwood): a definite, layered language where each layer gives up power for
  reasoning. The model for the specification language's taste.
- **Mark Miller's work** on capabilities, pet names and reliance: the boundary with callers and the
  treatment of names.
- **Dale Miller, "Proof Theory and Dependent Type Theory"** (2026): keep apart what the coder can express,
  what reasoning the system supports, and the form in which a verifier receives a proof.
- **Kobeissi, "Nobody Will Read the Lean"** (2026): a verifier confirms that a proof establishes its
  statement; whether the statement says what its owner means is a human judgment. Hence section 3.
- **Lurk** and **Bend2** (read November 2026): Lurk proves that an expression evaluated, succinctly; Bend2
  proves properties of source. Neither verifies native bytes against a contract. Ideas taken: name every
  assurance's object by hash; say for each function which unproved things its showing rests on.
- **Lean** is where this work began (section 16). It remains welcome for lemmas about specifications and
  as one of the outside checks of the core.

## 16. Where earlier work lives

- **Ode 0.1** (October 2026): tag `v0.1.0` of this repository. A proof kernel for sorted equations with
  structural induction (`KERNEL.md`, 355 lines of Python), proof exporters for word arithmetic, a symbolic
  verifier for a bytecode and an AArch64 subset compared with a processor, content addressing with
  separated domains (`DOMAINS.md`), and a game of maker, verifier and attacker. Carried into this design:
  the reliance set, producers outside it, the verifier's contract, obligations discharged by stage,
  computed claims, pet names, the game, the pinned launcher. Its words "checker" and "certificate" are
  "verifier" and "proof" here.
- **The Lean experiments** (November 11 to 14, 2026): BLAKE3-Servil's repository, fork
  `samshackleton-tech/BLAKE3`, branch `experiment/sam-wide-model`, under `tools/verify/machine/` (`lang/`,
  `one/`, `spec/`, `alg/`, `arm/`, `wide/`). Whole-hash theorems in Lean over a machine model, with
  generated proofs. They took days a function, broke when code was rebuilt, and rested on about 2,500
  solver axioms an independent Lean verifier refuses; a purpose-built verifier does the same work in
  seconds and lets Bob rely on less. `lang/DESIGN.md` there records the decisions of those days; the ones
  that still bind are in sections 4, 5 and 11 above.
- **The verifier of binaries** (since November 14, 2026): developed at the same place, in `kcheck/`, to
  commit `dca7275f`. It moved here on November 17, 2026 and continues here.
