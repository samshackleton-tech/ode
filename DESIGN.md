# Ode: design

This page says what Ode is for and how it is designed to get there. It records decisions, including
decisions about work that has not been done yet. Section 13 says what exists today. Three earlier lines of
work come together here: Ode 0.1 (this repository's tag `v0.1.0`), the Lean experiments of November 11 to
14, 2026, and the verifier of binaries built since November 14. Section 16 says where each of them lives.

Other pages: [README.md](README.md) (what is here and how to run it), [kcheck/VERIFY.md](kcheck/VERIFY.md)
(for a person who is verifying a binary), [kcheck/LANGUAGE.md](kcheck/LANGUAGE.md) (the specification and
contract language), [NAMES.md](NAMES.md) (names and identities), [LESSONS.md](LESSONS.md) (what the work
has taught us), [kcheck/README.md](kcheck/README.md) (the dated record of evidence).

## 1. The goal

**Bob can establish, with his own tools, that a substantial, useful, fast native binary does what he
requires of it. For that conclusion he relies only on a short list of named things (section 2).**

Three things are shipped together: a *binary*, a *contract*, and a *proof*. The contract is a short formal
text. It says what a function in the binary does and what the function needs from its caller. The proof is
a file that a program called the *verifier* uses to check that the binary meets the contract.

The first use case is the one by which everything is judged today. Bob is an auditor. He examines the
security of some code by reading its contract and running his verifier. He gives the verifier the binary,
the proof and the contract. He does not read the implementation. Other uses, such as maintaining the code
or building on it, are separate use cases. They are taken up after this one.

Two requirements are hard:

1. **Soundness.** If the verifier accepts, the binary meets the contract. (The tools print the word
   `shown` when they accept.) A single wrong acceptance defeats the project.
2. **Soundness that Bob can check.** Bob can reach justified confidence in the verifier while relying on
   only a small part of it (section 7).

Four more are goals, in this order of priority. Each gives way to the two hard requirements:

3. Bob has little to read and little to rely on.
4. The native code is as fast as the best code written for that processor.
5. Producing programs with proofs is practical at scale.
6. Verification is fast and local, and needs no network.

Three more goals concern the answers that Bob gets. The verifier should seldom reject a binary that does
meet its contract. When a binary does not meet its contract, the tools should be able to say so and give
an input that demonstrates it. And the answers should come fast.

**The test of the design** is a program that people already depend on. The current target is the core
crate of BLAKE3-Servil (`blake3-servil-core`: the hash on one thread), written in Ode, as fast or nearly
as fast as its 0.10 release, and verifiable by its user. BLAKE3 is the first example. Ode is a project of
its own. Two examples are planned after it: a decompressor of the zstd family, and a verifier that is
itself verified against a contract for verifiers.

**What Ode leaves out, on purpose.** A narrow scope is what lets Ode go further than general tools. Ode
does not try to handle:

- programs that already exist. Code is written new, in Ode, so that it is fast and so that it can be
  proved;
- arbitrary mathematics and arbitrary computation in specifications and proofs;
- arbitrary assembly. The coder uses only the instruction forms that Ode has a formal model of;
- a proof for every program that the language can express. The coder writes code so that it can be proved,
  in the same way that he writes it to be fast;
- comfort for human coders who work without tools: convenient syntax, tutorials, names that are easy to
  remember;
- existing languages. Existing proof assistants are not required either. Lean may help, and nobody has to
  run it.

**Who takes part.** Each of them may be a person, an AI agent, or a team of both.

| | what they do | what Bob relies on them for |
|---|---|---|
| the coder | writes Ode source: the code, every machine-level decision, and the structure of the proof | nothing |
| the maker | ships a binary with its proof and its specification. The maker may be the coder, and may be an attacker | nothing |
| Bob | decides what he requires, chooses a contract that says it, and runs his verifier | his own judgment of what he wants |
| Bob's verifier | a deterministic program. It decides whether a proof establishes that these bytes meet this contract | accepting only binaries that meet their contract (section 2) |
| Carol | maintains the code. She sees things that Bob has no use for, such as the names of inner functions and the details of a rejection | nothing |

The setting is hostile. A maker may be an attacker, and an attacker looks like any other maker. Keys get
stolen. Auditors compare notes with strangers. So every design question about what is sent to Bob is asked
twice: how does a good maker use this, and how does an evil one?

## 2. Reliance sets: who relies on what, and for what

**The words.** We say *rely*, after Mark S. Miller (*Robust Composition*, 2006, section 5.1). Reliance
names a property of a mechanism that a conclusion rests on, and it points at what breaks if the property
fails. We do not use the word "trust". In ordinary life it names something good. In security writing a
"trusted" part is one that can hurt you. And the word draws attention to the nature of the part, and away
from the question that matters: relied on *for what*? Two sentences take its place. They state one fact
from two sides. (Miller defines "relies upon" as dependence that a specification allows, on top of the
plain fact "is vulnerable to". The two uses below follow him.)

- **"A relies on X for P"** is for what the design is built on by intention. P is something that X is
  there to deliver, and the reader is asked to examine X or to have a reason for believing P. This
  sentence is never written without the "for what".
- **"A is vulnerable to X"** is for a gap that is still open. X is in a position to do harm and nothing
  checks it. Examples are a step that no proof covers yet, and a party who may be an attacker. This sentence is
  written with the harm, and with what would close the gap where that is known.

If "relies on" were used for an exposure that nobody chose, a risk would look like a decision. If
"vulnerable to" were used for the small core that Bob is asked to examine, the exposures that are
open would be hidden among alarms. A negative statement takes the first form. "The verdict does not rely on
the prover" claims exactly what the verifier's checking gives. "Bob is not vulnerable to the prover" would
claim more than is true, because a prover can still withhold a proof.

**Reliance sets.** Everything that an actor relies on for a conclusion is that actor's *reliance set*. In
Miller's words: "We will refer to the set of all elements on which P relies as P's reliance set." Two
actors can have different reliance sets, and so can two Bobs. Anything that lies in the reliance sets of
all of them is, in Miller's words, "a central point of failure". The older term "trusted computing base"
is used for a reliance set, for a platform, and for that intersection, and it does not say which is meant.

**What every Bob relies on.** Bob's conclusion is "this binary does what I require". It rests on the six
entries below and on nothing else. The compiler, the assembler, the linker, the prover, the coder and the
maker are absent from the table: whatever they produce is accepted only where the verifier accepts it.

| | Bob relies on | for | why this cannot be removed | what keeps it small and checkable |
|---|---|---|---|---|
| R1 | the verifier | accepting only what its rules allow, the rules being sound | every verification ends at some program that is run | a small core with explicit rules and a soundness argument. Bob has a choice of how to become confident in it (below, and section 7) |
| R2 | the programs that read the files | reading correctly the bytes they are given: the binary's file format and the contract's text | a proof is about bytes, and something has to connect bytes to meaning | they are part of the core. Only one form of file is accepted. Every name that the file gives to a linker must be verified |
| R3 | the contract | saying what Bob requires | only Bob knows what he wants (section 3) | contracts short enough to read in full, in a language made for the reader; a closed world (section 4) |
| R4 | the model of the processor | matching the processors it names | a proof about machine code is a proof about a model of the machine | one authoritative model. Each instruction form is compared with real processors. In audits, every changed binary that the verifier accepts is run on a processor (sections 8 and 11) |
| R5 | the physical processor | executing its instruction set correctly | no proof about code reaches physics | each promise states its exact scope. A contract's `trace` line speaks of instructions and addresses, and of nothing else |
| R6 | BLAKE3 | being collision-resistant | things are named by the hash of their content (section 10) | one hash function everywhere, digests written in full, compared by the tool |

**Where Bobs differ.** For R1, the design gives each Bob a choice of what to rely on (sections 7 and 12).
Each choice is a different reliance set:

1. Bob reads the core himself. His set contains his own reading.
2. A second core, written independently, accepts the same proof. His set contains "the two cores do not
   share a soundness bug".
3. The core is proved sound in a proof system that Bob already relies on, such as Lean or HOL Light. His
   set contains the program that verifies that system's proofs, and his own reading of the theorem.
4. The core is written in Ode and verified by Ode's own verifier. Alone this is circular. Combined with
   any one of the other three it is strong.

**Other actors, other conclusions.** The maker's conclusion is "Bob's verifier will accept my binary". For
that she relies on the prover, the compiler and her other tools. None of them is in any Bob's reliance
set. The coder relies on tools that say, early and precisely, why a proof fails. Carol relies on
names and messages that Bob never sees.

**What all the Bobs share** is R2 to R6, and the property in R1. These are the central points of failure.
They are where the design spends its effort on making things small and checkable.

**What Bob is vulnerable to today.** Section 13 compares the design with what exists. Three gaps matter
most:

- The verifier in use today is large and is not proved. Bob is vulnerable to a soundness bug anywhere in
  it: a wrong binary would be accepted. Eight such bugs were found and fixed in November 2026. The small
  core of section 7 is what closes this gap.
- Nothing checks the link step. When a verified object file is linked into a program, Bob is vulnerable to
  a linker, or a link command, that sends the program's calls somewhere else than the verified bytes.
- Every readable name that a maker sends is the maker's choice. Bob is vulnerable to a name that suggests
  more than its contract says (section 10).

## 3. Bob's intent and the contract his verifier decides

**Bob's intent** is what Bob wants from the software. It is his own view, and it keeps developing. It
includes concerns that he has not thought of yet and trade-offs that he has not settled. It may be vague,
incomplete or inconsistent, and it may change. Nobody else knows it, and no tool can know it until Bob
makes up his mind. It is an input to the process. There is no hidden formal contract behind it that is
waiting to be recovered.

A **public contract** is a precise statement about one function in a binary. It says what the caller must
provide (`requires`) and what the function then does (`ensures`, and the closed-world rule of section 4).
A **full contract** is a public contract together with every definition that it uses, directly or through
other definitions. The word "contract" always means the formal text. A full contract is a candidate
statement of part of Bob's intent.

Two questions are kept apart:

- *Does this contract say what Bob wants?* That is Bob's judgment. He may make it alone, with help, or by
  a policy that he has chosen to delegate to.
- *Do these bytes meet this contract?* That is a question for a deterministic verifier. The answer is the
  same for everyone, and no judgment of the maker or of an assistant enters into it.

The intended use is a conversation. Bob tries a candidate contract and asks: "if *this* is what I require,
does *that* library provide it?" His tools answer quickly and cheaply. The answer teaches him something,
and he revises the candidate, or his intent. For example, Bob at first cares only that a function hashes a
message correctly. An assistant raises the question of timing. Bob then decides whether the message is
secret. If it is, he requires that the instructions executed and the addresses touched depend only on the
length of the message. The tools can tell him which libraries provide each choice. Which choice he should
make is for him to decide.

The answers are quick and reliable because they are verifications of evidence:

- The binary comes with a proof of one public contract for each function. Two promises can be
  incomparable. One asks more of the caller and gives more: for inputs below 2^32 bytes, the trace depends
  only on the length. Another asks less and gives less. Neither can stand in for the other. So a promise
  may carry its condition (`ensures X if C`), and the contract holds every promise that its maker stands
  behind. Everything that she can prove is in one contract, and Bob receives it.
- Bob says what he, as the caller, will guarantee. His tool tells him what the contract then promises
  him. A promise applies if its condition follows from his guarantees, and the other promises drop out.
  Where he drops a promise or adds a guarantee, the tool decides the result from the two texts. Where his
  candidate needs reasoning, for example because it defines the same thing in another way, the candidate
  needs a proof of its own.

Each answer is one of three, and the three are kept distinct:

- **accepted** (the tools print `shown`);
- **refuted**, with evidence, such as an input on which the binary breaks the contract;
- **not accepted** (the tools print `NOT shown`). This answer says nothing about the program. It means
  that no proof was found or supplied. It does not mean that the binary fails.

An answer about one contract remains an answer about that contract when Bob changes his mind.

Finding a proof of an arbitrary new contract quickly is not promised. That is work for the prover and for
the coder. Exploring contracts interactively, and verifying that one contract implies another, are design
goals. The present tools verify one supplied proof against one given contract.

## 4. The specification and contract language

What Bob reads is written in a language of its own. It is separate from the code language, smaller than
it, and made for the reader. [kcheck/LANGUAGE.md](kcheck/LANGUAGE.md) defines it. These rules shape it:

- **The specification is declarative.** It says what a hash, a checksum, a format or an encoding *is*. It
  does so by definitions written as equations, with no mutable state and no memory. It can be evaluated on
  numbers: the official test vectors are run this way, and a tester searches for refuting inputs this way.
  A contract may also use a specification in a way that gives no algorithm, such as "decoding the output
  gives back the input".
- **A contract is a Hoare triple under a closed world.** `requires` says what the caller must provide.
  Everything else is the function's promise: what it returns and writes; that it reads and writes nothing
  else; that it terminates; that it stays within a stated amount of stack; that it preserves the registers
  that its calling convention says it preserves; and that its trace depends only on what the contract
  names. (The *trace* of a call is the sequence of instructions it executes and addresses it touches.)
  Saying nothing is the stronger promise. A function that needs to do more must have a contract that says
  so.
- **Memory holds bytes.** Byte order is stated in one place only, by the two words `words` and `bytes_of`.
- **Failure is a value.** A specification says `fails REASON if C`, and the contract says what the
  function does in that case. Some contracts do not describe a way to compute the result. Such a contract
  must also say when the answer "no" is ruled out. Otherwise an encoder that always answers "no" would
  meet it.
- **Every line must be needed.** Each line of a public contract is tested by removing it. A line whose
  removal changes nothing is deleted.
- **A name has one meaning.** A name is declared once. The language's own words cannot be redefined. A
  proof may not declare a name that appears in the text that Bob reads.

Two more rules are decided and are not built yet:

- **A contract must be satisfiable.** If no call can meet a contract's `requires`, the contract is true of
  every binary. So the reader is shown a call that meets it, or is told that none was found.
- **One language page, identified by its hash.** A full contract names the version of the language it is
  written in by the hash of that page. A later change to the language then cannot silently change the
  meaning of an old contract.

Changing a specification to suit the code that implements it puts a cost on every reader. Where the code
needs a fact that the plain specification leaves implicit, the fact is a **lemma**: a contract for a
definition. It is part of the proof, the verifier checks it, and Bob does not read it.

## 5. The coder chooses the machine code

Most language design tries to take a portable description from the coder and have a compiler find a fast
implementation of it. **Ode gives up that aim.** The coder states the machine-level decisions: which
instructions; which registers hold what; how vector registers and their lanes are used; the order of the
instructions; where every buffer is and how it is aligned; what is saved and where; and how functions pass
arguments to one another. What Ode automates is **the proof that the chosen implementation meets the
contract.** The results of programming-language research (types, ownership, refinement, certifying
compilation) are used for that purpose.

Consequences:

- **The compiler does what is written, or it refuses.** It expands the coder's macros, resolves labels
  and distances, and writes the proof next to the code. It does not add an instruction, move one, or pick
  a register or a layout as an optimization. Where the source does not settle a choice, it stops and says so.
- **The coder can predict the result.** The same source for the same target gives the same bytes. The
  bytes of one function depend only on the source of that function. Both properties are tested.
- **Generators, macros and searching agents are welcome on the coder's side.** They may propose and
  measure thousands of candidates. The source that is accepted records the decisions, so compiling it
  makes no new decisions.
- **One kind of input.** Everything is Ode source. A kernel's instructions are written one by one in the
  instruction layer of the language. Hand-written assembly next to it serves as a reference for bytes and
  for speed. It is not a second source.
- **People and agents carry speed from one processor to another, and the tools carry assurance.** A
  specification, a contract, a proof method and a template serve every target. A fast implementation for
  another instruction set is another piece of chosen code.
- **The speed of the chosen code is still measured.** Writing the instructions down fixes what runs. How
  fast it runs on a given machine is a measurement (section 11).

Memory and calls follow the same rule. This was decided in November 2026 and is partly built:

- **The cost of memory is what gets touched**: cache lines, pages, and what is shared between threads. A
  size in bytes does not measure it.
- **Nothing is allocated at run time.** The memory that a call needs is set aside beforehand, stated
  exactly in the contract (the `stack` line), and proved.
- **The coder lays out memory, and the compiler does what is written or stops.** A detailed proposal
  awaits a decision. In it, buffers lie in the order written, each with the alignment written. `line` and
  `page` are the target's names for the sizes of its cache line and its page. The coder may state what a
  layout is for (two things on one cache line, or two things on separate lines), and the compiler checks
  the statement.
- **Calls between Ode functions need no fixed convention.** Where the arguments are, what a called
  function may change, and whether it has a stack frame of its own are stated in its contract and proved.
  The C convention stays at the boundary where C or Rust calls in.
- **Code that the proof shows cannot be reached is removed.** So is a check that cannot fail. Where a
  caller has no proof, the check belongs in a separate entry point that does the checking.

The closest relatives are Jasmin (the programmer controls instruction selection and scheduling), Vale,
typed assembly language and proof-carrying code. See section 15.

## 6. The coder supplies the structure of the proof

The coder knows why the code is right. Ode has the coder say so at the point where the decisions are made,
and carries that information down to the bytes. There are three means, each taken from existing practice:

- **Types that mention values**: a buffer of `64 * n` bytes; a register that holds `n - b`; a vector
  register that holds the specification's `h[b]`; a function's contract, which is its type; a loop
  invariant, which is the type of the machine state at one point in a loop.
- **Ownership and permission for memory**: which ranges may be written, which may only be read, and that
  two ranges have no byte in common.
- **Proof-only values**: quantities such as "the number of iterations so far". They exist for the proof
  and cost nothing at run time.

For the 16-lane BLAKE3 loop the coder writes, at the head of the loop: these registers keep their values;
this one holds `n - b`; this one holds `64 * b`; these eight hold `h[b]`. That one annotation serves speed
(the chosen registers, the aligned scratch space) and it serves the proof (the bounds, the invariant, the
termination of the loop).

Two rules limit this:

- **An annotation creates an obligation. Facts come only from what the verifier has checked.** The
  verifier relies on nothing in a proof (inner contracts, layouts, lemmas, kinds, loop invariants) before
  it has checked it. It may use each of them only after checking it. A description of something impossible
  gives the verifier no value of that thing.
- **The final verdict is about the binary.** A proof about source code says nothing about a compiler that
  emitted something else. A verifier of Ode *source* is wanted as a tool for the coder, because it can
  give exact messages early. The verifier of the binary remains Bob's.

Which type system the coder's side uses, and which form of proof the verifier accepts, are separate
choices (section 14).

## 7. What the verifier establishes, and why Bob can be confident in it

**The obligation.** Suppose the verifier accepts a proof of a contract for some bytes. Then every call
that meets the contract's `requires` satisfies the contract, under the stated model of the processor: the
result, the memory read and written, the registers preserved, termination, the stack used, the processor
features needed, and the trace.

**The proof.** The verdict does not rely on the proof. A proof is a file of its own beside the binary
(section 14, item 4). The specification that the maker used is shipped as well, as a convenience. Bob
verifies against his own copy, or he reads the shipped one first.

**The verifier's own contract.**

- It answers "accepted" or "not accepted", and it gives a reason for every rejection. Malformed input, an
  unknown version and a form that it does not support are rejections.
- It is deterministic and works offline. The same bytes give the same answer, with no network, clock or
  randomness.
- It works within stated limits on the size of its input and on the work it does. Reaching a limit is a
  rejection.
- It only verifies. Guessing is the prover's work: where a loop invariant belongs, which lemma helps,
  which inequalities add up. The prover is in no Bob's reliance set.
- Everything that it prints for Bob is derived from the contract. A line that depends on text from the
  proof is printed only after that text has been checked. In Bob's mode it prints nothing that the maker
  chose and that Bob has no use for.
- It comes with inputs that it must reject: binaries and proofs that are wrong in known ways (section 11).

**How Bob can become confident in the verifier: shrink the core that he relies on, and make that core
provable.** Today's verifier executes the binary symbolically, with machinery that is clever and large.
Every soundness bug found in it had the same form: something became a fact because the implementation
represented it that way. Examples are one name for two different unknowns; independent fields for bytes
that overlap; a sequence identified by the form of its first value; and a number treated as an address.
The rule against that form is:

> Nothing becomes a fact because a clever part of the implementation represents it that way. Every fact
> follows from a small, explicit rule whose soundness has been established.

So the design separates three things:

1. **The formal model**: what a contract promises, what the processor does, and what the text of a
   specification means. It is written once, in a form that both a reader and a proof can use.
2. **The core**: a small verifier that accepts a proof only by explicit rules. Each rule is justified
   against the formal model. The core may execute instructions and unfold definitions itself, so a proof
   stays small. A proof contains what would otherwise have to be searched for: loop invariants, lemmas,
   and derivations of arithmetic facts. It leaves out what can be computed.
3. **The prover's abstractions**: regions of memory, summaries of loops and calls, knowledge about
   kernels. These can be as clever as they like. Their output is a proof for the core.

Assumptions and unknowns have exact scopes. Each register that a call may change becomes a separate
unknown. A fact learned on one branch holds only on that branch. An induction hypothesis is available
only under the rule that justifies it.

**Each Bob chooses what to rely on for the core.** No single foundation is required of every Bob. The
core is sound if any one of the following holds, and each Bob chooses among them. Each choice gives him a
different reliance set (section 2).

1. He reads the core himself. It is small enough for that.
2. A second core, written independently, accepts the same proof.
3. The core is proved sound in a proof system that he already relies on, such as Lean or HOL Light. This
   is an option for those who want it. It is never required.
4. The core is written in Ode, specified in Ode's specification language, and verified by Ode's own
   verifier against that contract. Alone this is circular. With any one check from outside it is strong.

For that reason the core is designed so that it *could* be written in Ode: small, with plain data, and
with nothing clever in it. Bob himself does not have to read the model of the processor or the soundness
argument. He needs a justified route, of his own choosing, from his question to his tool's answer. His
basis for relying on his verifier may be proofs, independent tools, earlier scrutiny by others, or the
expertise of his team.

**A first core exists: `proof-core/`.** It is a verifier written in Lean 4. It decides by a proof that it
is given. With it comes a theorem that Lean checks (`verify_all_sound`): if this verifier accepts the
functions in its input, whatever the proofs contain, then every one of them meets its contract on the
processor that the instruction table describes. The formal model that the theorem is about is 830 lines.
The verifier's own 2,003 lines are covered by the theorem, so a Bob who takes the third route does not
have to read them.

It handles a first part of what the full verifier handles: instructions on the general-purpose registers,
the flags and memory; loops, by loop invariants and induction; calls, by the contract of a function that
has already been verified (both functions that return a number and functions that write a buffer of words
for their caller); contracts with input buffers, output buffers, records laid out in memory, `returns` and
`stack`; and vector instructions that compute on 32-bit words. The verifier can follow operations on
512-bit registers and loads and stores at fixed offsets in buffers. It can follow a stack pointer
rounded down to a 64-byte boundary and the stores and loads in that frame. It still needs rules for
the 16-way kernel's indirect loads through its pointer array and its loop. The
specification model covers all of `kcheck/blake3.spec`. Evaluated in Lean, that specification
reproduces the 105 official test vectors.

As of November 19, 2026 it verifies five of the twelve small shipped functions, a function that calls one
of them, and three of the fourteen functions of the BLAKE3 hash: the two versions of the kernel that
compresses one block (proofs of 131 and 137 bytes, verified in 12 and 13 ms) and `b3l_node_out`, which
reads a 120-byte node record and calls one of them (a 38-byte proof, verified together with both kernels
in 22 ms). [proof-core/README.md](proof-core/README.md) has the list, the sizes and the times.

That page also says what is left out. Reading the object file and the text of the specification happens
outside the theorem. So do the link step and the check of which processor features a function needs. The
promise in the kernels' contracts that the trace does not depend on the data (constant time) is not in the
Lean model. This is the third route of the list above, begun. Lean is the language of this
implementation. No reader is required to use it: a proof is a text file that a verifier written in any
language can read.

## 8. The model of the processor

- **One authoritative model** of each instruction form that Ode uses. Every reading of an instruction is
  taken from it. Decoding (from bytes to instructions), the model (what an instruction does) and the proof
  rules are separate responsibilities. No reading may erase a distinction that another one needs. For
  example, the address of the file's data and a number that happens to equal it are different things.
- **The model is a table, not code** (`core/x86.tab`, since November 17, 2026). Each row describes one
  instruction form: how an assembler writes it, how the decoded instruction is written, and its effect, as
  a few statements built from primitive operations (`D = add64(D, S); zf = unknown; cf = unknown`). A row
  states what the instruction does in general. `= unknown` leaves a part of the state unspecified, and the
  verifier may then not rely on that part. Three readers use the same row: the verifier, which applies the
  effect to symbolic values; the comparison with a processor, which applies it to numbers; and an auditor.
  For each primitive operation the verifier has a partial rule for what it can conclude on symbolic
  values. It rejects what it has no answer for. Where it has an answer, the answer must agree with the
  meaning of the primitive on numbers, and that is tested on random values. No line of the verifier is
  about one particular instruction.
- **The byte encodings are in the table too** (since November 18, 2026). Under each row are the ways in
  which its instances are encoded, in the notation of the processor manuals (`REX.W 01 /r`, with a note of
  which operand is in which field). One small function writes the bytes of an instance in a given
  encoding, in exactly one form. The bytes of a file are read as an instance of a row only if that
  function writes exactly those bytes for it. So reading is the inverse of writing by construction.
  Whatever proposes what the bytes might mean is relied on for nothing. And no form is read that the table
  does not write: a prefix that has no effect, a displacement longer than necessary, a bit that an
  encoding does not use. Each of these was a separate question for a decoder written by hand. The same
  function is the assembler for the language (section 14, item 5). `core/asm.py` writes every function in
  the sources with it, and no outside assembler stands between an Ode source and its bytes. For each of
  the 27 functions it produces the same bytes as clang (`lang/test_asm.py`).
- **Compared with processors.** Each instruction form is run on real processors from random states and
  compared with the model. (Ode 0.1 did this for its AArch64 subset, and the Lean experiments did it for
  x86-64.) In an audit, every changed binary that the verifier accepts is run on a processor against the
  specification.
- **Only the forms that are needed.** The long-term aim is a subset of x86-64 and a subset of AArch64 that
  are sufficient for almost any program at full speed. A form outside the subset is rejected.
- **Invariants that the model keeps.** Each was adopted after a soundness bug. The stack pointer stays
  within the function's own frame. Nothing is remembered about the stack below the stack pointer. Flags
  mean exactly what the instruction that set them defines. An instruction is at most fifteen bytes long. A
  file is read in one form, and every table that it points to lies inside it.

## 9. Composing functions

- **A call is handled by the called function's contract and by nothing else.** Each called function is
  verified separately against the same text. A cycle of calls among functions is rejected. A function
  that calls itself must give a quantity that decreases.
- **After a call, the caller's facts must still be consistent.** A contract that promises something
  impossible cannot make a path of its caller disappear.
- **A loop whose number of iterations is not fixed is handled at a loop invariant, by induction**, against
  one step of the specification's sequence. The invariant is written in the source, and the compiler
  carries it into the proof.
- **State kept across calls** is the next kind of composition to build. An example is the `update` and
  `finalize` of an incremental hasher: the contract speaks of a state that the caller keeps between calls.
- **Capabilities at the boundary** (proposed, not built). A contract's piece of memory is a capability
  held in the proof, and there is no address without its piece. Where a caller that has no proof passes
  memory in, an entry point with checks makes the capability real, in the manner of Fil-C. Inside proved
  code the checks are removed, because they have been proved unnecessary.
- **One obligation, discharged where enough is known.** A requirement is stated once. Wherever possible
  it is proved before the program runs. At a boundary with a caller that has no proof, it is a check that
  stops the program. For a processor feature, it is a test at startup. The record says which of these
  applies.

## 10. Names and identities

[NAMES.md](NAMES.md) has the requirements, which are binding, and the proposal, which is not decided yet.
Every readable name that a maker sends may be a trick. Only the names that Bob assigns himself are hints
that he can rely on for recognizing a thing. So the name of a thing is the BLAKE3 hash of its content,
written in full and compared by the tool. A word is what one named party calls a thing. A contract is
hashed with the maker's words replaced by numbered letters, and her words are sent beside it as a
glossary. Code is identified by its position in a file that is identified by its hash. A contract names
no code: the verification connects the two.

## 11. Evidence besides proof

A verifier that is not itself verified is worth what its audits are worth. A verified one still needs R4
of section 2. So:

- **The game.** A maker who plays the attacker wins when Bob's verifier accepts and the binary then
  breaks the contract on a processor. Every win that is found stays in the repository as an input that
  the verifier must reject (`kcheck/test_kholes.py`, `kcheck/backdoor.o`), with evidence of the break.
- **Reading as the attacker.** For each instruction and each part of the model we ask: what does the
  verifier assume that the processor, the linker or the arithmetic does not guarantee? This reading found
  the six soundness bugs of November 17, 2026, in a tree whose audits by single changes had found nothing.
- **Audits by change.** Every single-bit change of every verified function is tried. Each change that
  the verifier accepts is run on a processor against the specification. Lemmas and specifications are
  changed too, and judged on numbers. These audits find bugs in instruction forms. They cannot find bugs
  that need several instructions, a layout or a contract to change together.
- **A gate short enough to run every time** (`kcheck/gate.py`, under five minutes, with a control: the
  stored bad binary must be rejected), and long sweeps that run in the background.
- **Claims are computed.** A sentence about what has been verified is generated from the verifier's
  records, with the hashes of the things it is about. A number typed by hand drifts away from the proof
  next to it.
- **Blame is assigned.** A rejection says what is at fault where it can: an input that refutes the
  contract (the code or the contract is at fault); source that keeps the contract where the bytes break
  it (the compiler); a named clause at which the proof fails (the proof); or a limit that was reached (no
  verdict).
- **Speed is measured.** It is a property of particular bytes on a particular machine. It is compared
  over pairs of runs, on a machine that is doing nothing else. A slower result is a bug of the same rank
  as a wrong answer.

## 12. Bootstrapping

1. A first verifier in an existing language (today: Python), justified by audits and by reading.
2. The small core, separate from it, with its soundness argument and a second implementation.
3. The core written in Ode, and verified against a contract for verifiers by the first verifier and by
   itself.
4. A launcher small enough to read, kept by Bob. It admits the verifier by the hash of its bytes and runs
   exactly those bytes. A program cannot vouch for its own copy.

## 13. Where it stands (November 19, 2026)

What has been built is a prototype of the outer architecture. The part that Bob relies on is still large
and is not proved.

| the design asks for | today |
|---|---|
| a substantial program verified from its bytes | the one-shot BLAKE3 hash for x86-64 with AVX-512: 14 functions from Ode source, shipped as one file, against a specification of 185 lines and a contract of 7 lines. That is about a tenth of the target crate's x86-64 kernels by bytes. There is no incremental hasher, no extendable output, no AVX2 and no AArch64 |
| programs other than BLAKE3 | twelve functions in eight files: Adler-32, an LZ4 decoder and two encoders, a framed format that calls two of them, UTF-8 validation, base-64, variable-length integers, and the Internet checksum |
| code as fast as the best | 97% of the library's speed at 1 MiB, and 60% at 16 to 32 KiB (a 16-lane path for 2 to 16 chunks has not been written) |
| a small core with justified rules (R1) | The verifier in use is about 3,290 lines of Python for the hash, which are not proved, and a table of 93 rows with 150 byte encodings. About 1,200 more lines check that the definitions of a specification terminate. What an instruction does, and which bytes are an instruction, is in the table. The rules for memory, calls, paths, loop invariants, returns, traces and files are written down with their justifications in `core/RULES.md`. They are still carried out by the full verifier and not by a small core that replays a proof. Only arithmetic is decided by a supplied proof, in a core of 58 lines with a second implementation in C. Eight soundness bugs were found by reading on November 17 and 18, and fixed: in each case a wrong binary would have been accepted. The soundness of this verifier has not been established. Next to it stands the first small core, whose soundness is a theorem checked by Lean (`proof-core/`, section 7): 1,906 lines covered by the theorem, with a formal model of 807 lines. It verifies five shipped byte programs, a function that calls one of them, the two one-block kernels and their caller. It also handles 512-bit registers and unaligned loads and stores at fixed offsets in buffers |
| the coder chooses the machine code | Every function is written in the source as its instructions, and nothing is chosen between the source and the bytes. That has been so since November 18, 2026, when the word-level layer and its compiler were removed. The five kernels were written this way and are identical, byte for byte, to the reference kernels. Of the nine other functions of the hash, one has been written by hand (`node_out`: 18 instructions where the compiler produced 58). The other eight, and the thirteen functions of the other programs, are for now what the old compiler last produced, with each old statement kept as a comment. They are longer than necessary and are to be rewritten by hand |
| the coder's types carried down to the bytes | a loop invariant (three forms), inner contracts, layouts and lemmas. There is no type system for Ode source and no verifier of source |
| the verifier's own contract | It is deterministic and works offline. There are 22 stored cases that it must reject, and a gate that fails if the stored bad binary is accepted. Its limits on work are partial: a wrong lemma can take minutes to reject |
| three answers | "accepted" and "not accepted" come from the verifier. "Refuted, with an input" comes from a tester that runs the binary on a processor (x86-64 Linux) |
| a contract shown to be satisfiable | not built. The tester makes calls that meet `requires`, but the reader is not shown one yet |
| exploring contracts; implications between contracts | not built. `ensures` and `needs` lines can carry a condition today. `trace`, `writes` and `stack` lines cannot yet |
| names by hash, glossaries, Bob's own list of names | the tools print full BLAKE3 digests of files and specifications. The rest is a proposal |
| one model of the processor | What each instruction does and how it is encoded is one table (`core/x86.tab`: 93 rows, 150 encodings). The verifier decodes and executes by it. 90 rows, as an assembler writes them, and 147 encodings, as the table writes their bytes, have been run from random states and compared with three processors (a Zen 4, a Zen 5 and an Ice Lake Xeon). None differed. Three rows were not run: the address of the file's data, the call and the return. Each of the 35 rules on symbolic values is tested against the meaning of its primitive on numbers. Before the decoder written by hand was removed, the two decoders agreed on every instruction of every shipped file, and over every single-bit change of those files they never read two different rows. In audits, changed binaries that the verifier accepts are judged by processors |
| claims computed from records | a machine-readable record of each verification exists. The numbers on the pages are still typed by hand |
| one driver for every binary | the hash's file has a driver of its own that knows the names of its functions. The other programs share one driver |

## 14. Open decisions

Each of these is open on purpose, and each says what will close it.

1. **The format of proofs for the core.** The candidate is a small system of explicit inference rules,
   possibly in sequent style. The kernel of Ode 0.1 is a working example of this kind for equations:
   sorted equations and structural induction, no search, and a written soundness argument. *This closes
   when* one slice of the hash (a loop, a call, a memory boundary) has been verified through a core that
   has a soundness argument, and the size of the proof and the time of the verification have been
   measured. *Two steps have been taken.* First, the model of the processor has been moved out of the
   verifier's code and into a table (section 8). Code is now read in the way that is wanted for the whole
   core: something that is relied on for nothing proposes, and a small written rule decides. Second, the
   core in `proof-core/` (section 7) has verified loops, calls and writes to the caller's memory in small
   functions, and two kernels of the hash, under a soundness theorem, with sizes and times measured. The
   decision stays open until a slice of the hash that has a loop and a call has gone through that core.
2. **Types for Ode source.** The direction is dependent or refinement types with ownership. *This closes
   when* a kernel and its caller have been written with them, and the compiler has carried them into a
   proof that the core accepts.
3. **Where computation in proofs happens**: in a verified procedure inside the core, or in a derivation
   for each decision, supplied by the prover, as is done for arithmetic today. *Criterion:* whichever
   keeps the core small on the proofs of the first example.
4. **Data and file layout**: how code, constants, proof and specification are shipped, and how the names
   of files and contracts follow the naming rules. *Decided so far (Sam, November 17, 2026):* a proof is
   a file of its own beside the binary. It is not a section inside the binary. The tools can still read a
   proof stored inside a binary (`.ode.proof`), and the shipped examples still store theirs that way. That
   way is no longer maintained or extended. It is not being removed either, because something like it
   may return. The rest has not been discussed: whether the specification stored in a binary moves out in
   the same way, and what the files are called.
5. **The word-level layer.** *Decided (Sam, November 17, 2026) and done (November 18):* there is one
   language. Every function, kernel or not, is written as its instructions, and each instruction,
   register and stack byte is the coder's choice. The word-level layer and its compiler are gone. Its 22
   functions are in the sources as the instructions that it last produced, and the bytes of the shipped
   files did not change. They are to be rewritten by hand. The first has been: `node_out` written by hand
   is 18 instructions where the compiler produced 58, and the same verifier accepts it against the same
   contract. The assembler works from the table (section 8), so no outside assembler stands between source
   and bytes. *Open:* the conveniences. The one language will grow a compiler, of one kind only. It may
   check what the coder declares. It may expand a convenience in a fixed and documented way, such as a
   name bound to a register, or an `if` over a flag that the coder sets. And it may carry the coder's
   types and loop invariants down to the proof. It may not choose. Where it would have to choose, it asks
   the coder. The test of a convenience is that the coder can tell the exact bytes from the source without
   running the compiler. The coder's information is kept for making proofs. It could serve speed or
   porting as well, as a suggestion that the coder accepts into the source. Nothing relies on it for
   either, and nothing takes control of the machine code away from the coder.
6. **Succinct proofs of verification** (Lurk and similar systems): an optional further route, "a proof
   that the core accepted". *Criterion:* what Bob has to read in order to rely on it is shorter than the
   core.
7. **The second instruction set.** AArch64 needs a decoder, a model and kernels of its own.

## 15. Related work

These are described from memory, except where a reading is dated. Each is to be read again against this
design.

- **Proof-carrying code** (Necula and Lee; Appel's foundational form) and **typed assembly language**
  (Morrisett and others; with indices, Xi and Harper): the arrangement used here. Binary and proof go to
  a small verifier, and the compiler is in no user's reliance set.
- **DML and ATS** (Xi and Pfenning), and liquid types: types that mention values from a decidable domain,
  with annotations in place of proofs.
- **Vale** (Bond and others) and **Jasmin**: assembly-level languages for fast cryptographic code with
  contracts, in which the programmer controls the instructions. These are the closest in subject. Each
  relies on a general proof assistant or solver, where Ode aims at a small verifier made for the purpose.
- **RefinedC** (Sammler and others): refinement types verified by a procedure that does no search and
  produces proofs. This is the closest in method.
- **Noether** (Daira-Emma Hopwood): a definite, layered language in which each layer gives up power in
  exchange for easier reasoning. It is the model for the taste of the specification language.
- **Mark S. Miller's work** on capabilities, pet names and reliance: the boundary with callers, the
  treatment of names, and the vocabulary of section 2. *Robust Composition* (2006), sections 5.1 and 5.2,
  was read on November 19, 2026.
- **Dale Miller, "Proof Theory and Dependent Type Theory"** (2026): keep apart what the coder can
  express, what reasoning the system supports, and the form in which a verifier receives a proof.
- **Kobeissi, "Nobody Will Read the Lean"** (2026): a verifier confirms that a proof establishes its
  statement. Whether the statement says what its owner means is a human judgment. Hence section 3.
- **Lurk** and **Bend2** (read in November 2026): Lurk proves succinctly that an expression was
  evaluated. Bend2 proves properties of source code. Neither verifies native bytes against a contract.
  Two ideas were taken from them: name the object of every assurance by its hash, and say for each
  function which things without a proof its verification relies on.
- **Lean** is where this work began (section 16). It remains welcome for lemmas about specifications,
  and as one of the outside checks of the core.

## 16. Where earlier work lives

- **Ode 0.1** (October 2026): tag `v0.1.0` of this repository. It has a proof kernel for sorted equations
  with structural induction (`KERNEL.md`, 355 lines of Python), proof exporters for word arithmetic, a
  symbolic verifier for a bytecode and for an AArch64 subset that was compared with a processor, content
  addressing with separated domains (`DOMAINS.md`), and a game of maker, verifier and attacker. This
  design takes from it: reliance sets, with the producers of binaries and proofs in no user's set; the
  verifier's own contract; obligations discharged by stage; computed claims; pet names; the game; and the
  launcher that admits a verifier by its hash. Its words "checker" and "certificate" are "verifier" and
  "proof" here.
- **The Lean experiments** (November 11 to 14, 2026): BLAKE3-Servil's repository, fork
  `samshackleton-tech/BLAKE3`, branch `experiment/sam-wide-model`, under `tools/verify/machine/` (`lang/`,
  `one/`, `spec/`, `alg/`, `arm/`, `wide/`). They hold theorems in Lean about the whole hash over a model
  of the processor, with generated proofs. Each function took days. The proofs broke when the code was
  rebuilt. And they depended on about 2,500 solver axioms, which an independent verifier of Lean proofs
  rejects. A verifier built for the purpose does the same work in seconds and lets Bob rely on less.
  `lang/DESIGN.md` there records the decisions of those days. The ones that still bind are in sections
  4, 5 and 11 above.
- **The verifier of binaries** (since November 14, 2026): developed at the same place, in `kcheck/`, up to
  commit `dca7275f`. It moved here on November 17, 2026 and continues here.
