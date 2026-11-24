# Proposal: a model of AArch64 for Ode

A written proposal, 22 November 2026, before anything is built. It asks for one decision, and it marks what was measured, what was read, what is judgment, and what is not known.

**Decided the same day: answer C,** taken in the two steps below. If C proves useful, the table, its comparison with processors and the proof of agreement are to be published as work of independent interest: something people can learn from and use who do not use Ode. So they are built as a package of their own, which names nothing of Ode's verifier or contracts.

## The decision

Ode's theorems are about a model of the processor. For x86-64 that model is Ode's own: a table of instruction forms (`core/x86.tab`) with the meaning of its rows in Lean (`proof-core/Machine.lean`). Which model stands under the theorems for AArch64?

On 11 November the choice for AArch64 was Google DeepMind's `arm64-semantics`. Ode's table and the verifier that steps by it came after that, from 17 November on. So the question is open again, and there are three answers:

- **A.** Google's model, as chosen on 11 November.
- **B.** A table of Ode's own for AArch64, of the same kind as the one for x86-64.
- **C.** B, and beside it a proof in Lean that the rows of that table agree with Google's model. The proof is kept apart from the verifier: nothing that verifies depends on it.

I recommend C, taken in two steps so that its costs are measured before they are promised. C does not build Ode's verifier on Google's model, which is what the choice of 11 November said. If that choice is to stand, the answer is A.

## What was measured and read

Google's `arm64-semantics` (repository `google-deepmind/code-verification`, the checkout of 11 November, `b0f729ac`; Apache-2.0; Lean 4.34.0 there, 4.35.0 on its main branch today; Ode builds with Lean 4.34.1 and no package beyond Lean's own):

| Part | Files | Lines |
|---|---:|---:|
| `Arm64/Trusted/ISA/` (the folder's name is Google's): decoder, evaluator, state | 7 | 7,166 |
| all of `Arm64/Trusted/`: adds `Object`, `Process` (the loading of a static Linux program), `Spec`, `Surface` and `Syscalls` | 61 | 16,767 |
| all of `Arm64/` | 134 | 50,610 |
| `ProofLib/`: the logic their proofs are written in | 315 | 184,747 |

Ode for x86-64 today:

| Part | Files | Lines |
|---|---:|---:|
| the machine: `core/x86.tab`, `Machine.lean`, `Table.lean`, `Contract.lean` | 4 | 1,801 |
| the verifier: `Core.lean`, `Reader.lean`, `Arithmetic.lean` | 3 | 4,471 |
| the proofs that the verifier is sound (`Sound*.lean`) | 18 | 20,388 |

Three things read in Google's files:

1. The instructions the trial used have constructors in `Syntax.lean` and cases in `Eval.lean`: `eor`, `rev32`, `ushr`, `shl`, `sli` and `ld1`/`st1` on vector registers; `smulh`, `adds`, `cbz`, conditional select and a load that moves its base register on general registers. I found them by name or by their encoding. I did not read the evaluators through or run them. SVE is not modeled (`Decode.lean` says so), and nothing in the folder names SME.
2. Its trace (`TraceEvent` in `State.lean`) records bytes written by system calls and changes of files. It does not record which instructions ran or which addresses they touched. Ode's theorem about what an observer sees (`verify_all_trace`) is about those addresses.
3. Its top-level statements are about a whole Linux process (`ElfRunsTo` in `Process/`). Ode's are about one function under a contract.

One thing read in Ode's files: the model and the proofs are written for x86-64. `Machine.lean` has sixteen general registers, two flags, and a call that stores the return address below the stack pointer. The proofs name the stack pointer 296 times and the registers that carry arguments 146 times.

## The three answers

### A. Google's model

- What it gives: an account of AArch64 that others wrote, maintain and use. A reader who already relies on it for other work adds nothing to what he relies on. An error anybody finds in it is found for everybody.
- What a reader of the machine reads: the 7,166 lines of `Arm64/Trusted/ISA/`, in place of a table of a few hundred lines.
- What has to be built: the verifier's steps for AArch64, each proved against Google's evaluator; a definition of the trace of addresses, either inside Google's files or laid over them; a build that takes their repository and follows their Lean version.
- Not known: how much of Ode's 20,388 lines of proof carries over when the machine's state is Google's (bit vectors) and not Ode's (whole numbers). I expect little. That is a judgment; nothing was tried.

### B. A table of Ode's own

- What it gives: one way of saying a machine and one verifier for both processors; the trace of addresses from the start, since the table's meaning already records it; rows compared with processors, as `core/cross.py` does for x86-64.
- What a reader of the machine reads: `core/arm64.tab` and a machine file for AArch64. By the size of the x86-64 files (306 and 709 lines) I guess a few hundred lines each for a first set of rows. That is a guess.
- What has to be built: the table; the machine file; `cross.py` for AArch64 (today it runs on x86-64 Linux only); and the change that lets `Core.lean` and its proofs serve two machines.
- Not known: the size of that last change. It is the largest cost of B and of C, and nothing has measured it.
- What it gives up: the account of AArch64 is ours alone to write and to defend. A reader who relies on Google's model has to read our table as well, or rely on the comparison with processors.

### C. B, and a proof of agreement with Google's model

- What it adds to B: a reader who relies on Google's model gets a theorem that each row of our table does what Google's evaluator does to the same instruction word. He need not read our table's encodings. A reader who does not rely on Google's model is where he is under B: the proof is outside what verifies.
- Not known: whether such a proof can be had at a cost worth paying. The two models hold state in different forms, and not one row has been tried. If it cannot, C falls back to B.

## Why C, in two steps

These are judgments.

1. Under A the theorem about traces has no ground to stand on until Google's model is changed or wrapped. Under B and C it comes with the table.
2. Ode aims at one mechanism where one serves. A second model of another kind beside the table would be a second way of saying a machine, with its own reader, proofs and upkeep.
3. A reader who reads the machine reads far less under B and C.
4. C keeps Google's model as a second route to confidence for those who rely on it, which B alone gives up.

Against C: we take on writing an account of AArch64, which the choice of 11 November meant to spare us, and the proof of agreement may prove too costly.

The two steps:

1. **Measure.** About twenty rows (`mov`, `add`, `sub`, `ldr`/`str`, `bl`/`ret`, `ld1`/`st1`, `eor`, `rev32`), a machine file for them, and `cross.py` on an Apple M6 and an AmpereOne. Verify one function that calls another through `bl` and the hash step of the trial (`eor` and `rev32` on four lanes), and refuse changed versions of both. Count the lines of `Core.lean` and of the proofs that had to change. Prove one row's agreement with Google's evaluator, to learn what such a proof costs.
2. **Decide again with those numbers:** go on to C, stay at B, or turn to A.

After step 1 the work returns to the rest of the x86-64 hash, with the model of calls and registers that serves both processors.

## What the verifier's code fixes to x86-64 today

Read in the code; the list may not be complete.

1. **Registers and calls.** Sixteen general registers with the stack pointer among them (`Machine.lean`); the registers that carry arguments (`argRegs`, in `Contract.lean`) and those a called function gives back (`calleeSaved`, in `Machine.lean`) are C's convention. `call` stores the return address in memory. AArch64 has thirty-one general registers and a stack pointer apart from them; `bl` puts the return address in a register. A contract that names its own registers for arguments and results, as `ODE.md` section 5 proposes, would take the convention out of the verifier for both processors.
2. **Flags.** The table has a zero flag and a carry flag. The trial's AArch64 code uses conditions on overflow as well (`b.vs`), and tested arithmetic on x86-64 needs the overflow flag too (`jo`).
3. **A load that moves its base.** `ldr w2, [x0], #4` changes two registers. A row's effect is already a list of statements (`push` has two), so the table's language needs nothing new for it.
4. **Vectors.** The table has rows on four lanes and on sixteen lanes of 32 bits. NEON has four lanes; the table's lane-wise operations (`each32` with `xor32` or `ror32`) say what `eor` and a rotate do there.
5. **Encoding.** Every AArch64 instruction is four bytes, so the part of the table that says how a row is written in bytes should be simpler than for x86-64. That is an expectation.

*Ode stands for Obviously Didn't Explode.*
