# Proposal: Verifying the First AArch64 Functions in Ode

Written proposal before building the AArch64 formal model (22 November 2026). Takes up Sam's November 11 choice of Google DeepMind's `arm64-semantics` in light of Ode's table-driven verifier built since November 17 (`core/x86.tab` + `proof-core/`). Nothing proposed here is built yet; awaits Sam's decision.

## Summary and recommendation

We recommend **Option C (Hybrid)**:

1. Define Ode's AArch64 instructions in a small table (`core/arm64.tab`, roughly 250 to 350 lines for the first milestone) paired with a small AArch64 machine model (`proof-core/MachineArm64.lean`, roughly 600 to 700 lines) that plugs into the **same** table interpreter (`Table.lean`), specification semantics (`Contract.lean`), proof format, and Lean verifier (`Core.lean`) used for x86-64.
2. Validate every row of `core/arm64.tab` in **two independent ways**:
   - **Hardware cross-check (`cross.py`):** assemble random instances of each row and run them on real AArch64 silicon (Apple Silicon and AmpereOne), comparing every architectural effect against the table.
   - **Optional Lean equivalence against Google's `arm64-semantics`:** prove (in a separate optional module, never required by `odeverify`) that each row of `core/arm64.tab` decodes the same 32-bit word and produces the same register/memory transition as Google DeepMind's `Arm64/Trusted/ISA/{Decode,Eval}.lean`.

This keeps Bob's minimal reliance set small, preserves Ode's architectural constant-time theorem (`verify_all_trace`), keeps `odeverify` free of external Lean dependencies, and still gives an auditor who already relies on Google's `arm64-semantics` an independent formal route to confidence in our AArch64 instruction rules.

## What we measured in Google's `arm64-semantics`

Inspecting `google-deepmind/code-verification` (`arm64-semantics`, local checkout `b0f729ac`, Apache-2.0; Lean `v4.34.0` locally, `v4.35.0` upstream; Ode uses Lean `v4.34.1` with zero external Lean packages):

| Component | Files | Lines | Notes |
|---|---:|---:|---|
| Google `Arm64/Trusted/ISA/` (upstream folder name) | 7 | 7,166 | `Eval.lean` 3,072, `Decode.lean` 1,299, `Float.lean` 793, `State.lean` 689, `Syntax.lean` 631, `Memory.lean` 397, `Semantics.lean` 285 |
| Google full `Arm64/Trusted/` (upstream folder name) | 61 | 16,767 | Adds Linux ELF loader, POSIX syscalls, Rust/C ABI, separation logic |
| Google `Arm64/` total | 134 | 50,610 | Includes lemmas and helpers |
| Google `ProofLib/` total | 315 | 184,747 | Symbolic execution and Hoare/separation logic |
| Ode x86-64 machine + table + contract (`Machine.lean`, `Table.lean`, `Contract.lean`, `core/x86.tab`) | 4 | 1,801 | Plus `Core.lean` 4,028, `Reader.lean` 228, `Arithmetic.lean` 215 (total 6,272 lines with comments) |

Four technical findings from reading Google's `Arm64/Trusted/ISA/` directly:

1. **Good NEON and scalar coverage, no SME2:** `Syntax.lean` covers AArch64 scalar instructions (`mul`, `smulh`, `adds`, `cbz`, `cbnz`, `condSelect` / `cset`, `ldr`/`str` with post-indexing) and 128-bit NEON (`simdThreeSame`, `simdTwoRegMisc`, `simdImmShift`, `simdTbl`, `simdExt`, `simdPermute`, `simdLdSt1Multi`, `cryptoXar`). It does not cover SME2.
2. **No architectural PC/address trace:** `TraceEvent` in `State.lean` records Linux syscall I/O (`writeByte`, `fileChanged`, `userDefined`), not instruction addresses or memory addresses touched. Proving Ode's constant-time property (`verify_all_trace`) directly over their `Step` relation would require modifying their core `State` and `Eval` files anyway.
3. **Linux ELF process orientation:** their top-level semantics targets whole Linux ELF binaries (`ElfRunsTo`) with POSIX syscalls and fixed `BitVec 64` memory, whereas Ode verifies relocatable functions against declarative contracts on both Linux ELF and macOS Mach-O.
4. **Incompatible with Ode's table-driven verifier and future self-verification:** `Core.lean` executes instruction effects generically through `Table.lean` (191 lines) and checks small separate proof files in milliseconds (`ode_sum` in 3.6 ms, `p16` in 109 ms). Driving a proof-file verifier directly off 3,072 lines of `BitVec` evaluators in `Eval.lean` would either duplicate the verifier or drag 184,747 lines of `ProofLib` into the build, and would block writing the verifier in Ode itself or checking it in Metamath Zero.

## Three options compared

### Option A: Build Ode's AArch64 verifier directly on Google's `arm64-semantics`

- **Pros:** reuses an existing, externally audited AArch64 decoder and evaluator for 128-bit NEON and scalar code.
- **Cons:** adds at least 7,166 lines of external Lean code (including 793 lines of IEEE floating-point semantics Ode never uses) to every Bob's reliance set; lacks architectural PC/address traces for `verify_all_trace` (requiring a maintained fork); cannot share `Table.lean` or `Core.lean` cleanly with x86-64; couples Ode's Lean toolchain to an external repository; cannot be transliterated into an Ode-written verifier or a small Metamath Zero kernel.

### Option B: Standalone table `core/arm64.tab` + `MachineArm64.lean` (same architecture as x86-64)

- **Pros:** tiny reading list (~250–350 lines for `core/arm64.tab` plus ~600–700 lines for `MachineArm64.lean`); one verifier (`Core.lean` + `Table.lean`) for both x86-64 and AArch64; full `verify_all_trace` constant-time theorem from day one; hardware `cross.py` directly validates every row on Apple Silicon and AmpereOne; zero external Lean packages; directly portable to an Ode-written verifier and Metamath Zero.
- **Cons:** does not use Google's `arm64-semantics`, so an auditor who already relies on Google's model still has to audit `core/arm64.tab` (or rely on hardware `cross.py`).

### Option C (Recommended): `core/arm64.tab` + optional equivalence proof against Google's `arm64-semantics`

- **Pros:** keeps every benefit of Option B (tiny reliance set, one shared `Core.lean` verifier, `verify_all_trace`, zero external packages in `odeverify`, self-verifying Ode verifier and MM0 compatibility), **and** adds an independent optional Lean module (`arm64-bridge/`, outside `odeverify`'s build) that proves each row of `core/arm64.tab` matches Google's `Arm64/Trusted/ISA/{Decode,Eval}.lean`.
- **Reliance sets under Option C:**
  - **Bob (minimal reader):** reads `core/arm64.tab` + `MachineArm64.lean` + `Core.lean` (plus hardware `cross.py` receipts). Does not depend on Google's repository at all.
  - **Bob (Google-semantics user):** checks the optional bridge theorem showing `core/arm64.tab` agrees with Google's `Arm64/Trusted/ISA` on every instruction used, without auditing our 32-bit bit-pattern encodings by hand.
- **Cost:** writing the optional bridge proofs adds effort after the table works, bounded to the ~30–50 rows Ode actually uses rather than all of AArch64.

## What changes in `proof-core/` to support two processors (`2 >> 1`)

Our two-target trial (`ode_quad32`, `ode_all_zero`, `mix16`, `mix12`, and checked 64-bit arithmetic) identified the exact processor differences that must stop being hard-coded to x86-64:

1. **Registers and call-return mechanics:** x86-64 has 16 GPRs (`rsp` = stack, `call` pushes return address to memory, `ret` pops it); AArch64 has 31 GPRs (`x0`–`x30`, zero register `xzr`, `sp` separate and 16-byte aligned at loads/stores, `bl` writes the return address to `x30`, `ret` jumps to `x30`). `Core.lean` currently hard-codes x86 `argRegs := [7, 6, 2, 1, 8, 9]` and `calleeSaved := [3, 5, 12, 13, 14, 15]`. Making register sets, argument/result registers, and preserved registers part of the target/contract removes C ABI assumptions from the verifier core and serves Ode-to-Ode calls on both processors.
2. **Flags and branchless predicates:** x86-64 `x86.tab` tracks `zf` and `cf`; AArch64 needs `N, Z, C, V` (for `subs`/`b.ne`, `adds`/`b.vs`, `cmp`/`cset`). `V` (signed overflow) is also needed on x86-64 (`imul`/`add` + `jo`) for checked arithmetic in the Ode-written verifier.
3. **Addressing modes:** AArch64 post-indexed loads (`ldr w2, [x0], #4`) update both a destination register and the base pointer in one instruction. `Table.lean` already supports multi-statement row effects (`D = mem32(B, 0); B = add64(B, 4)`), so no new effect-language mechanism is needed.
4. **Vector widths:** x86-64 uses 128-bit `xmm` (4 lanes) and 512-bit `zmm` (16 lanes); AArch64 NEON uses 32 × 128-bit `v0`–`v31` (4 lanes of 32-bit words). The existing 4-lane primitives (`each32(xor32, ...)`, `each32(ror32, ...)`, `mem128`) already match NEON's lane equations.
5. **Fixed 32-bit instruction encoding:** AArch64 instructions are uniformly 4 bytes (no variable-length REX/VEX/EVEX prefixes), which makes `core/arm64.tab` and its encoder/decoder substantially simpler than x86-64's.

## Proposed first Arm64 verification milestones (before `b3l_wide32`)

Once Sam approves the option:

1. **Milestone A1 (`arm_sum` + `arm_mix16`):** ~20 rows in `core/arm64.tab` (`mov`, `add`, `sub`, `ldr`/`str`, `bl`/`ret`, `ld1`/`st1`, `eor`, `rev32`), `MachineArm64.lean`, hardware `cross.py` on Apple Silicon, and Lean `odeverify` approving `arm_sum` (calling `arm_third` via `bl`/`x30`) and `arm_mix16` (`eor` + `rev32` on 4 lanes) while refusing false mutants.
2. **Milestone A2 (`arm_all_zero`):** add `cbz`/`cbnz`, `subs`, `b.ne`, `orr`, `cmp`, `cset`, and verify `arm_all_zero` (both early-exit and branchless OR-accumulator) on AArch64 beside x86-64.
3. **Milestone A3 (optional bridge):** prove equivalence of the ~30 used rows of `core/arm64.tab` against Google's `Arm64/Trusted/ISA/{Decode,Eval}.lean` in a separate optional Lake package.
4. **Then** return to `b3l_wide32` and the remaining x86-64 hash functions, carrying the cleaner target-parametric call/register model into both processors.
