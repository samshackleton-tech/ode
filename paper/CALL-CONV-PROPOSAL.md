# Proposal: Custom Calling Conventions for Calls Between Ode Functions

*Status: written proposal for review. Nothing in `proof-core/` or `lang/` is changed until this
proposal is approved.*

## 1. Why Change Calls Between Ode Functions

Today, every function in Ode follows the C calling convention of its target processor:
- On x86-64 (System V AMD64): parameters arrive in `rdi, rsi, rdx, rcx, r8, r9`, the return value
  leaves in `rax`, and the called function must preserve `rbx, rbp, r12, r13, r14, r15` (plus `rsp`).
- On AArch64 (AAPCS64): parameters arrive in `x0` through `x7`, the return value leaves in `x0`,
  and the called function must preserve `x19` through `x29` (plus `sp` and `x30`).

Keeping the C calling convention as the default is required at every boundary where Rust or C calls
into Ode, or where Ode calls into legacy code. However, inside a program made of several Ode
functions, forcing every internal helper call to obey the C calling convention adds real cost.

We measured two concrete examples in this repository:

1. **Short-input BLAKE3 hashing on Zen 5 (`blake3-servil-core --features ode-verified`):** At 256 KiB,
   our Lean-verified x86-64 BLAKE3 (`b3l_hashr`, 14 functions) runs at 16.365 GiB/s (98.8% of the
   hand-tuned Rust + assembly library, and 31.6% faster than official BLAKE3 1.8.7). At 64 bytes,
   however, it runs at 0.670 GiB/s (51.4% of the hand-tuned library). For a 64-byte message,
   `b3l_hashr` makes four nested C-convention calls (`b3l_chunk_node`, `b3l_pad`,
   `blake3_servil_compress_in_place_sse41`, and `b3l_node_out`). Each call saves and restores
   callee-saved registers on the stack and shuffles values into the fixed C argument registers.
2. **Small verified helpers in loops (Wave 1 Base64 and DER parsers):** Calling an 18-instruction
   helper like `ode_b64_char_val` (which only touches two scratch registers) inside a loop forces the
   caller on x86-64 or AArch64 to copy live loop variables into callee-saved registers, allocate a
   48-to-64-byte stack frame, save all of them at function entry, and restore them before every
   return.

The priority direction set for Ode is: **make calls from one Ode function to another as fast as
possible; keep C/Rust FFI supported at the boundary without letting C's rules slow down internal
calls.**

---

## 2. A Concrete Example: Before and After

Consider a small helper that maps one ASCII byte to its 6-bit RFC 4648 Base64 value (`0..63`, or
`255` if invalid), called four times per iteration inside a validator loop.

### Today (C calling convention)

The contract says nothing about registers, so the verifier enforces the C calling convention:

```ode
contract ode_b64_char_val(b: number) {
    requires b < 256
    returns b64_val(b)
    trace depends on b
    stack 0
}
```

Even though `ode_b64_char_val` on AArch64 only reads `x0` and writes `x0`, the C calling convention
tells the caller that the call may overwrite every caller-saved register (`x0` through `x18`). So the
caller must save its own pointer, length, loop counter, and intermediate values into callee-saved
registers (`x19`..`x23`), allocate a 48-byte stack frame, store those registers plus `x30` at entry,
and load all six registers back before returning.

### Under this proposal (custom Ode calling convention)

An internal helper may add an explicit `calling` block inside its contract, naming the exact
register for each parameter, the register carrying the return value, and the exact registers the
called function guarantees not to change:

```ode
contract ode_b64_char_val(b: number) {
    requires b < 256
    returns b64_val(b)
    trace depends on b
    stack 0
    calling {
        in b = x9
        out = x10
        preserves x0, x1, x2, x3, x4, x5, x6, x7, x11, x12, x13, x14, x15
    }
}
```

Now look at what happens to the caller:
- The caller keeps its own arguments (`buf` in `x0`, `len` in `x1`) and loop variables (`at` in `x2`,
  `v0` in `x3`, `v1` in `x4`) in ordinary scratch registers across every call to `ode_b64_char_val`.
- Before calling `ode_b64_char_val`, the caller loads one byte straight into `x9` (`ldrb w9, [x0, x2]`),
  calls `bl ode_b64_char_val`, and reads the decoded 6-bit value straight out of `x10`.
- The caller saves **zero** callee-saved general-purpose registers for those live variables.

The table below compares the register-saving work inside `ode_b64_valid_quad` (4 calls to
`ode_b64_char_val`) under today's C calling convention and under the custom `calling` block above.
Cells count instructions or bytes added solely for calling-convention bookkeeping.

| Metric in `ode_b64_valid_quad` (AArch64) | Today (C ABI) | With `calling { ... }` |
|---|---:|---:|
| Callee-saved GPRs spilled to stack (`x19`..`x23`) | 5 registers (40 bytes) | 0 registers (0 bytes) |
| Prologue + epilogue `str`/`ldr` instructions for those GPRs | 10 instructions | 0 instructions |
| Argument-shuffling `mov x0, ...` instructions before 4 calls | 4 instructions | 0 instructions |
| Result-saving `mov x20.., x0` instructions after 4 calls | 4 instructions | 0 instructions |

---

## 3. Proposed Contract Syntax and Rules

A contract without a `calling` block keeps the exact C calling convention of its architecture (100%
backward compatible with every existing contract, proof, and FFI boundary).

A contract with a `calling` block may write up to three lines inside `calling { ... }`:

1. **`in param = reg, ...`** — assigns each contract parameter to a specific general-purpose
   register on the target architecture. Every parameter of the contract must be listed once, and all
   chosen registers must be distinct and must not be the stack pointer (`rsp` / `sp`) or the return
   link register (`x30` on AArch64).
2. **`out = reg`** — names the single general-purpose register carrying the returned number when the
   contract has a `returns` line. It must not be the stack pointer or the AArch64 link register. If
   omitted, it defaults to `rax` (x86-64) or `x0` (AArch64).
3. **`preserves r1, r2, ...`** — lists the exact set of general-purpose registers whose values the
   called function must leave equal to their entry values at every `ret`. Every listed register must
   be valid, distinct from the stack pointer (which is always preserved), and distinct from `out`
   when the contract returns a number. Any general-purpose register not listed in `preserves` (and
   not `rsp`/`sp` or `x30`) is treated by the caller as overwritten by the call.

### Optional Phase 2 Extensions (Not in Phase 1)

Two natural extensions are kept separate so Phase 1 stays tiny:
- **Preserved vector registers (`preserves xmm6, xmm7` / `v8..v15`):** useful when a wide SIMD loop
  calls a small scalar helper without spilling live vector accumulators.
- **Custom link register (`link = x15` on AArch64) and tail calls (`jmp` / `b`):** on AArch64, if a
  leaf helper receives its return address in a chosen register (`x15`, via `adr` + `b`, or via tail
  call `b`), the caller does not even overwrite `x30`, eliminating the caller's entire stack frame
  (`stack 0`!) for non-recursive callers.

---

## 4. Exact Changes to the Verifier and Its Soundness Proof

A key design fact makes Phase 1 remarkably small: `proof-core/Contract.lean` and
`proof-core/Core.lean` **already route all parameter lookups and preserved-register checks through
two helper functions on `Contract`**:

- `Contract.argRegs (c : Contract) : List Nat` (currently `if c.arm64 then argRegsArm else argRegsX86`)
- `Contract.keeps (c : Contract) : List Nat` (currently `if c.arm64 then calleeSavedArm else calleeSavedX86`)

The table below lists every file affected by Phase 1, what changes in that file, and the estimated
size of the change in lines of code.

| File | Change in Phase 1 | Estimated Size |
|---|---|---:|
| `kcheck/ode.py` | Parse optional `calling { in ...; out = ...; preserves ... }` block on contracts | ~45 lines Python |
| `proof-core/statement.py` | Emit `argregs ...`, `retreg N`, `keeps ...` lines into `.statement` when a `calling` block is present; validate register names and disjointness | ~35 lines Python |
| `proof-core/Reader.lean` | Read optional `argregs`, `retreg`, `keeps` lines into `Contract` (defaulting to C ABI when absent) | ~30 lines Lean |
| `proof-core/Contract.lean` | Add three optional fields (`customArgs`, `customRet`, `customKeeps`) to `Contract`; check validity (`validCalling`: all registers `< nreg`, distinct from `RSP`/`LINK`, pairwise distinct `argRegs`, `retReg` not in `keeps`); use `c.retReg` where `0` is currently hardcoded for the returned number | ~35 lines Lean |
| `proof-core/Core.lean` | Replace hardcoded register `0` with `c.retReg` in `symReturn` (return check) and `afterCall` / `afterCallQ` (caller state after a call); check `c.validCalling` at entry | ~25 lines Lean |
| `proof-core/SoundCall.lean` & `SoundTop.lean` | Replace concrete register `0` with `c.retReg` and pass `c.validCalling` where `argRegs` / `keeps` properties were previously proved by `decide` on the fixed C ABI lists | ~60 lines Lean |

### What Does Not Change

- **Bob's reliance set does not grow in any surprising way:** Bob reads the contract of the top-level
  entry point he calls. Any external entry point called from Rust or C has no `calling` block, so it
  keeps the exact C calling convention. Custom `calling` blocks appear only on internal helper
  contracts that Bob's top-level contract never relies on directly (the verifier checks that every
  caller and every callee agree on the callee's `calling` block).
- **Zero changes to the 10 top-level soundness theorem statements in `proof-core/test_sound.py`:**
  all existing C-ABI contracts have `customArgs = none`, `customRet = none`, `customKeeps = none`,
  so they mean byte-for-byte what they mean today.
- **Zero hidden register moves or compiler magic:** the programmer still chooses every register and
  every instruction explicitly. The verifier simply checks that the caller puts arguments where the
  callee's contract expects them, and that the callee preserves every register its contract promises
  to preserve.

### Soundness Invariants Checked by the Verifier

To prevent any soundness hole from malformed custom conventions, `Contract.validCalling` enforces:
1. Every register index in `argRegs`, `retReg`, and `keeps` is strictly less than the machine's
   general-purpose register count (`16` on x86-64, `32` on AArch64).
2. `RSP` is never in `argRegs`, never `retReg`, and never duplicated in `keeps` (stack pointer
   preservation is always enforced separately).
3. On AArch64, `LINK` (`x30`) is never in `argRegs` and never `retReg` (return-address preservation
   is enforced separately in Phase 1).
4. All registers in `argRegs` are pairwise distinct (so two parameters can never alias the same
   register).
5. When `c.givesNumber = true`, `c.retReg` is not in `c.keeps` (a register cannot simultaneously hold
   a newly computed return value and be promised unchanged unless the return value equals the entry
   register, avoiding ambiguity in `afterCall`).
6. In `Core.lean`, the trace-mark check at `ret` checks `c.retReg` (not hardcoded register `0`) when
   `resultFollowsTrace` is true, and `afterCallQ` marks `c.retReg` clean (not hardcoded `0`) when
   `cleanRet` is true.

---

## 5. Planned Verification and Negative Controls (Before Merging Phase 1)

Before any Phase 1 implementation is merged, it will include:
1. **Positive controls (both x86-64 and AArch64):**
   - `ode_b64_char_val` + `ode_b64_valid_quad` with custom `calling`, showing 0 callee-saved GPR
     spills and real-silicon RFC 4648 execution PASS.
   - `b3l_pad` / `b3l_chunk_node` prototype on x86-64 measuring 64-byte BLAKE3 speedup on Zen 5.
2. **Negative controls (must be refused by `odeverify`):**
   - Callee overwrites a register listed in its `preserves` list -> refused at `ret`.
   - Caller passes an argument in C's `rdi`/`x0` when callee's `calling` asks for `r10`/`x9` ->
     refused at `call`/`bl`.
   - Caller reads the return value from `rax`/`x0` when callee returns in `r11`/`x10` -> refused.
   - Malformed `.statement` putting `RSP`, `LINK`, out-of-range register, or duplicate register in
     `argregs` -> refused immediately by `validCalling`.
   - Trace leak: callee returns a value computed from data kept out of the trace in a custom `out`
     register (`r11`/`x10`) -> refused by trace check at `ret`.

---

## 5b. Real C-Boundary Finding Caught During AArch64 Audit: AAPCS64 `d8..d15`

While auditing all AArch64 binaries produced by the Spec-First AI Factory on 24 November, we caught a
concrete gap in the existing C-boundary ABI model in `proof-core/Contract.lean` and
`proof-core/Machine.lean`:

- On AArch64 (AAPCS64, used by both Linux and macOS), the low 64 bits of vector registers `v8..v15`
  (`d8..d15`) are callee-saved alongside general-purpose registers `x19..x29`.
- Today `Contract.keeps` checks `calleeSavedArm = [19..29]` (general-purpose registers only) and
  places no preservation check on `v8..v15`. As a result, a generated AArch64 SIMD routine
  (`chacha20_double_round_4x_arm64`) wrote to `v8` and `v9`, passed `odeverify`, and would have
  clobbered a C or Rust caller's live `d8`/`d9` values.
- Immediate mitigation (already landed): we audited every AArch64 `.ode` file in the repository,
  replaced `v8`/`v9` in `chacha20_double_round_4x_arm64.ode` with caller-saved `v16`/`v17`, and
  added a live hardware `d8..d15` preservation check to `proof-core/test_chacha20.py` and
  `factory/test_factory_native.py`.
- Proposed model fix (bundled with Phase 1 of this proposal): for default C-ABI AArch64 contracts
  (those without a custom `calling` block), forbid writing to `v8..v15` unless saved and restored
  (or track `v8..v15` preservation in `Contract.keepsVec`, defaulting to `[8..15]` on AArch64 C ABI
  and `[]` on x86-64 System V ABI). Custom Ode-to-Ode `calling` blocks may explicitly list vector
  registers to clobber or preserve.

---

## 6. Questions for Review Before Building

1. **Syntax:** Is the explicit `calling { in ...; out = ...; preserves ... }` block inside `contract`
   clear and readable for an auditor, or do you prefer putting register names directly inline in the
   parameter header (for example `contract helper(b in x9: number) -> x10`)?
2. **Scope of Phase 1:** Should we build Phase 1 (custom GPR `in`, `out`, `preserves`, ~230 lines
   across Python and Lean) first and measure the 64-byte BLAKE3 and Base64 speedups before deciding
   whether Phase 2 (preserved vector registers + custom AArch64 link register / tail calls) is worth
   its added Lean lines?
3. **FFI guard:** Should a top-level contract checked without callers (or marked `export`) refuse a
   custom `calling` block by default so a programmer cannot accidentally export a non-C-ABI function
   to Rust or C?
4. **AAPCS64 `d8..d15` fix:** Should we bundle the C-boundary AArch64 `v8..v15` preservation rule
   into Phase 1 immediately (forbidding writes to `v8..v15` on default C-ABI AArch64 contracts unless
   restored)?
