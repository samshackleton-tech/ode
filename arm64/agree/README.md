# Proving rows of `arm64.tab` against Google DeepMind's `arm64-semantics`

This folder is a standalone Lean 4 package. It proves that **all 47 of the 47 rows** of `../arm64.tab`
agree with Google DeepMind's `arm64-semantics` (package `arm64` in `google-deepmind/code-verification` at
commit `b0f729accbc21a0413e7ca4e1da43fa45b5f2e1b`, under Lean 4.34.0).

It imports only the instruction-table parser (`Table.lean`), the instruction interpreter (`Machine.lean`),
and Google DeepMind's `Arm64.Trusted.ISA` (`Decode` and `Eval`).

## What is proved

The table below lists all 49 theorems in `Agree.lean` (one per row of `../arm64.tab`, plus separate
misaligned-stack fault theorems for `ldr64_sp` and `str64_sp`), the row each theorem covers, and what it
states for every valid choice of operands and matching starting states.

| Theorem | Row in `arm64.tab` | What it shows |
|---|---|---|
| `ArmAgree.agree_nop` | `nop` (`nothing`) | Advances `pc` by 4 and leaves every register, vector lane, flag, and memory byte equal. |
| `ArmAgree.agree_mov_ri` | `mov_ri` (`D = I`) | For all `x0`..`x30` destination `d` and 16-bit immediate `imm`, `MOVZ Xd, #imm` writes `imm` into `d`, advances `pc` by 4, and leaves everything else equal. |
| `ArmAgree.agree_mov32_ri` | `mov32_ri` (`D = I`) | For all `w0`..`w30` destination `d` and 16-bit immediate `imm`, `MOVZ Wd, #imm` writes zero-extended `imm` into `d`, advances `pc` by 4, and leaves everything else equal. |
| `ArmAgree.agree_mov_rr` | `mov_rr` (`D = S`) | For all `x0`..`x30` operands `d, s`, `ORR Xd, XZR, Xs` copies `s` into `d`, advances `pc` by 4, and leaves everything else equal. |
| `ArmAgree.agree_add_rri` | `add_rri` (`D = add64(S, I)`) | For all `x0`..`x30` operands `d, s` and 12-bit immediate `imm`, `ADD Xd, Xs, #imm` writes the 64-bit sum into `d`, advances `pc` by 4, and leaves everything else equal. |
| `ArmAgree.agree_sub_rri` | `sub_rri` (`D = sub64(S, I)`) | For all `x0`..`x30` operands `d, s` and 12-bit immediate `imm`, `SUB Xd, Xs, #imm` writes the 64-bit difference into `d`, advances `pc` by 4, and leaves everything else equal. |
| `ArmAgree.agree_add_rrr` | `add_rrr` (`D = add64(S, P)`) | For all `x0`..`x30` operands `d, s, p`, `ADD Xd, Xs, Xp` writes the same 64-bit sum into `d`, advances `pc` by 4, and leaves everything else equal. |
| `ArmAgree.agree_sub_rrr` | `sub_rrr` (`D = sub64(S, P)`) | For all `x0`..`x30` operands `d, s, p`, `SUB Xd, Xs, Xp` writes the same 64-bit difference into `d`, advances `pc` by 4, and leaves everything else equal. |
| `ArmAgree.agree_add_sp` | `add_sp` (`sp = add64(sp, I)`) | For every 12-bit immediate `imm`, `ADD SP, SP, #imm` updates `sp` to `(sp + imm) mod 2^64`, advances `pc` by 4, and leaves everything else equal. |
| `ArmAgree.agree_sub_sp` | `sub_sp` (`sp = sub64(sp, I)`) | For every 12-bit immediate `imm`, `SUB SP, SP, #imm` updates `sp` to `(sp - imm) mod 2^64`, advances `pc` by 4, and leaves everything else equal. |
| `ArmAgree.agree_add_of_sp` | `add_of_sp` (`D = add64(sp, I)`) | For all `x0`..`x30` destination `d` and 12-bit immediate `imm`, `ADD Xd, SP, #imm` writes `(sp + imm) mod 2^64` into `d`, advances `pc` by 4, and leaves everything else equal. |
| `ArmAgree.agree_ldr64` | `ldr64` (`D = mem64(B, N)`) | For all `x0`..`x30` operands `d, b` and 12-bit scaled offset `8*n`, when `b + 8*n + 8 <= 2^64` and readable, both models load the same 8 little-endian bytes into `d`. |
| `ArmAgree.agree_str64` | `str64` (`mem64(B, N) = S`) | For all `x0`..`x30` operands `s, b` and 12-bit scaled offset `8*n`, when `b + 8*n + 8 <= 2^64` and writable, both models store the same 8 little-endian bytes of `s`. |
| `ArmAgree.agree_ldr32` | `ldr32` (`D = low32(mem32(B, N))`) | For all `x0`..`x30` operands `d, b` and 12-bit scaled offset `4*n`, when `b + 4*n + 4 <= 2^64` and readable, both models load the same zero-extended 32-bit word into `d`. |
| `ArmAgree.agree_str32` | `str32` (`mem32(B, N) = low32(S)`) | For all `x0`..`x30` operands `s, b` and 12-bit scaled offset `4*n`, when `b + 4*n + 4 <= 2^64` and writable, both models store the same low 4 little-endian bytes of `s`. |
| `ArmAgree.agree_ldrb` | `ldrb` (`D = mem8(B, N)`) | For all `x0`..`x30` operands `d, b` and 12-bit byte offset `n`, when `b + n < 2^64` and readable, both models load the same zero-extended byte into `d`. |
| `ArmAgree.agree_strb` | `strb` (`mem8(B, N) = low8(S)`) | For all `x0`..`x30` operands `s, b` and 12-bit byte offset `n`, when `b + n < 2^64` and writable, both models store the same low 8 bits of `s`. |
| `ArmAgree.agree_ldr64_sp_fault` | `ldr64_sp` (`D = mem64(on16(sp), N)`) | Whenever `sp` is not a multiple of 16, `Ode.exec` returns `none` and Google DeepMind's model raises `.Exception "SP alignment fault"`. |
| `ArmAgree.agree_ldr64_sp` | `ldr64_sp` (`D = mem64(on16(sp), N)`) | Whenever `sp` is a multiple of 16 and the 8 bytes at `sp + 8*n` are readable without wrapping past `2^64`, both models load the same 8 little-endian bytes into `d`. |
| `ArmAgree.agree_str64_sp_fault` | `str64_sp` (`mem64(on16(sp), N) = S`) | Whenever `sp` is not a multiple of 16, `Ode.exec` returns `none` and Google DeepMind's model raises `.Exception "SP alignment fault"`. |
| `ArmAgree.agree_str64_sp` | `str64_sp` (`mem64(on16(sp), N) = S`) | Whenever `sp` is a multiple of 16 and the 8 bytes at `sp + 8*n` are writable without wrapping past `2^64`, both models store the same 8 little-endian bytes of `s`. |
| `ArmAgree.agree_cmp_rr` | `cmp_rr` (`zf = equal(S, P); cf = below(S, P)`) | For all `x0`..`x30` operands `s, p`, `SUBS XZR, Xs, Xp` sets `PSTATE.Z = zf` and `PSTATE.C = !cf`, advances `pc` by 4, and leaves registers, vectors, and memory equal. |
| `ArmAgree.agree_cmp_ri` | `cmp_ri` (`zf = equal(S, I); cf = below(S, I)`) | For all `x0`..`x30` operand `s` and 12-bit immediate `imm`, `SUBS XZR, Xs, #imm` sets `PSTATE.Z = zf` and `PSTATE.C = !cf`, advances `pc` by 4, and leaves registers, vectors, and memory equal. |
| `ArmAgree.agree_b` | `b` (`jump I`) | Takes the signed 26-bit PC-relative jump to the same target address and leaves every register, vector lane, flag, and memory byte equal. |
| `ArmAgree.agree_b_eq` | `b_eq` (`jump I if zf`) | Takes the signed 19-bit PC-relative jump on the exact same states (`PSTATE.Z = zf = true`) and falls through by 4 bytes otherwise. |
| `ArmAgree.agree_b_ne` | `b_ne` (`jump I if not zf`) | Takes the signed 19-bit PC-relative jump on the exact same states (`PSTATE.Z = zf = false`) and falls through by 4 bytes otherwise. |
| `ArmAgree.agree_b_hs` | `b_hs` (`jump I if not cf`) | Under `PSTATE.C = !cf`, `B.CS` (`B.HS`) takes the signed 19-bit PC-relative jump on the exact same states as `jump I if not cf` and falls through by 4 bytes otherwise. |
| `ArmAgree.agree_b_lo` | `b_lo` (`jump I if cf`) | Under `PSTATE.C = !cf`, `B.CC` (`B.LO`) takes the signed 19-bit PC-relative jump on the exact same states as `jump I if cf` and falls through by 4 bytes otherwise. |
| `ArmAgree.agree_bl` | `bl` (`call I link x30`) | `Ode.afterCall` and `BL` both write `pc + 4` into `x30` (`lr`), jump `pc` to the callee entry address, and leave every other register, vector lane, flag, and memory byte equal. |
| `ArmAgree.agree_ret` | `ret` (`return x30`) | `Ode.exec` (`.returned`) and `RET X30` both set `pc` to the value of `x30` and leave every register, vector lane, flag, and memory byte equal. |
| `ArmAgree.agree_ld1_4s` | `ld1_4s` (`X = mem128(B, 0)`) | For all `v0`..`v31` destination `x` and `x0`..`x30` base `b`, when `b + 16 <= 2^64` and readable, both models load the same four 32-bit little-endian lanes into `x`. |
| `ArmAgree.agree_st1_4s` | `st1_4s` (`mem128(B, 0) = X`) | For all `v0`..`v31` source `x` and `x0`..`x30` base `b`, when `b + 16 <= 2^64` and writable, both models store the same 16 little-endian bytes from the four lanes of `x`. |
| `ArmAgree.agree_eor_v` | `eor_v` (`X = each32(xor32, Y, Z)`) | For all `v0`..`v31` operands `x, y, z`, both models compute the same bitwise XOR across all four 32-bit lanes and leave everything else equal. |
| `ArmAgree.agree_orr_v` | `orr_v` (`X = each32(or32, Y, Z)`) | For all `v0`..`v31` operands `x, y, z`, both models compute the same bitwise OR across all four 32-bit lanes and leave everything else equal. |
| `ArmAgree.agree_add_4s` | `add_4s` (`X = each32(add32, Y, Z)`) | For all `v0`..`v31` operands `x, y, z`, both models compute the same lane-wise 32-bit wrapping sum across all four lanes and leave everything else equal. |
| `ArmAgree.agree_rev32` | `rev32_8h` (`X = each32(ror32, Y, 16)`) | For all `v0`..`v31` operands `x, y`, Google DeepMind's halfword-swap loop produces the same result as rotating each 32-bit lane right by 16 bits. |
| `ArmAgree.agree_ushr_4s` | `ushr_4s` (`X = each32(shr32, Y, I)`) | For all `v0`..`v31` operands `x, y` and shift encoding `i = 0..31` (`I = 32 - i`), both models compute the same unsigned 32-bit right shift across all four lanes. |
| `ArmAgree.agree_shl_4s` | `shl_4s` (`X = each32(shl32, Y, I)`) | For all `v0`..`v31` operands `x, y` and shift `i = 0..31`, both models compute the same 32-bit left shift across all four lanes. |
| `ArmAgree.agree_lsl_ri` | `lsl_ri` (`D = shl64(S, I)`) | For all `x0`..`x30` operands `d, s` and shift `I = 1..63` (`UBFM Xd, Xs, #64-I, #63-I`), both models write `(s << I) mod 2^64` into `d`. |
| `ArmAgree.agree_fmov_d` | `fmov_d` (`X = lanes_of64(S)`) | For all `v0`..`v31` destination `x` and `x0`..`x30` source `s`, `FMOV Dx, Xs` writes the two 32-bit halves of `s` into lanes 0 and 1 of `x` and zeroes lanes 2 and 3. |
| `ArmAgree.agree_uzp1_4s` | `uzp1_4s` (`X = lanes(Y.0, Y.2, Z.0, Z.2)`) | For all `v0`..`v31` operands `x, y, z`, `UZP1 Vx.4S, Vy.4S, Vz.4S` packs even 32-bit lanes `(Y.0, Y.2, Z.0, Z.2)`. |
| `ArmAgree.agree_uzp2_4s` | `uzp2_4s` (`X = lanes(Y.1, Y.3, Z.1, Z.3)`) | For all `v0`..`v31` operands `x, y, z`, `UZP2 Vx.4S, Vy.4S, Vz.4S` packs odd 32-bit lanes `(Y.1, Y.3, Z.1, Z.3)`. |
| `ArmAgree.agree_zip1_4s` | `zip1_4s` (`X = lanes(Y.0, Z.0, Y.1, Z.1)`) | For all `v0`..`v31` operands `x, y, z`, `ZIP1 Vx.4S, Vy.4S, Vz.4S` interleaves low 32-bit lanes `(Y.0, Z.0, Y.1, Z.1)`. |
| `ArmAgree.agree_zip2_4s` | `zip2_4s` (`X = lanes(Y.2, Z.2, Y.3, Z.3)`) | For all `v0`..`v31` operands `x, y, z`, `ZIP2 Vx.4S, Vy.4S, Vz.4S` interleaves high 32-bit lanes `(Y.2, Z.2, Y.3, Z.3)`. |
| `ArmAgree.agree_zip1_2d` | `zip1_2d` (`X = lanes(Y.0, Y.1, Z.0, Z.1)`) | For all `v0`..`v31` operands `x, y, z`, `ZIP1 Vx.2D, Vy.2D, Vz.2D` packs low 64-bit halves `(Y.0, Y.1, Z.0, Z.1)`. |
| `ArmAgree.agree_zip2_2d` | `zip2_2d` (`X = lanes(Y.2, Y.3, Z.2, Z.3)`) | For all `v0`..`v31` operands `x, y, z`, `ZIP2 Vx.2D, Vy.2D, Vz.2D` packs high 64-bit halves `(Y.2, Y.3, Z.2, Z.3)`. |
| `ArmAgree.agree_ext_4` | `ext_4` (`X = lanes(Y.1, Y.2, Y.3, Z.0)`) | For all `v0`..`v31` operands `x, y, z`, `EXT Vx.16B, Vy.16B, Vz.16B, #4` extracts 32-bit lanes `(Y.1, Y.2, Y.3, Z.0)`. |
| `ArmAgree.agree_ext_8` | `ext_8` (`X = lanes(Y.2, Y.3, Z.0, Z.1)`) | For all `v0`..`v31` operands `x, y, z`, `EXT Vx.16B, Vy.16B, Vz.16B, #8` extracts 32-bit lanes `(Y.2, Y.3, Z.0, Z.1)`. |
| `ArmAgree.agree_ext_12` | `ext_12` (`X = lanes(Y.3, Z.0, Z.1, Z.2)`) | For all `v0`..`v31` operands `x, y, z`, `EXT Vx.16B, Vy.16B, Vz.16B, #12` extracts 32-bit lanes `(Y.3, Z.0, Z.1, Z.2)`. |

All 49 theorems depend only on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`),
with no `sorry`, no `admit`, and no `bv_decide` axioms.

## What else is checked

Because `Table.lean`'s parser (`parseExpr`, `unify`) is marked `partial` and Lean 4.34's `String.toNat?`
is opaque to the Lean kernel, `Agree.lean` states each row's parsed effect as a Lean constant and takes
the register-name lookup results as hypotheses. Two executable tests close that link against the live
files:

- `CheckMain.lean` (`agree-check`) reads `../arm64.tab` through `Ode.readTable`, checks that the table
  has 47 rows and that every single row has the exact effect AST used in `Agree.lean`, and checks
  `Ode.findRow`, `Ode.regOf`, `Ode.vecOf`, and `Ode.readInt` across all 31 general registers, all 32
  vector registers, sample displacements, immediates, shifts, and signed branch offsets.
- `test_agree.py` runs `agree-check`, compares encoded 32-bit words for all 47 rows against `../word.py`
  (both `word.decode` and `word.encode`, verifying the proved set equals the full set of rows in
  `arm64.tab`), and checks `#print axioms` on all 49 theorems.

## Known differences between the two models

- **64-bit address wraparound on loads:** Google DeepMind's `read64` wraps `addr + k` modulo `2^64` for
  each byte `k = 0..7`, while `Ode.load` treats addresses as natural numbers without wraparound.
  `agree_ldr64_sp` therefore assumes `sp + 8*n + 8 <= 2^64`.
- **Lean version:** this package uses Lean 4.34.0 to match Google DeepMind's `arm64` package, while the
  parent repository's Lean proofs use Lean 4.34.1. `Table.lean` and `Machine.lean` build cleanly under
  both versions.

## How to build and test

```
cd arm64/agree
lake build
python3 test_agree.py
```

The first `lake build` fetches Google DeepMind's `code-verification` repository at the pinned commit and
builds its zero-dependency `arm64` library (`Arm64.Trusted.*`), then builds `Table`, `Machine`, `Agree`,
and `agree-check`.
