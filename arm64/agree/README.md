# Proving rows of `arm64.tab` against Google DeepMind's `arm64-semantics`

This folder is a standalone Lean 4 package. It proves that four rows of `../arm64.tab` agree with
Google DeepMind's `arm64-semantics` (package `arm64` in `google-deepmind/code-verification` at commit
`b0f729accbc21a0413e7ca4e1da43fa45b5f2e1b`, under Lean 4.34.0).

It imports only the instruction-table parser (`Table.lean`), the instruction interpreter (`Machine.lean`),
and Google DeepMind's `Arm64.Trusted.ISA` (`Decode` and `Eval`).

## What is proved

The table below lists each theorem in `Agree.lean`, the row of `../arm64.tab` it covers, and what the
theorem states for every valid choice of operands and matching starting states.

| Theorem | Row in `arm64.tab` | What it shows |
|---|---|---|
| `ArmAgree.agree_add_rrr` | `add_rrr` (`D = add64(S, P)`) | For all `x0`..`x30` operands `d, s, p`, decoding and running the 32-bit word in Google DeepMind's model writes the same 64-bit sum into `d`, advances `pc` by 4, and leaves every other register, vector lane, flag, and memory byte equal. |
| `ArmAgree.agree_ldr64_sp_fault` | `ldr64_sp` (`D = mem64(on16(sp), N)`) | Whenever the stack pointer is not a multiple of 16, `Ode.exec` returns `none` and Google DeepMind's model raises `.Exception "SP alignment fault"`. |
| `ArmAgree.agree_ldr64_sp` | `ldr64_sp` (`D = mem64(on16(sp), N)`) | Whenever the stack pointer is a multiple of 16 and the 8 bytes at `sp + 8*n` are readable without wrapping past `2^64`, both models load the same 8 little-endian bytes into `d`, advance `pc` by 4, and leave everything else equal. |
| `ArmAgree.agree_eor_v` | `eor_v` (`X = each32(xor32, Y, Z)`) | For all `v0`..`v31` operands `x, y, z`, both models compute the same bitwise XOR across all four 32-bit lanes of the 128-bit vector register and leave everything else equal. |
| `ArmAgree.agree_rev32` | `rev32_8h` (`X = each32(ror32, Y, 16)`) | For all `v0`..`v31` operands `x, y`, Google DeepMind's halfword-swap loop produces the same result as rotating each 32-bit lane right by 16 bits, and leaves everything else equal. |

All five theorems depend only on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`),
with no `sorry`, no `admit`, and no `bv_decide` axioms.

## What else is checked

Because `Table.lean`'s parser (`parseExpr`, `unify`) is marked `partial` and Lean 4.34's `String.toNat?`
is opaque to the Lean kernel, `Agree.lean` states each row's parsed effect as a Lean constant and takes
the register-name lookup results as hypotheses. Two executable tests close that link against the live
files:

- `CheckMain.lean` (`agree-check`) reads `../arm64.tab` through `Ode.readTable`, checks that each of the
  four rows has the exact effect AST used in `Agree.lean`, and checks `Ode.findRow`, `Ode.regOf`,
  `Ode.vecOf`, and `Ode.readInt` across all 31 general registers, all 32 vector registers, and sample
  displacements.
- `test_agree.py` runs `agree-check`, compares more than 100 encoded 32-bit words from `Agree.lean`
  against `../word.py` (both `word.decode` and `word.encode`), and checks `#print axioms` on all five
  theorems.

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
