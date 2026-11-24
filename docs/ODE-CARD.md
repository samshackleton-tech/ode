# Ode Reference Card

A compact guide to writing and verifying x86-64 and AArch64 functions in Ode. Every example in this
card is checked automatically by `proof-core/test_card.py` against the Lean 4 verifier `odeverify`.

## 1. Workflow

Use `lang/ode_tool.py` to compile, search for a proof, verify with `odeverify`, and check performance
advice in one command:

```sh
python3 lang/ode_tool.py check   FILE.ode FILE.spec [--include DEFS.spec] [--arch ARCH] [--trace] [--json]
python3 lang/ode_tool.py refute  FILE.ode FILE.spec [--include DEFS.spec]      # fast concrete bug search (no Lean)
python3 lang/ode_tool.py advise  FILE.ode [--spec FILE.spec] [--arch ARCH] [--trace]
python3 lang/ode_tool.py compare A.ode B.ode [--spec FILE.spec] [--arch ARCH] [--trace]
python3 lang/ode_tool.py serve                                                 # persistent JSON-lines worker on stdin
```

Every `check` run gives one of four outcomes: `shown` (accepted by `odeverify`), `refused` (rejected by
`odeverify`), `FALSE` (a concrete input was found where the code disagrees with the contract), or
`no proof found` (the prover stopped; check loop `place { ... }` invariants or diagnostics).

## 2. Registers and Calling Conventions

Each row in the table below lists the ABI role, the x86-64 System V registers, and the AArch64 AAPCS64
registers for that role.

| Role | x86-64 (System V) | AArch64 (AAPCS64) |
|---|---|---|
| Argument registers (in order) | `rdi`, `rsi`, `rdx`, `rcx`, `r8`, `r9` | `x0`, `x1`, `x2`, `x3`, `x4`, `x5`, `x6`, `x7` |
| Return value | `rax` | `x0` |
| Caller-saved (scratch) | `rax`, `rcx`, `rdx`, `rsi`, `rdi`, `r8`–`r11`, `xmm`/`zmm`, `k0`–`k7` | `x0`–`x18`, `v0`–`v31` |
| Callee-saved (must restore) | `rbx`, `rbp`, `r12`–`r15` | `x19`–`x28`, `x29`, `x30` (link register `lr`) |
| Stack pointer & alignment | `rsp` (16-byte aligned before `call`; `call` pushes 8-byte return addr) | `sp` (16-byte aligned at every `ldr`/`str` using `sp` and at `bl`) |
| Call / return instructions | `call SYMBOL` / `ret` | `bl SYMBOL` / `ret` (save/restore `x30` if function executes `bl`) |

## 3. Ode Source Notation

Ode has one layer: the coder chooses every instruction, register, and stack layout. The compiler expands
only fixed notations and never inserts hidden moves, spills, or comparisons.

- **Target:** `target x86_64` (default if omitted) or `target arm64` at the top of the file.
- **Function:** `fn local_name as "linker_symbol" { ... }` (the closing `}` must sit at column 0).
- **Register aliases:** `reg idx = rcx` (or `reg idx = x2`). Use `idx` in operands and inside `place { ... }`.
- **Stack frame:**
  ```ode
  frame {
    buf: 1 * block       // kinds: byte (1), u32 (4), u64 (8), cv (32), block (64), or plain byte count
    saved_lr: 1 * u64
  }
  ```
  `frame.size` equals the total byte size of the frame (keep it a multiple of 16 on AArch64).
  `&buf` computes `[rsp + off]` (x86-64 `lea`) or `sp, off` (AArch64 `add`).
  `saved_lr[0]` accesses slot 0 of that field; `buf.u64[k]` reinterprets `buf` as 8-byte slots.
- **Typed single-instruction assignment (`:=`):**
  - `dst := src` expands to exactly ONE instruction (`mov`, `lea`, `ldr`, `str`, or `add`), matching
    operand sizes (`byte`, `dword`, `qword`, or frame slot size). On AArch64, `:=` cannot store an
    immediate directly to memory (load into a register first).
- **Explicit local control flow (zero hidden `cmp`, byte-identical to labels):**
  Write your own `cmp` (or `test`), then branch on one of the four supported conditions: `eq` (equal /
  zero), `ne` (not equal / nonzero), `ult` (unsigned `<`), or `uge` (unsigned `>=`).
  - `if COND { ... }` and `if COND { ... } else { ... }` (emits one conditional branch, plus one jump for `else`).
  - `loop { ... }` (top-tested loop; emits an unconditional back-edge at `}`).
  - `loop { ... } while COND` (bottom-tested loop; emits one conditional back-edge `<branch(COND)>`).
  - Inside a `loop`: `break`, `break if COND`, `continue`, `continue if COND`.
  - Raw labels (`@name:`) and jumps (`jmp @name`, `je @name`, `b @name`, `b.eq @name`) also work everywhere.
  - On x86-64, place a single `ret` at the end of each function (jump or `break` to it rather than writing an early `ret` mid-function).
  - Raw assembly operands take literal integer offsets (such as `[rsi + 16]`); constant arithmetic like `$k * 16` works inside `:=` and frame slots (`buf.u64[$k]`).
- **Inline macros (`inline fn`):**
  `inline fn NAME(p: gpr, q: vec) distinct(p, q) changes p { ... }` — checked against the instruction
  table so every modified register is listed in `changes`.
- **Loop invariants (`place { ... }`):**
  Every loop head needs a `place { ... }` block telling the prover what stays true on every iteration:
  - `name i = idx` — names the register holding the loop counter.
  - `fact 0 <= i`, `fact i <= n` — linear bounds on counters and values.
  - `fact all_zero(a) == zero_from(a, i)` — specification equality linking loop state to the goal.
  - `wrote out[i ..] = expr` or `wrote out[.. i] = expr` — slice written so far.
  - `keep r1 r2` — extra registers kept unchanged across the loop.
  - `decreases n - i` — nonnegative expression that strictly decreases each turn.

## 4. Verified Instruction Reference

The tables below list the core verified instructions accepted by `odeverify` from `core/x86.tab` and
`arm64/arm64.tab`. Each row shows the category and exact assembly forms.

### x86-64 (`core/x86.tab`)

| Category | Exact assembly syntax |
|---|---|
| 64-bit arithmetic & logic | `add r, r/imm`, `sub r, r/imm`, `and r, r/imm`, `or r, r/imm`, `xor r, r` (zero), `shl r, imm`, `shr r, imm`, `dec r` |
| 32-bit arithmetic & logic | `mov r32, r32/imm/[base+n]`, `or r32, r32`, `and r32, imm`, `xor r32, r32`, `shr r32, imm`, `dec r32` |
| Loads, stores & addresses | `mov r, r/imm`, `mov r, qword ptr [base+n]`, `mov qword ptr [base+n], r`, `lea r, [base+n]`, `movzx r32, byte ptr [base+n]`, `mov byte ptr [base+n], al/imm` |
| Compare, test & branches | `cmp r, r/imm`, `test r, r`, `jmp @L`, `je @L`, `jne @L`, `jb @L`, `jae @L` |
| Stack & calls | `push r`, `pop r`, `sub rsp, imm`, `add rsp, imm`, `call SYMBOL`, `ret` |
| SIMD 128-bit (`needs avx512` / `sse41`) | `vmovdqu xmmX, [base+N]`, `vmovdqu [base+N], xmmX`, `vmovdqa xmmX, xmmY`, `vpaddd xmmX, xmmY, xmmZ`, `vpxord xmmX, xmmY, xmmZ`, `vpor xmmX, xmmY, xmmZ`, `vprord xmmX, xmmY, imm`, `psrld xmmX, imm`, `pslld xmmX, imm`, `pshufb xmmX, xmmY` |
| SIMD 512-bit (`needs avx512`) | `vmovdqu32 zmmX, [base+N]`, `vmovdqu32 [base+N], zmmX`, `vpaddd`, `vpxord`, `vprord`, `vpshufb`, `vshufi32x4`, `vpermq`, `vpbroadcastd` |

### AArch64 (`arm64/arm64.tab` — all 47 rows formally proved against `arm64-semantics`)

| Category | Exact assembly syntax |
|---|---|
| Integer moves & arithmetic | `mov xd, xs/imm`, `mov wd, imm`, `add xd, xs, xp/imm`, `sub xd, xs, xp/imm`, `lsl xd, xs, imm` |
| Stack pointer | `sub sp, sp, imm`, `add sp, sp, imm`, `add xd, sp, imm`, `ldr xd, [sp, off]`, `str xs, [sp, off]` |
| Memory loads & stores | `ldr xd, [xb, off]`, `str xs, [xb, off]`, `ldr wd, [xb, off]`, `str ws, [xb, off]`, `ldrb wd, [xb, off]`, `strb ws, [xb, off]` |
| Compare, branch & call | `cmp xs, xp/imm`, `b @L`, `b.eq @L`, `b.ne @L`, `b.hs @L`, `b.lo @L`, `bl SYMBOL`, `ret`, `nop` |
| NEON 128-bit vector | `ld1 {vX.4s}, [xb]`, `st1 {vX.4s}, [xb]`, `eor vD.16b, vA.16b, vB.16b`, `orr vD.16b, vA.16b, vB.16b`, `add vD.4s, vA.4s, vB.4s`, `rev32 vD.8h, vS.8h`, `ushr vD.4s, vS.4s, imm`, `shl vD.4s, vS.4s, imm`, `fmov dX, xS`, `uzp1`/`uzp2`/`zip1`/`zip2` (`.4s`/`.2d`), `ext vD.16b, vA.16b, vB.16b, 4/8/12` |

## 5. Contracts and Specifications

A `.spec` file defines pure declarative functions (`def`) and function contracts (`contract`):

- Parameter kinds: `number` (64-bit integer), `bytes` with `n bytes` (variable-length byte buffer),
  `cv` (32 bytes = 8 words), `block` (64 bytes = 16 words), `N bytes` (fixed size), or a named `layout`.
- Common clauses inside `contract SYMBOL(...) { ... }`:
  - `requires no_overlap(out, a, b)` — memory buffers do not share any byte.
  - `requires n <= 64` — linear bounds on numeric inputs.
  - `ensures out = expr` — postcondition for a written buffer.
  - `returns expr` — postcondition for the return register (`rax` / `x0`).
  - `trace depends on n` — lists inputs (or computed values) that branches and memory addresses may
    depend on. Omit data inputs to guarantee constant-time control flow and memory accesses with respect
    to those inputs.
  - `result depends on ...` — optional clause restricting what a returned integer may depend on.
  - `stack N` (or `stack BASE + STEP * bits((n - SUB) / DIV)` for recursion) and `decreases n`.
  - `needs sse41` / `needs avx512` (x86-64 processor features).

## 6. Verified Worked Examples

### Example 1: x86-64 loop with structured control flow and `place`

<!-- card-example: all_zero_x86 x86_64 -->
```spec
def zero_from(a, i) {
    if i >= len(a) then 1
    else if a[i] != 0 then 0
    else zero_from(a, i + 1)
}
def all_zero(a) { zero_from(a, 0) }

contract card_all_zero_x86(a: n bytes, n: number) {
    returns all_zero(a)
    trace depends on a, n
    stack 0
}
```
```ode
target x86_64

fn all_zero as "card_all_zero_x86" {
  reg base = rdi
  reg count = rsi
  reg idx = rcx
  reg res = rax

  idx := 0
  res := 1
  loop {
    place {
      name i = idx
      fact 0 <= i
      fact i <= n
      fact all_zero(a) == zero_from(a, i)
      decreases n - i
    }
    cmp idx, count
    break if uge
    mov rdx, base
    add rdx, idx
    movzx edx, byte ptr [rdx]
    cmp rdx, 0
    if ne {
      res := 0
      break
    }
    add idx, 1
  }
  ret
}
```

### Example 2: AArch64 loop with structured control flow and `place`

<!-- card-example: all_zero_arm64 arm64 -->
```spec
def zero_from(a, i) {
    if i >= len(a) then 1
    else if a[i] != 0 then 0
    else zero_from(a, i + 1)
}
def all_zero(a) { zero_from(a, 0) }

contract card_all_zero_arm64(a: n bytes, n: number) {
    returns all_zero(a)
    trace depends on a, n
    stack 0
}
```
```ode
target arm64

fn all_zero as "card_all_zero_arm64" {
  reg base = x0
  reg count = x1
  reg idx = x2
  reg addr = x3
  reg cur = w4
  reg cur64 = x4

  idx := 0
  loop {
    place {
      name i = idx
      fact 0 <= i
      fact i <= n
      fact all_zero(a) == zero_from(a, i)
      decreases n - i
    }
    cmp idx, count
    if uge {
      x0 := 1
      ret
    }
    add addr, base, idx
    ldrb cur, [addr, 0]
    cmp cur64, 0
    if ne {
      x0 := 0
      ret
    }
    add idx, idx, 1
  }
}
```

### Example 3: AArch64 constant-time vector function (zero branches, trace depends on nothing)

<!-- card-example: xor16_arm64 arm64 -->
```spec
def xor_block(a, b) { [a[i] ^ b[i] for i in 0..16] }

contract card_xor16_arm64(out: block, a: block, b: block) {
    requires no_overlap(out, a, b)
    ensures out = xor_block(a, b)
    stack 0
}
```
```ode
target arm64

fn xor16 as "card_xor16_arm64" {
  reg op = x0
  reg ap = x1
  reg bp = x2

  for k in 0..3 {
    ld1 {v0.4s}, [ap]
    ld1 {v1.4s}, [bp]
    eor v0.16b, v0.16b, v1.16b
    st1 {v0.4s}, [op]
    add ap, ap, 16
    add bp, bp, 16
    add op, op, 16
  }
  ld1 {v0.4s}, [ap]
  ld1 {v1.4s}, [bp]
  eor v0.16b, v0.16b, v1.16b
  st1 {v0.4s}, [op]
  ret
}
```

### Example 4: AArch64 caller with stack frame, callee-saved registers, and function call

<!-- card-example: xor_twice_arm64 arm64 -->
```spec
def xor_block(a, b) { [a[i] ^ b[i] for i in 0..16] }

contract card_xor16_step(out: block, a: block, b: block) {
    requires no_overlap(out, a, b)
    ensures out = xor_block(a, b)
    stack 0
}

contract card_xor16_twice(out: block, a: block, b: block) {
    requires no_overlap(out, a, b)
    ensures out = xor_block(xor_block(a, b), b)
    stack 96
}
```
```ode
target arm64

fn xor16_step as "card_xor16_step" {
  for k in 0..3 {
    ld1 {v0.4s}, [x1]
    ld1 {v1.4s}, [x2]
    eor v0.16b, v0.16b, v1.16b
    st1 {v0.4s}, [x0]
    add x1, x1, 16
    add x2, x2, 16
    add x0, x0, 16
  }
  ld1 {v0.4s}, [x1]
  ld1 {v1.4s}, [x2]
  eor v0.16b, v0.16b, v1.16b
  st1 {v0.4s}, [x0]
  ret
}

fn xor16_twice as "card_xor16_twice" {
  frame {
    tmp: 1 * block
    saved_lr: 1 * u64
    saved_out: 1 * u64
    saved_b: 1 * u64
    pad: 8
  }
  reg keep_out = x19
  reg keep_b = x20

  sub sp, sp, frame.size
  saved_lr[0] := x30
  saved_out[0] := keep_out
  saved_b[0] := keep_b
  keep_out := x0
  keep_b := x2

  x0 := &tmp
  bl card_xor16_step

  x0 := keep_out
  x1 := &tmp
  x2 := keep_b
  bl card_xor16_step

  keep_b := saved_b[0]
  keep_out := saved_out[0]
  x30 := saved_lr[0]
  add sp, sp, frame.size
  ret
}
```

## 7. Reading Common Verifier Diagnostics

Each row below lists a message from `ode_tool.py check`, what caused it, and the typical fix.

| Message | Cause | Fix |
|---|---|---|
| `with no place` | A loop head has no `place { ... }` block | Add a `place { name ...; fact ...; decreases ... }` block at the loop head |
| `need entail` + `cannot show: ...` | A bound or offset could not be proved from the known inequalities | Check for off-by-one bounds, guard the access, or strengthen `fact` lines in `place { ... }` |
| `values kept out of the trace` | A branch or memory address depends on an input not listed in `trace depends on` | Use branchless operations, or (if allowed by the problem) list the input in `trace depends on` |
| `register a callee keeps` | A callee-saved register (`rbx`/`r12`–`r15` or `x19`–`x30`) changed between entry and `ret` | Save it into your `frame` on entry and restore it before `ret` |
| `multiple of 16` (AArch64) | `sp` was not 16-byte aligned at a stack load/store or `bl` | Pad `frame { ... }` so `frame.size` is a multiple of 16 |
| `cannot show: reg <= 2^64 - N` | A dead pointer increment moved a pointer past the last byte of a fixed buffer (`ptr + N` can wrap `2^64`) | Omit the pointer increment after the last load/store |
| `no instruction at N` (x86-64) | An early `ret` appeared before the end of an x86-64 function | Use one `ret` at the end of the function and `break` or jump to it |
| `FALSE on probe` | Concrete execution found an input where code disagrees with the contract | Fix the functional bug shown in the counterexample before tuning proofs |
