# One function, several notations

*This page is made by `paper/trial/make_styles.py` from the files in `paper/trial/src/` and the results in `paper/trial/results/`. Its counts and verdicts are read from them. Sections 1 to 3 show each function twice in the notation of the repository's compiler (`lang/odec.py`): with every instruction written out, and with the forms that the compiler expands. The forms came from the trial's prototype. They are the compiler's now, and what they were first compared with, a text macro and a file of typed counts of bytes, is gone (commit `082ba81` has this page as it was at the trial). Section 4 is still made with the prototype, `paper/trial/ode2.py`, a trial's tool: the compiler has no table of AArch64 instructions yet. The contracts are in today's specification language, so an output equation is written with `=` where the report proposes `==`.*

## 1. Three mixing steps

The function reads two arrays of sixteen words, `d` and `a`, mixes them three times and writes `d` back. One step is `(x ^ y) ror 16` in each word: into `d`, then into `a`, then into `d` again. Its contract:

```
def xor_ror16(d, a) { (d ^ a) >>> 16 }
def mix16_step(d, a) { [xor_ror16(d[i], a[i]) for i in 0..16] }
def mix16_chain_3(d, a) {
  let d1 = mix16_step(d, a)
  let a2 = mix16_step(a, d1)
  let d3 = mix16_step(d1, a2)
  d3
}

contract ode_mix16_3(out: block, d: block, a: block) {
    requires no_overlap(out, d, a)
    ensures out = mix16_chain_3(d, a)
    stack 0
    needs avx512
}
```

**Every instruction written out** (`mix16_raw.ode`):

```
fn mix16_3 as "ode_mix16_3" {
  vmovdqu32 zmm0, [rsi + 0]
  vmovdqu32 zmm1, [rdx + 0]
  vpxord zmm0, zmm0, zmm1
  vprord zmm0, zmm0, 16
  vpxord zmm1, zmm1, zmm0
  vprord zmm1, zmm1, 16
  vpxord zmm0, zmm0, zmm1
  vprord zmm0, zmm0, 16
  vmovdqu32 [rdi + 0], zmm0
  vzeroupper
  ret
}
```

**With an inline function** (`mix16.ode`). It says which class of register each operand is of, that the two must differ, and which one it changes:

```
target x86_64

inline fn mix16(d: zmm, a: zmm) distinct(d, a) changes d {
  vpxord d, d, a
  vprord d, d, 16
}

fn mix16_3 as "ode_mix16_3" {
  vmovdqu32 zmm0, [rsi + 0]
  vmovdqu32 zmm1, [rdx + 0]
  mix16(zmm0, zmm1)
  mix16(zmm1, zmm0)
  mix16(zmm0, zmm1)
  vmovdqu32 [rdi + 0], zmm0
  vzeroupper
  ret
}
```

The two give one object file, byte for byte: 11 instructions, 61 bytes of code. The verifier says `shown` of it; the proof file is 16 bytes and the statement 810.

What the compiler says of four mistakes. Each refusal names the line of the mistake:

| The mistake | What the compiler says |
|---|---|
| one register for both operands: `mix16(zmm1, zmm1)` | `` mix16.ode: line 14: mix16: `d` and `a` must differ, and both are given zmm1 `` |
| a general register where a vector register belongs: `mix16(rax, zmm0)` | `` mix16.ode: line 14: mix16: `d` is a register of the class zmm, and `rax` is not one `` |
| the inline function names a register that it was not given: `vprord zmm2, d, 16` | `` mix16.ode: line 7: inline fn mix16: the line names the register `zmm2`; an inline function takes each register it uses as a parameter `` |
| the inline function changes a register that `changes` does not list: `vprord a, d, 16` | `` mix16.ode: line 7: mix16, used at line 13: `vprord zmm1, zmm0, 16` changes zmm1, which `changes` of mix16 does not list `` |

With the text macro that the compiler had before, the second of these was refused by the assembler, which named the function and not the line. The first and the third were taken, and the function then computed something else.

## 2. A scan with a loop

The function says whether every byte of an array is zero, and leaves at the first byte that is not. Its contract:

```
def all_zero_from(xs, at) {
    if at == len(xs) then 1
    else if xs[at] != 0 then 0
    else all_zero_from(xs, at + 1)
}

def all_zero(xs) { all_zero_from(xs, 0) }

contract ode_all_zero(xs: n bytes, n: number) {
    returns all_zero(xs)
    trace depends on xs, n
    stack 0
}
```

**Every instruction written out** (`all_zero.ode`). The loop's invariant stands at the loop, as `place { ... }`:

```
fn all_zero_early as "ode_all_zero" {
  xor ecx, ecx
  @loop:
  place {
    name i = rcx
    fact i <= n
    fact all_zero_from(xs, i) == all_zero(xs)
    decreases n - i
  }
  cmp rcx, rsi
  jae @yes
  mov rdx, rdi
  add rdx, rcx
  movzx eax, byte ptr [rdx + 0]
  cmp rax, 0
  jne @no
  add rcx, 1
  jmp @loop
  @yes:
  mov rax, 1
  jmp @done
  @no:
  xor eax, eax
  @done:
  ret
}
```

The prover needs the invariant with a count of bytes from the function's first byte to that instruction. The compiler works the count out (`odec.py all_zero.ode all_zero_early --places` prints this):

```
place +0x2 {
    name i = rcx
    fact i <= n
    fact all_zero_from(xs, i) == all_zero(xs)
    decreases n - i
}
```

**With names for registers and `:=`** (`all_zero_named.ode`). `reg` gives a register a name for the rest of the function. `p := xs` is one instruction, `mov rdx, rdi`:

```
target x86_64

fn all_zero_early as "ode_all_zero" {
  reg xs = rdi
  reg n  = rsi
  reg i  = rcx
  reg p  = rdx
  reg b  = rax

  xor ecx, ecx
  @loop:
  place {
    name i = rcx
    fact i <= n
    fact all_zero_from(xs, i) == all_zero(xs)
    decreases n - i
  }
  cmp i, n
  jae @yes
  p := xs
  add p, i
  movzx eax, byte ptr [p + 0]
  cmp b, 0
  jne @no
  add i, 1
  jmp @loop
  @yes:
  b := 1
  jmp @done
  @no:
  xor eax, eax
  @done:
  ret
}
```

The two give one object file, 14 instructions and 40 bytes of code, and the same place. The verifier says `shown`; the statement is 770 bytes and the proof 463.

Then one instruction (`nop`) is added before the loop. The place moves with it, to `place +0x3`, and the function is `shown` again. Before, a person typed the count into a second file, and a count that is not moved goes wrong. The same proof with the place at the count as it was before (`place +0x2`) is `refused: live or dead is expected`. The prover, given the place at that count, had found no proof and had not stopped after 60 seconds: it does not say that the loop has no place.

## 3. A frame

`quad32` makes the parent of two parents with the 32-way kernel. Its frame holds a table of 32 addresses and two arrays of 32 results. This is how the table is filled for the first call.

**Every instruction written out** (`proof-core/examples/quad/quad32.ode`: 156 lines, 135 of them code). Each store names its place in the frame as a number; `[rsp + N]` stands 73 times in the code. The first lines:

```
fn quad32 as "ode_quad32" {
  push rbx
  push r12
  sub rsp, 2312
  mov rbx, rdi
  mov r12, rcx
  // the table: lane 0 reads a, lane 1 reads b, the other lanes read a
  mov rax, rsi
  mov qword ptr [rsp + 0], rax
  mov rax, rdx
  mov qword ptr [rsp + 8], rax
  mov rax, rsi
  mov qword ptr [rsp + 16], rax
  mov rax, rsi
  mov qword ptr [rsp + 24], rax
```

and 28 more pairs like the last, to `[rsp + 248]`.

**With a frame** (`quad32.ode`: 69 lines, 56 of them code). The frame is declared once, and a store names a slot. `for i in 2..32` repeats its lines for each number from 2 to 31, with `$i` replaced by the number:

```
fn quad32 as "ode_quad32" {
  reg out = rbx
  reg kf  = r12
  reg tmp = rax

  frame {
    table: 32 * u64
    r1:    32 * cv
    r2:    32 * cv
    pad:   8
  }

  push out
  push kf
  sub rsp, frame.size
  out := rdi
  kf  := rcx

  // the first round: lane 0 reads a (rsi), lane 1 reads b (rdx), the lanes 2 to 31 read a
  tmp := rsi
  table[0] := tmp
  tmp := rdx
  table[1] := tmp
  for i in 2..32 {
    tmp := rsi
    table[$i] := tmp
  }
```

The two give one object file, the kept one, byte for byte (695 bytes of code). So the kept proofs stand: the verifier says `shown` with them, and `ode_quad32`'s own proof is 15 bytes.

A store past the table's end would land in the first array of results. Written out, nothing says so. With the frame, the compiler says:

```
quad32.ode: line 27: `table[32]`: the slots of `table` are 0 to 31
```

`:=` moves as many bytes as both of its sides have, and never widens or cuts. A slot of the table has eight bytes and `eax` has four, so `table[0] := eax` is refused:

```
quad32.ode: line 25: `:=` moves as many bytes as both sides have: `table[0]` has 8 and `eax` has 4
```

## 4. The same step on AArch64

This section is the prototype's. Four words to a register in place of sixteen. A rotation by 16 is one instruction there (`rev32` on halfwords); a rotation by 12 needs a third register, which the inline function names and requires to differ from the other two:

```
inline fn mix16(d: vreg, a: vreg) distinct(d, a) changes d {
  eor d.16b, d.16b, a.16b
  rev32 d.8h, d.8h
}

inline fn mix12(d: vreg, a: vreg, tmp: vreg) distinct(d, a) distinct(d, tmp) distinct(a, tmp) changes d, tmp {
  eor d.16b, d.16b, a.16b
  ushr tmp.4s, d.4s, #12
  shl d.4s, d.4s, #20
  orr d.16b, d.16b, tmp.16b
}

fn arm_mix16_3 as "arm_mix16_3" {
  ld1 {v0.4s}, [x1]
  ld1 {v1.4s}, [x2]
  mix16(v0, v1)
  mix16(v1, v0)
  mix16(v0, v1)
  st1 {v0.4s}, [x0]
  ret
}
```

A use that gives the scratch register and the destination the same register is refused:

```
arm.ode2:29: inline fn `mix12`: distinct(d, tmp) violated (both bound to v0)
```

These were run, not verified: there is no verifier for AArch64 yet. On an Apple M6 (arm64) the functions of `arm.ode2` agree with C that computes the same (`arm_check.c`), and 3 copies with one instruction changed each differ from it.

## What was measured

Each row is one function in one notation: the lines of its source that are code, the bytes of code in its object file, what the verifier printed, and the bytes of its proof file.

| Function | Notation | Lines of code | Bytes of code | The verifier | Proof bytes |
|---|---|---|---|---|---|
| `mix16_3` | written out | 13 | 61 | shown | 16 |
| `mix16_3` | with an inline function | 15 | 61 | shown | 16 |
| `all_zero` | written out | 26 | 40 | shown | 463 |
| `all_zero` | with names and `:=` | 32 | 40 | shown | 463 |
| `quad32` | written out | 135 | 695 | shown | 15 |
| `quad32` | with a frame | 56 | 695 | shown | 15 |

Within a function the notations give the same bytes, so the verdict and the proof are one. The verdicts are from an x86-64 Linux work machine with the repository's verifier; `paper/trial/test_styles.py` makes them again.

## What is not there yet

- An inline function has no contract yet: the verifier reads the instructions of each use, as if they were written out.
- A slot of the frame is counted from the stack pointer as it is once the function has taken the frame's size from it. The compiler does not follow the stack pointer; the verifier judges the code.
- A place names the registers that it speaks of itself (`name i = rcx`). The names that `reg` gives are not carried into it: a name in a place may also be a parameter of the contract, as `xs` and `n` are in section 2.
- Where the table of instructions lacks the `mov` that a `:=` stands for (a store of a number into eight bytes of memory, for one), the assembler refuses it. Its refusal names the function and the instruction, not the line.
- The compiler has no table of AArch64 instructions. The prototype, which section 4 is made with, judges `changes` from the first operand of each instruction as written. It is a trial's tool and is not in the suite.
