# One function, several notations

*This page is made by `paper/trial/make_styles.py` from the files in `paper/trial/src/` and the results in `paper/trial/results/`. Its counts and verdicts are read from them. "Today" is what the repository's compiler (`lang/odec.py`) takes. "Prototype" is what the trial's front end `paper/trial/ode2.py` takes: a trial's tool, not one of the repository's, and not a decision about the language. The inline function of section 1 was the prototype's when this page was first made. It is the compiler's now, and the text macro that it was compared with is gone from the compiler (commit `082ba81` has this page as it was then). The contracts are in today's specification language in both, so an output equation is written with `=` where the report proposes `==`.*

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

**Today** (`all_zero.ode`, with the loop's invariant in a second file, `all_zero.places`). The invariant is tied to the code by a count of bytes from the function's start, which a person types:

```
fn all_zero_early as "ode_all_zero" {
  xor ecx, ecx
  @loop:
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

```
place +0x2 {
    name i = rcx
    fact i <= n
    fact all_zero_from(xs, i) == all_zero(xs)
    decreases n - i
}
```

**Prototype** (`all_zero.ode2`). Registers have names, a store is written `:=`, and the invariant stands at the loop:

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

Both give one object file: 14 instructions, 40 bytes of code. The place the tool works out is the one typed in `all_zero.places`. The verifier says `shown`; the statement is 770 bytes and the proof 463.

Then one instruction (`nop`) is added before the loop. The prototype's place moves with it, to `place +0x3`, and the function is `shown` again. The same proof with the place at the count typed before (`place +0x2`) is `refused: live or dead is expected`. The prover, given the place file as typed before, had found no proof and had not stopped after 60 seconds: it does not say that the loop has no place.

## 3. A frame

`quad32` makes the parent of two parents with the 32-way kernel. Its frame holds a table of 32 addresses and two arrays of 32 results. This is how the table is filled for the first call.

**Today** (`proof-core/examples/quad/quad32.ode`: 156 lines, 135 of them code). Each store names its place in the frame as a number; `[rsp + N]` stands 73 times in the code. The first lines:

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

**Prototype** (`quad32.ode2`: 69 lines, 56 of them code). The frame is declared once, and a store names a slot:

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

  // Round 1: lane 0 reads a (rsi), lane 1 reads b (rdx), lanes 2..31 read a
  tmp := rsi
  table[0] := tmp
  tmp := rdx
  table[1] := tmp
  for i in 2..32 {
    tmp := rsi
    table[i] := tmp
  }
```

The prototype's object file is the kept one, byte for byte (695 bytes of code), so the kept proofs stand: the verifier says `shown` with them, and `ode_quad32`'s own proof is 15 bytes.

A store past the table's end would land in the first array of results. Today nothing says so. The prototype:

```
quad32.ode2:27: frame slot `table[32]` out of bounds (declared 0..32)
```

## 4. The same step on AArch64

Four words to a register in place of sixteen. A rotation by 16 is one instruction there (`rev32` on halfwords); a rotation by 12 needs a third register, which the inline function names and requires to differ from the other two:

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

| Function | Notation | Lines of code | Bytes of code | The verifier | Proof bytes |
|---|---|---|---|---|---|
| `mix16_3` | today, written out | 13 | 61 | shown | 16 |
| `mix16_3` | today, inline function | 15 | 61 | shown | 16 |
| `all_zero` | today, with a place file | 26 | 40 | shown | 463 |
| `all_zero` | prototype | 32 | 40 | shown | 463 |
| `quad32` | today | 135 | 695 | shown | 15 |
| `quad32` | prototype | 56 | 695 | shown | 15 |

Within a function the notations give the same bytes, so the verdict and the proof are one. The verdicts are from an x86-64 Linux work machine with the repository's verifier; `paper/trial/test_styles.py` makes them again.

## What is not there yet

- An inline function has no contract yet: after a use the caller reasons from the instructions, as if they were written out.
- The prototype (sections 2 to 4) judges `changes` from the first operand of each instruction as written. The repository's compiler reads what an instruction changes from the instruction table.
- The prototype knows the forms on this page and no others. It is a trial's tool and is not in the suite.
