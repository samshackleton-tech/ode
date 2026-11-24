#!/usr/bin/env python3
"""Locked 8-task benchmark suite for the pre-registered AI coder experiment (paper/CODER-EXPERIMENT.md).

4 categories x 2 architectures (x86-64 and AArch64) = 8 symmetric tasks:
  T1 / T2: constant-time 64-byte SIMD mix step ((d[i] ^ a[i]) >>> 16), zero stack
  T3 / T4: byte-scanning loop counting leading zero bytes with loop `place` invariant
  T5 / T6: constant-time 16-byte copy-and-zero-pad loop (`trace depends on n`, input bytes out of trace)
  T7 / T8: composed caller with 64-byte stack-frame buffer, callee-saved registers, and two helper calls

Each task carries:
  - id, category, target, symbol(s)
  - spec: locked declarative specification and contract
  - prompt: plain-English task instructions given to every model in every arm
  - reference: known-good Ode solution (verified `shown` by proof-core/test_coder_exp.py)
  - negative: known-bad Ode mutation (verified NOT `shown` by proof-core/test_coder_exp.py)
"""

SPEC_MIX = """def xor_ror16(x, y) { (x ^ y) >>> 16 }
def mix_step(d, a) { [xor_ror16(d[i], a[i]) for i in 0..16] }
"""

SPEC_LEAD_ZERO = """def lead_zeros_from(a, i) {
    if i >= len(a) then i
    else if a[i] != 0 then i
    else lead_zeros_from(a, i + 1)
}
def lead_zeros(a) { lead_zeros_from(a, 0) }
"""

SPEC_PAD16 = """def pad16(src) {
    [if i < len(src) then src[i] else 0 for i in 0..16]
}
"""

TASKS = [
    # ------------------------------------------------------------------
    # T1: x86-64 constant-time SIMD mix step
    # ------------------------------------------------------------------
    {
        "id": "T1_x86_mix_step",
        "category": "simd_const_time",
        "target": "x86_64",
        "symbols": ["exp_mix_step_x86"],
        "spec": SPEC_MIX + """
contract exp_mix_step_x86(out: block, d: block, a: block) {
    requires no_overlap(out, d, a)
    ensures out = mix_step(d, a)
    stack 0
    needs avx512
}
""",
        "prompt": (
            "Write a single Ode source file (`target x86_64`) implementing `exp_mix_step_x86` to meet "
            "the contract below. Arguments arrive in `rdi` (`out`), `rsi` (`d`), and `rdx` (`a`). "
            "Compute `(d[i] ^ a[i]) >>> 16` for all 16 32-bit words (64 bytes) using 128-bit vector "
            "instructions (`vmovdqu`, `vpxord`, `vprord`), using zero stack and no branches."
        ),
        "reference": """target x86_64

fn mix_step as "exp_mix_step_x86" {
  reg op = rdi
  reg dp = rsi
  reg ap = rdx

  vmovdqu xmm0, [dp + 0]
  vmovdqu xmm1, [ap + 0]
  vpxord xmm0, xmm0, xmm1
  vprord xmm0, xmm0, 16
  vmovdqu [op + 0], xmm0
  vmovdqu xmm0, [dp + 16]
  vmovdqu xmm1, [ap + 16]
  vpxord xmm0, xmm0, xmm1
  vprord xmm0, xmm0, 16
  vmovdqu [op + 16], xmm0
  vmovdqu xmm0, [dp + 32]
  vmovdqu xmm1, [ap + 32]
  vpxord xmm0, xmm0, xmm1
  vprord xmm0, xmm0, 16
  vmovdqu [op + 32], xmm0
  vmovdqu xmm0, [dp + 48]
  vmovdqu xmm1, [ap + 48]
  vpxord xmm0, xmm0, xmm1
  vprord xmm0, xmm0, 16
  vmovdqu [op + 48], xmm0
  ret
}
""",
        "negative": """target x86_64

fn mix_step as "exp_mix_step_x86" {
  reg op = rdi
  reg dp = rsi
  reg ap = rdx

  vmovdqu xmm0, [dp + 0]
  vmovdqu xmm1, [ap + 0]
  vpxord xmm0, xmm0, xmm1
  vprord xmm0, xmm0, 8
  vmovdqu [op + 0], xmm0
  vmovdqu xmm0, [dp + 16]
  vmovdqu xmm1, [ap + 16]
  vpxord xmm0, xmm0, xmm1
  vprord xmm0, xmm0, 8
  vmovdqu [op + 16], xmm0
  vmovdqu xmm0, [dp + 32]
  vmovdqu xmm1, [ap + 32]
  vpxord xmm0, xmm0, xmm1
  vprord xmm0, xmm0, 8
  vmovdqu [op + 32], xmm0
  vmovdqu xmm0, [dp + 48]
  vmovdqu xmm1, [ap + 48]
  vpxord xmm0, xmm0, xmm1
  vprord xmm0, xmm0, 8
  vmovdqu [op + 48], xmm0
  ret
}
""",
    },

    # ------------------------------------------------------------------
    # T2: AArch64 constant-time NEON mix step
    # ------------------------------------------------------------------
    {
        "id": "T2_arm_mix_step",
        "category": "simd_const_time",
        "target": "arm64",
        "symbols": ["exp_mix_step_arm"],
        "spec": SPEC_MIX + """
contract exp_mix_step_arm(out: block, d: block, a: block) {
    requires no_overlap(out, d, a)
    ensures out = mix_step(d, a)
    stack 0
}
""",
        "prompt": (
            "Write a single Ode source file (`target arm64`) implementing `exp_mix_step_arm` to meet "
            "the contract below. Arguments arrive in `x0` (`out`), `x1` (`d`), and `x2` (`a`). "
            "Compute `(d[i] ^ a[i]) >>> 16` for all 16 32-bit words (64 bytes) using 128-bit NEON "
            "instructions (`ld1`, `eor`, `rev32`, `st1`), using zero stack and no branches."
        ),
        "reference": """target arm64

fn mix_step as "exp_mix_step_arm" {
  reg op = x0
  reg dp = x1
  reg ap = x2

  for k in 0..3 {
    ld1 {v0.4s}, [dp]
    ld1 {v1.4s}, [ap]
    eor v0.16b, v0.16b, v1.16b
    rev32 v0.8h, v0.8h
    st1 {v0.4s}, [op]
    add dp, dp, 16
    add ap, ap, 16
    add op, op, 16
  }
  ld1 {v0.4s}, [dp]
  ld1 {v1.4s}, [ap]
  eor v0.16b, v0.16b, v1.16b
  rev32 v0.8h, v0.8h
  st1 {v0.4s}, [op]
  ret
}
""",
        "negative": """target arm64

fn mix_step as "exp_mix_step_arm" {
  reg op = x0
  reg dp = x1
  reg ap = x2

  for k in 0..3 {
    ld1 {v0.4s}, [dp]
    ld1 {v1.4s}, [ap]
    eor v0.16b, v0.16b, v1.16b
    st1 {v0.4s}, [op]
    add dp, dp, 16
    add ap, ap, 16
    add op, op, 16
  }
  ld1 {v0.4s}, [dp]
  ld1 {v1.4s}, [ap]
  eor v0.16b, v0.16b, v1.16b
  st1 {v0.4s}, [op]
  ret
}
""",
    },

    # ------------------------------------------------------------------
    # T3: x86-64 byte-scanning loop with `place` invariant
    # ------------------------------------------------------------------
    {
        "id": "T3_x86_lead_zeros",
        "category": "loop_scan",
        "target": "x86_64",
        "symbols": ["exp_lead_zeros_x86"],
        "spec": SPEC_LEAD_ZERO + """
contract exp_lead_zeros_x86(a: n bytes, n: number) {
    returns lead_zeros(a)
    trace depends on a, n
    stack 0
}
""",
        "prompt": (
            "Write a single Ode source file (`target x86_64`) implementing `exp_lead_zeros_x86` to meet "
            "the contract below. Arguments arrive in `rdi` (`a`) and `rsi` (`n`); return the count of "
            "leading zero bytes in `rax` using zero stack. Include a `place { ... }` loop invariant at "
            "the loop head."
        ),
        "reference": """target x86_64

fn lead_zeros as "exp_lead_zeros_x86" {
  reg base = rdi
  reg count = rsi
  reg idx = rax

  idx := 0
  loop {
    place {
      name i = idx
      fact 0 <= i
      fact i <= n
      fact lead_zeros(a) == lead_zeros_from(a, i)
      decreases n - i
    }
    cmp idx, count
    break if uge
    mov rdx, base
    add rdx, idx
    movzx edx, byte ptr [rdx]
    cmp rdx, 0
    break if ne
    add idx, 1
  }
  ret
}
""",
        "negative": """target x86_64

fn lead_zeros as "exp_lead_zeros_x86" {
  reg base = rdi
  reg count = rsi
  reg idx = rax

  idx := 0
  loop {
    place {
      name i = idx
      fact 0 <= i
      fact i <= n
      fact lead_zeros(a) == lead_zeros_from(a, i)
      decreases n - i
    }
    cmp idx, count
    break if uge
    mov rdx, base
    add rdx, idx
    movzx edx, byte ptr [rdx]
    cmp rdx, 0
    break if eq
    add idx, 1
  }
  ret
}
""",
    },

    # ------------------------------------------------------------------
    # T4: AArch64 byte-scanning loop with `place` invariant
    # ------------------------------------------------------------------
    {
        "id": "T4_arm_lead_zeros",
        "category": "loop_scan",
        "target": "arm64",
        "symbols": ["exp_lead_zeros_arm"],
        "spec": SPEC_LEAD_ZERO + """
contract exp_lead_zeros_arm(a: n bytes, n: number) {
    returns lead_zeros(a)
    trace depends on a, n
    stack 0
}
""",
        "prompt": (
            "Write a single Ode source file (`target arm64`) implementing `exp_lead_zeros_arm` to meet "
            "the contract below. Arguments arrive in `x0` (`a`) and `x1` (`n`); return the count of "
            "leading zero bytes in `x0` using zero stack. Include a `place { ... }` loop invariant at "
            "the loop head."
        ),
        "reference": """target arm64

fn lead_zeros as "exp_lead_zeros_arm" {
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
      fact lead_zeros(a) == lead_zeros_from(a, i)
      decreases n - i
    }
    cmp idx, count
    break if uge
    add addr, base, idx
    ldrb cur, [addr, 0]
    cmp cur64, 0
    break if ne
    add idx, idx, 1
  }
  x0 := idx
  ret
}
""",
        "negative": """target arm64

fn lead_zeros as "exp_lead_zeros_arm" {
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
      fact lead_zeros(a) == lead_zeros_from(a, i)
      decreases n - i
    }
    cmp idx, count
    break if uge
    add addr, base, idx
    ldrb cur, [addr, 0]
    cmp cur64, 0
    break if eq
    add idx, idx, 1
  }
  x0 := idx
  ret
}
""",
    },

    # ------------------------------------------------------------------
    # T5: x86-64 trace-independent 16-byte copy-and-zero-pad loop
    # ------------------------------------------------------------------
    {
        "id": "T5_x86_pad16",
        "category": "loop_write_ct",
        "target": "x86_64",
        "symbols": ["exp_pad16_x86"],
        "spec": SPEC_PAD16 + """
contract exp_pad16_x86(out: 16 bytes, src: n bytes, n: number) {
    requires no_overlap(out, src)
    requires n <= 16
    ensures out = pad16(src)
    trace depends on n
    stack 0
}
""",
        "prompt": (
            "Write a single Ode source file (`target x86_64`) implementing `exp_pad16_x86` to meet "
            "the contract below. Arguments arrive in `rdi` (`out`), `rsi` (`src`), and `rdx` (`n`, "
            "at most 16). Copy `src[0..n]` into `out[0..n]` and fill `out[n..16]` with zero bytes, "
            "using zero stack and keeping the bytes of `src` out of the execution trace (`trace depends on n`)."
        ),
        "reference": """target x86_64

fn pad16 as "exp_pad16_x86" {
  reg dst = rdi
  reg src = rsi
  reg len = rdx
  reg idx = rcx

  idx := 16
  loop {
    place {
      name i = idx
      fact i <= 16
      wrote out[i ..] = pad16(src)
      decreases i
    }
    cmp idx, 0
    break if eq
    sub idx, 1
    mov r8, dst
    add r8, idx
    cmp idx, len
    if ult {
      mov r9, src
      add r9, idx
      movzx eax, byte ptr [r9]
      mov byte ptr [r8], al
      continue
    }
    mov byte ptr [r8], 0
  }
  ret
}
""",
        "negative": """target x86_64

fn pad16 as "exp_pad16_x86" {
  reg dst = rdi
  reg src = rsi
  reg len = rdx
  reg idx = rcx

  idx := 16
  loop {
    place {
      name i = idx
      fact i <= 16
      wrote out[i ..] = pad16(src)
      decreases i
    }
    cmp idx, 0
    break if eq
    sub idx, 1
    mov r8, dst
    add r8, idx
    cmp idx, len
    if ult {
      mov r9, src
      add r9, idx
      movzx eax, byte ptr [r9]
      mov byte ptr [r8], al
      continue
    }
    mov byte ptr [r8], 1
  }
  ret
}
""",
    },

    # ------------------------------------------------------------------
    # T6: AArch64 trace-independent 16-byte copy-and-zero-pad loop
    # ------------------------------------------------------------------
    {
        "id": "T6_arm_pad16",
        "category": "loop_write_ct",
        "target": "arm64",
        "symbols": ["exp_pad16_arm"],
        "spec": SPEC_PAD16 + """
contract exp_pad16_arm(out: 16 bytes, src: n bytes, n: number) {
    requires no_overlap(out, src)
    requires n <= 16
    ensures out = pad16(src)
    trace depends on n
    stack 0
}
""",
        "prompt": (
            "Write a single Ode source file (`target arm64`) implementing `exp_pad16_arm` to meet "
            "the contract below. Arguments arrive in `x0` (`out`), `x1` (`src`), and `x2` (`n`, "
            "at most 16). Copy `src[0..n]` into `out[0..n]` and fill `out[n..16]` with zero bytes, "
            "using zero stack and keeping the bytes of `src` out of the execution trace (`trace depends on n`)."
        ),
        "reference": """target arm64

fn pad16 as "exp_pad16_arm" {
  reg dst = x0
  reg src = x1
  reg len = x2
  reg idx = x3
  reg saddr = x4
  reg daddr = x5
  reg bw = w6
  reg bx = x6

  idx := 16
  loop {
    place {
      name i = idx
      fact i <= 16
      wrote out[i ..] = pad16(src)
      decreases i
    }
    cmp idx, 0
    break if eq
    sub idx, idx, 1
    add daddr, dst, idx
    cmp idx, len
    if ult {
      add saddr, src, idx
      ldrb bw, [saddr, 0]
      strb bw, [daddr, 0]
      continue
    }
    bx := 0
    strb bw, [daddr, 0]
  }
  ret
}
""",
        "negative": """target arm64

fn pad16 as "exp_pad16_arm" {
  reg dst = x0
  reg src = x1
  reg len = x2
  reg idx = x3
  reg saddr = x4
  reg daddr = x5
  reg bw = w6
  reg bx = x6

  idx := 16
  loop {
    place {
      name i = idx
      fact i <= 16
      wrote out[i ..] = pad16(src)
      decreases i
    }
    cmp idx, 0
    break if eq
    sub idx, idx, 1
    add daddr, dst, idx
    cmp idx, len
    if ult {
      add saddr, src, idx
      ldrb bw, [saddr, 0]
      strb bw, [daddr, 0]
      continue
    }
    bx := 1
    strb bw, [daddr, 0]
  }
  ret
}
""",
    },

    # ------------------------------------------------------------------
    # T7: x86-64 frame + callee-saved + helper call composition
    # ------------------------------------------------------------------
    {
        "id": "T7_x86_mix_twice",
        "category": "frame_call",
        "target": "x86_64",
        "symbols": ["exp_step_x86", "exp_mix_twice_x86"],
        "spec": SPEC_MIX + """
contract exp_step_x86(out: block, d: block, a: block) {
    requires no_overlap(out, d, a)
    ensures out = mix_step(d, a)
    stack 0
    needs avx512
}

contract exp_mix_twice_x86(out: block, d: block, a: block) {
    requires no_overlap(out, d, a)
    ensures out = mix_step(mix_step(d, a), a)
    stack 96
    needs avx512
}
""",
        "prompt": (
            "Write a single Ode source file (`target x86_64`) defining BOTH `exp_step_x86` and "
            "`exp_mix_twice_x86` (in that order) to meet the contracts below. `exp_mix_twice_x86` "
            "must allocate a stack frame holding a 64-byte intermediate block, save and restore any "
            "callee-saved registers it uses, and call `exp_step_x86` twice within `stack 96`."
        ),
        "reference": """target x86_64

fn step as "exp_step_x86" {
  vmovdqu xmm0, [rsi + 0]
  vmovdqu xmm1, [rdx + 0]
  vpxord xmm0, xmm0, xmm1
  vprord xmm0, xmm0, 16
  vmovdqu [rdi + 0], xmm0
  vmovdqu xmm0, [rsi + 16]
  vmovdqu xmm1, [rdx + 16]
  vpxord xmm0, xmm0, xmm1
  vprord xmm0, xmm0, 16
  vmovdqu [rdi + 16], xmm0
  vmovdqu xmm0, [rsi + 32]
  vmovdqu xmm1, [rdx + 32]
  vpxord xmm0, xmm0, xmm1
  vprord xmm0, xmm0, 16
  vmovdqu [rdi + 32], xmm0
  vmovdqu xmm0, [rsi + 48]
  vmovdqu xmm1, [rdx + 48]
  vpxord xmm0, xmm0, xmm1
  vprord xmm0, xmm0, 16
  vmovdqu [rdi + 48], xmm0
  ret
}

fn mix_twice as "exp_mix_twice_x86" {
  frame {
    tmp: 1 * block
  }
  push rbx
  push r12
  sub rsp, frame.size
  rbx := rdi
  r12 := rdx

  rdi := &tmp
  call exp_step_x86

  rdi := rbx
  rsi := &tmp
  rdx := r12
  call exp_step_x86

  add rsp, frame.size
  pop r12
  pop rbx
  ret
}
""",
        "negative": """target x86_64

fn step as "exp_step_x86" {
  vmovdqu xmm0, [rsi + 0]
  vmovdqu xmm1, [rdx + 0]
  vpxord xmm0, xmm0, xmm1
  vprord xmm0, xmm0, 16
  vmovdqu [rdi + 0], xmm0
  vmovdqu xmm0, [rsi + 16]
  vmovdqu xmm1, [rdx + 16]
  vpxord xmm0, xmm0, xmm1
  vprord xmm0, xmm0, 16
  vmovdqu [rdi + 16], xmm0
  vmovdqu xmm0, [rsi + 32]
  vmovdqu xmm1, [rdx + 32]
  vpxord xmm0, xmm0, xmm1
  vprord xmm0, xmm0, 16
  vmovdqu [rdi + 32], xmm0
  vmovdqu xmm0, [rsi + 48]
  vmovdqu xmm1, [rdx + 48]
  vpxord xmm0, xmm0, xmm1
  vprord xmm0, xmm0, 16
  vmovdqu [rdi + 48], xmm0
  ret
}

fn mix_twice as "exp_mix_twice_x86" {
  frame {
    tmp: 1 * block
  }
  push rbx
  push r12
  sub rsp, frame.size
  rbx := rdi
  r12 := rdx

  rdi := &tmp
  call exp_step_x86

  rdi := rbx
  rsi := &tmp
  rdx := r12
  call exp_step_x86

  add rsp, frame.size
  pop rbx
  pop r12
  ret
}
""",
    },

    # ------------------------------------------------------------------
    # T8: AArch64 frame + callee-saved + helper call composition
    # ------------------------------------------------------------------
    {
        "id": "T8_arm_mix_twice",
        "category": "frame_call",
        "target": "arm64",
        "symbols": ["exp_step_arm", "exp_mix_twice_arm"],
        "spec": SPEC_MIX + """
contract exp_step_arm(out: block, d: block, a: block) {
    requires no_overlap(out, d, a)
    ensures out = mix_step(d, a)
    stack 0
}

contract exp_mix_twice_arm(out: block, d: block, a: block) {
    requires no_overlap(out, d, a)
    ensures out = mix_step(mix_step(d, a), a)
    stack 96
}
""",
        "prompt": (
            "Write a single Ode source file (`target arm64`) defining BOTH `exp_step_arm` and "
            "`exp_mix_twice_arm` (in that order) to meet the contracts below. `exp_mix_twice_arm` "
            "must allocate a 16-byte-aligned stack frame holding a 64-byte intermediate block and "
            "saved registers (`x30`, plus any callee-saved registers used), and call `exp_step_arm` "
            "twice within `stack 96`."
        ),
        "reference": """target arm64

fn step as "exp_step_arm" {
  for k in 0..3 {
    ld1 {v0.4s}, [x1]
    ld1 {v1.4s}, [x2]
    eor v0.16b, v0.16b, v1.16b
    rev32 v0.8h, v0.8h
    st1 {v0.4s}, [x0]
    add x1, x1, 16
    add x2, x2, 16
    add x0, x0, 16
  }
  ld1 {v0.4s}, [x1]
  ld1 {v1.4s}, [x2]
  eor v0.16b, v0.16b, v1.16b
  rev32 v0.8h, v0.8h
  st1 {v0.4s}, [x0]
  ret
}

fn mix_twice as "exp_mix_twice_arm" {
  frame {
    tmp: 1 * block
    saved_lr: 1 * u64
    saved_out: 1 * u64
    saved_a: 1 * u64
    pad: 8
  }
  reg keep_out = x19
  reg keep_a = x20

  sub sp, sp, frame.size
  saved_lr[0] := x30
  saved_out[0] := keep_out
  saved_a[0] := keep_a
  keep_out := x0
  keep_a := x2

  x0 := &tmp
  bl exp_step_arm

  x0 := keep_out
  x1 := &tmp
  x2 := keep_a
  bl exp_step_arm

  keep_a := saved_a[0]
  keep_out := saved_out[0]
  x30 := saved_lr[0]
  add sp, sp, frame.size
  ret
}
""",
        "negative": """target arm64

fn step as "exp_step_arm" {
  for k in 0..3 {
    ld1 {v0.4s}, [x1]
    ld1 {v1.4s}, [x2]
    eor v0.16b, v0.16b, v1.16b
    rev32 v0.8h, v0.8h
    st1 {v0.4s}, [x0]
    add x1, x1, 16
    add x2, x2, 16
    add x0, x0, 16
  }
  ld1 {v0.4s}, [x1]
  ld1 {v1.4s}, [x2]
  eor v0.16b, v0.16b, v1.16b
  rev32 v0.8h, v0.8h
  st1 {v0.4s}, [x0]
  ret
}

fn mix_twice as "exp_mix_twice_arm" {
  frame {
    tmp: 1 * block
    saved_lr: 1 * u64
    saved_out: 1 * u64
    saved_a: 1 * u64
    pad: 8
  }
  reg keep_out = x19
  reg keep_a = x20

  sub sp, sp, frame.size
  saved_lr[0] := x30
  saved_out[0] := keep_out
  saved_a[0] := keep_a
  keep_out := x0
  keep_a := x2

  x0 := &tmp
  bl exp_step_arm

  x0 := keep_out
  x1 := &tmp
  x2 := keep_a
  bl exp_step_arm

  keep_a := saved_out[0]
  keep_out := saved_out[0]
  x30 := saved_lr[0]
  add sp, sp, frame.size
  ret
}
""",
    },
]
