// Three functions for AArch64, assembled by clang (`clang --target=aarch64-linux-gnu -c mix.s -o armmix.o`):
// Ode's compiler has no table for AArch64 yet. Their contracts are in mix.spec.

// arm_mix16_3(out, d, a), in x0, x1, x2: three mixing steps on sixteen words, `d`, then `a`, then `d` again,
// each step `(x ^ y) ror 16` a word at a time (`rev32` on halves of 16 bits turns a word by 16). Four words
// at a time, in v0 and v1.
    .text
    .globl arm_mix16_3
    .type arm_mix16_3, %function
arm_mix16_3:
    ld1 {v0.4s}, [x1]
    ld1 {v1.4s}, [x2]
    eor v0.16b, v0.16b, v1.16b
    rev32 v0.8h, v0.8h
    eor v1.16b, v1.16b, v0.16b
    rev32 v1.8h, v1.8h
    eor v0.16b, v0.16b, v1.16b
    rev32 v0.8h, v0.8h
    st1 {v0.4s}, [x0]
    add x1, x1, 16
    add x2, x2, 16
    add x0, x0, 16
    ld1 {v0.4s}, [x1]
    ld1 {v1.4s}, [x2]
    eor v0.16b, v0.16b, v1.16b
    rev32 v0.8h, v0.8h
    eor v1.16b, v1.16b, v0.16b
    rev32 v1.8h, v1.8h
    eor v0.16b, v0.16b, v1.16b
    rev32 v0.8h, v0.8h
    st1 {v0.4s}, [x0]
    add x1, x1, 16
    add x2, x2, 16
    add x0, x0, 16
    ld1 {v0.4s}, [x1]
    ld1 {v1.4s}, [x2]
    eor v0.16b, v0.16b, v1.16b
    rev32 v0.8h, v0.8h
    eor v1.16b, v1.16b, v0.16b
    rev32 v1.8h, v1.8h
    eor v0.16b, v0.16b, v1.16b
    rev32 v0.8h, v0.8h
    st1 {v0.4s}, [x0]
    add x1, x1, 16
    add x2, x2, 16
    add x0, x0, 16
    ld1 {v0.4s}, [x1]
    ld1 {v1.4s}, [x2]
    eor v0.16b, v0.16b, v1.16b
    rev32 v0.8h, v0.8h
    eor v1.16b, v1.16b, v0.16b
    rev32 v1.8h, v1.8h
    eor v0.16b, v0.16b, v1.16b
    rev32 v0.8h, v0.8h
    st1 {v0.4s}, [x0]
    ret
    .size arm_mix16_3, .-arm_mix16_3

// arm_mix16_again(out, d, a): the same, by a call of arm_mix16_3. `bl` puts the address to come back to in
// x30, where this function's own caller's address was: so that one is kept in the stack frame.
    .globl arm_mix16_again
    .type arm_mix16_again, %function
arm_mix16_again:
    sub sp, sp, 16
    str x30, [sp, 8]
    bl arm_mix16_3
    ldr x30, [sp, 8]
    add sp, sp, 16
    ret
    .size arm_mix16_again, .-arm_mix16_again

// arm_mix16_6(out, d, a): the three steps twice, the second time on what the first gave: a block of the stack
// frame holds that in between. Frame, 96 bytes: the block at sp + 0; x30 at sp + 64; x19 and x20, which hold
// `out` and `a` across the first call, at sp + 72 and sp + 80. (The block is written with zeros first: the
// verifier hands a called function a part of the frame to write only where it knows what each cell holds.)
    .globl arm_mix16_6
    .type arm_mix16_6, %function
arm_mix16_6:
    sub sp, sp, 96
    str x30, [sp, 64]
    str x19, [sp, 72]
    str x20, [sp, 80]
    mov x19, x0
    mov x20, x2
    mov x9, 0
    str x9, [sp, 0]
    str x9, [sp, 8]
    str x9, [sp, 16]
    str x9, [sp, 24]
    str x9, [sp, 32]
    str x9, [sp, 40]
    str x9, [sp, 48]
    str x9, [sp, 56]
    add x0, sp, 0
    bl arm_mix16_3
    mov x0, x19
    add x1, sp, 0
    mov x2, x20
    bl arm_mix16_3
    ldr x20, [sp, 80]
    ldr x19, [sp, 72]
    ldr x30, [sp, 64]
    add sp, sp, 96
    ret
    .size arm_mix16_6, .-arm_mix16_6
