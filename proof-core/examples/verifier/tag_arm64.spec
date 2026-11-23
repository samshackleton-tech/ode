// Verifier-in-Ode building blocks (AArch64): constant-time 64-byte XOR difference and 32-byte fold.
// All three functions have zero branches and keep their input buffers out of the trace (`trace depends on` nothing).

def xor64(a, b) { [a[i] ^ b[i] for i in 0..16] }

def fold32(x) { [x[i] ^ x[i + 8] for i in 0..8] }

def diff32(a, b) { fold32(xor64(a, b)) }

contract v_xor64(out: block, a: block, b: block) {
    requires no_overlap(out, a, b)
    ensures out = xor64(a, b)
    stack 0
}

contract v_fold32(out: cv, x: block) {
    requires no_overlap(out, x)
    ensures out = fold32(x)
    stack 0
}

contract v_diff32(out: cv, a: block, b: block) {
    requires no_overlap(out, a, b)
    ensures out = diff32(a, b)
    stack 80
}
