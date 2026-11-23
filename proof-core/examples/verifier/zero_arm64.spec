// Verifier-in-Ode building block (AArch64): checks whether every byte of an n-byte slice is zero.
// First verified AArch64 loop in Ode, using cmp, b.hs, b.ne, b, and ldrb.

def zero_from(a, at) {
    if at == len(a) then 1
    else if a[at] != 0 then 0
    else zero_from(a, at + 1)
}

def all_zero(a) { zero_from(a, 0) }

contract arm_all_zero(a: n bytes, n: number) {
    returns all_zero(a)
    trace depends on a, n
    stack 0
}
