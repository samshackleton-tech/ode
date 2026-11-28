// Verifier-in-Ode building blocks (both x86-64 and AArch64): core operations of `Arithmetic.lean`
// and `Reader.lean` written in Ode and verified directly by `odeverify` against their declarative
// specifications.
//
// 1. `row_contradicts(coeffs, pos, neg)`: checks the final row of an arithmetic refutation proof
//    (`Arithmetic.lean`): returns 1 iff `pos < neg` (strictly negative constant `pos - neg < 0`)
//    and every variable coefficient in `coeffs[0..n]` is zero.
// 2. `sum16(a, b)`: lane-wise 32-bit sum of two 16-variable coefficient rows (`Arithmetic.sum`),
//    branch-free and zero-stack (`trace depends on` nothing).
// 3. `bytes_eq(a, b)`: exact byte-slice equality (used by `Reader.lean` to match statement and
//    proof keywords and symbol names).

def all_zero_from(a, at) {
    if at >= len(a) then 1
    else if a[at] != 0 then 0
    else all_zero_from(a, at + 1)
}

def row_contradicts(a, pos, neg) {
    if pos < neg then all_zero_from(a, 0)
    else 0
}

def sum16(a, b) { [a[i] + b[i] for i in 0..16] }

def eq_from(a, b, at) {
    if at >= len(a) then 1
    else if a[at] != b[at] then 0
    else eq_from(a, b, at + 1)
}

def bytes_eq(a, b) { eq_from(a, b, 0) }

// --- x86-64 contracts ---

contract v_row_contradicts_x86(coeffs: n bytes, n: number, pos: number, neg: number) {
    returns row_contradicts(coeffs, pos, neg)
    trace depends on coeffs, n, pos, neg
    stack 0
}

contract v_row_sum16_x86(out: block, a: block, b: block) {
    requires disjoint(out, a, b, 1)
    ensures out = sum16(a, b)
    stack 0
    needs avx512
}

contract v_bytes_eq_x86(a: n bytes, b: n bytes, n: number) {
    returns bytes_eq(a, b)
    trace depends on a, b, n
    stack 0
}

// --- AArch64 contracts ---

contract v_row_contradicts_arm64(coeffs: n bytes, n: number, pos: number, neg: number) {
    returns row_contradicts(coeffs, pos, neg)
    trace depends on coeffs, n, pos, neg
    stack 0
}

contract v_row_sum16_arm64(out: block, a: block, b: block) {
    requires disjoint(out, a, b, 1)
    ensures out = sum16(a, b)
    stack 0
}

contract v_bytes_eq_arm64(a: n bytes, b: n bytes, n: number) {
    returns bytes_eq(a, b)
    trace depends on a, b, n
    stack 0
}
