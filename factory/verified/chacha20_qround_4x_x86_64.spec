// RFC 8439 Section 2.1 ChaCha20 quarter-round executed across 4 parallel 32-bit lanes
// (a 64-byte block arranged as four 16-byte rows a, b, c, d).
// Note: ROTL(x, k) == ROTR(x, 32 - k), so rotations 16, 12, 8, 7 are >>> 16, >>> 20, >>> 24, >>> 25.
// Zero branches, zero stack, constant-time in all data.
def qr_a1(a, b) { a + b }
def qr_d1(a1, d) { (d ^ a1) >>> 16 }
def qr_c1(c, d1) { c + d1 }
def qr_b1(b, c1) { (b ^ c1) >>> 20 }
def qr_a2(a1, b1) { a1 + b1 }
def qr_d2(a2, d1) { (d1 ^ a2) >>> 24 }
def qr_c2(c1, d2) { c1 + d2 }
def qr_b2(b1, c2) { (b1 ^ c2) >>> 25 }

def chacha_qr(s) {
    let a = [s[0], s[1], s[2], s[3]]
    let b = [s[4], s[5], s[6], s[7]]
    let c = [s[8], s[9], s[10], s[11]]
    let d = [s[12], s[13], s[14], s[15]]
    let a1 = [qr_a1(a[i], b[i]) for i in 0..4]
    let d1 = [qr_d1(a1[i], d[i]) for i in 0..4]
    let c1 = [qr_c1(c[i], d1[i]) for i in 0..4]
    let b1 = [qr_b1(b[i], c1[i]) for i in 0..4]
    let a2 = [qr_a2(a1[i], b1[i]) for i in 0..4]
    let d2 = [qr_d2(a2[i], d1[i]) for i in 0..4]
    let c2 = [qr_c2(c1[i], d2[i]) for i in 0..4]
    let b2 = [qr_b2(b1[i], c2[i]) for i in 0..4]
    a2 ++ b2 ++ c2 ++ d2
}

contract ode_chacha20_qround_4x(out: block, state: block) {
    requires disjoint(out, state, 1)
    ensures out = chacha_qr(state)
    stack 0
    needs avx
}
