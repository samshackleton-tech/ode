// Complete 16-block parallel RFC 8439 Section 2.3 ChaCha20 keystream kernel
// (1,024 output bytes = 16 consecutive blocks with counters state[12] + 0..15).
// All 20 rounds (10 double rounds) + feed-forward state addition, stack 0,
// branch-free and constant-time (no `trace` clause).
def qr_a1(a, b) { a + b }
def qr_d1(a, b, d) { (d ^ qr_a1(a, b)) >>> 16 }
def qr_c1(a, b, c, d) { c + qr_d1(a, b, d) }
def qr_b1(a, b, c, d) { (b ^ qr_c1(a, b, c, d)) >>> 20 }
def qr_a2(a, b, c, d) { qr_a1(a, b) + qr_b1(a, b, c, d) }
def qr_d2(a, b, c, d) { (qr_d1(a, b, d) ^ qr_a2(a, b, c, d)) >>> 24 }
def qr_c2(a, b, c, d) { qr_c1(a, b, c, d) + qr_d2(a, b, c, d) }
def qr_b2(a, b, c, d) { (qr_b1(a, b, c, d) ^ qr_c2(a, b, c, d)) >>> 25 }

def col_round(s) {
    [qr_a2(s[0], s[4], s[8],  s[12]), qr_a2(s[1], s[5], s[9],  s[13]),
     qr_a2(s[2], s[6], s[10], s[14]), qr_a2(s[3], s[7], s[11], s[15]),
     qr_b2(s[0], s[4], s[8],  s[12]), qr_b2(s[1], s[5], s[9],  s[13]),
     qr_b2(s[2], s[6], s[10], s[14]), qr_b2(s[3], s[7], s[11], s[15]),
     qr_c2(s[0], s[4], s[8],  s[12]), qr_c2(s[1], s[5], s[9],  s[13]),
     qr_c2(s[2], s[6], s[10], s[14]), qr_c2(s[3], s[7], s[11], s[15]),
     qr_d2(s[0], s[4], s[8],  s[12]), qr_d2(s[1], s[5], s[9],  s[13]),
     qr_d2(s[2], s[6], s[10], s[14]), qr_d2(s[3], s[7], s[11], s[15])]
}

def diag_round(s) {
    [qr_a2(s[0], s[5], s[10], s[15]), qr_a2(s[1], s[6], s[11], s[12]),
     qr_a2(s[2], s[7], s[8],  s[13]), qr_a2(s[3], s[4], s[9],  s[14]),
     qr_b2(s[3], s[4], s[9],  s[14]), qr_b2(s[0], s[5], s[10], s[15]),
     qr_b2(s[1], s[6], s[11], s[12]), qr_b2(s[2], s[7], s[8],  s[13]),
     qr_c2(s[2], s[7], s[8],  s[13]), qr_c2(s[3], s[4], s[9],  s[14]),
     qr_c2(s[0], s[5], s[10], s[15]), qr_c2(s[1], s[6], s[11], s[12]),
     qr_d2(s[1], s[6], s[11], s[12]), qr_d2(s[2], s[7], s[8],  s[13]),
     qr_d2(s[3], s[4], s[9],  s[14]), qr_d2(s[0], s[5], s[10], s[15])]
}

def chacha20_dround(s) { diag_round(col_round(s)) }

def chacha20_block(s) {
    let s1 = chacha20_dround(s)
    let s2 = chacha20_dround(s1)
    let s3 = chacha20_dround(s2)
    let s4 = chacha20_dround(s3)
    let s5 = chacha20_dround(s4)
    let s6 = chacha20_dround(s5)
    let s7 = chacha20_dround(s6)
    let s8 = chacha20_dround(s7)
    let s9 = chacha20_dround(s8)
    let s10 = chacha20_dround(s9)
    [s[i] + s10[i] for i in 0..16]
}

def with_ctr(s, k) {
    [s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7],
     s[8], s[9], s[10], s[11], if k == 0 then s[12] else s[12] + word(k), s[13], s[14], s[15]]
}

def chacha20_blocks4(s, k) {
    chacha20_block(with_ctr(s, k)) ++ chacha20_block(with_ctr(s, k + 1)) ++
    chacha20_block(with_ctr(s, k + 2)) ++ chacha20_block(with_ctr(s, k + 3))
}

def chacha20_blocks16(s) {
    chacha20_blocks4(s, 0) ++ chacha20_blocks4(s, 4) ++
    chacha20_blocks4(s, 8) ++ chacha20_blocks4(s, 12)
}

contract ode_chacha20_blocks16(out: 1024 bytes, state: 64 bytes) {
    requires disjoint(out, state, 1)
    ensures out = bytes_of(chacha20_blocks16(words(state)))
    needs avx512
    stack 0
}
