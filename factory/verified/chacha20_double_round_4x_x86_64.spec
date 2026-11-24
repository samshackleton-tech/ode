// RFC 8439 Section 2.3 full ChaCha20 double round (4 column + 4 diagonal quarter-rounds)
// in 4-way SIMD, branch-free and constant-time (no `trace` clause).
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

contract ode_chacha20_double_round_4x(state: 64 bytes) {
    ensures state = bytes_of(chacha20_dround(words(state)))
    stack 0
    needs avx
}
