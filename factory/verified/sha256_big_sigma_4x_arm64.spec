// FIPS 180-4 SHA-256 round functions:
//   Sigma0(a) = (a >>> 2) ^ (a >>> 13) ^ (a >>> 22)
//   Sigma1(e) = (e >>> 6) ^ (e >>> 11) ^ (e >>> 25)
// Computed across 4x32-bit lanes and added modulo 2^32, branch-free.
def big_sigma0(a) { (a >>> 2) ^ (a >>> 13) ^ (a >>> 22) }
def big_sigma1(e) { (e >>> 6) ^ (e >>> 11) ^ (e >>> 25) }
def big_sigma_sum4(a, e) { [big_sigma0(a[i]) + big_sigma1(e[i]) for i in 0..4] }

contract ode_sha256_big_sigma_4x(out: 16 bytes, a: 16 bytes, e: 16 bytes) {
    requires no_overlap(out, a, e)
    ensures out = bytes_of(big_sigma_sum4(words(a), words(e)))
    stack 0
}
