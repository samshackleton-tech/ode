// Contract for the AArch64 NEON one-block BLAKE3 compression kernel (`compress_arm64.ode`), using
// `compress` from ../../../kcheck/blake3.spec. There is no `trace` line: which instructions run and
// which addresses are touched depend on nothing that is given (neither h, m, length, t, nor flags).
contract blake3_servil_compress_in_place_arm64(h: cv, m: block, length: word, t: counter, flags: low word) {
    requires disjoint(h, m, 1)
    ensures h = compress(h, m, t, length, flags)
    stack 0
}
