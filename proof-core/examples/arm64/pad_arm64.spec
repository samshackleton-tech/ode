// Contract for BLAKE3's chunk-tail padding on AArch64 (`pad_arm64.ode`), using `padded` from blake3.spec.
contract b3l_pad_arm64(block: 64 bytes, src: n bytes, n: number) {
    requires disjoint(block, src, 1)
    requires n <= 64
    ensures block = padded(src)
    trace depends on n
    stack 0
}
