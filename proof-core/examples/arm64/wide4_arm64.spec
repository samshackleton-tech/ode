// 4-way NEON 4-KiB BLAKE3 subtree kernel for AArch64 (`wide4_arm64.ode`).
// Hashes four 1,024-byte chunks in parallel across 4 NEON lanes (keeping all 8 CV vectors
// resident in v0..v7 across all 16 blocks), then combines them via 3 parent compressions.
// Constant-time (no `trace depends on` clause).

contract b3l_wide4_arm64(out: cv, input: 4096 bytes, kf: keyed, t: number) {
    requires disjoint(out, input, kf, 1)
    requires 1024 * t + 4096 <= 18446744073709551615
    ensures out = subtree(kf.key, kf.flags, t, input)
    stack 544
}
