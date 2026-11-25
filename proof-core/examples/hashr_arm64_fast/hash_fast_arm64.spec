// Contracts for the fast AArch64 BLAKE3 bundle (`hash_fast_arm64.ode` + `wide4_fast_arm64.ode`),
// using `kcheck/blake3.spec` definitions (`padded`, `compress`, `chunk_node`, `node_value`,
// `children`, `subtree`, `hash_words`, `words`, `bytes_of`).
//
// `b3l_hashr_arm64` satisfies the EXACT SAME canonical `.ocl` contract (`trace depends on len`
// only) as `examples/arm64/hash_arm64.spec`.

layout node120 120 { h: cv at 0, block: 64 bytes at 32, counter: number at 96, length: number at 104 below 65, flags: byte at 112 }
layout keyed 40 { key: cv at 0, flags: byte at 32 }

contract b3l_pad_fast_arm64(block: 64 bytes, src: n bytes, n: number) {
    requires no_overlap(block, src)
    requires n <= 64
    ensures block = padded(src)
    trace depends on n
    stack 0
    calling {
        in block = x0, src = x1, n = x2
        preserves x15, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29
    }
}

contract b3l_node_out_fast_arm64(out: cv, nd: node120, root: byte) {
    requires no_overlap(out, nd)
    ensures out = node_value(nd, root)
    stack 0
}

contract b3l_chunk_node_fast_arm64(nd: node120, input: len bytes, len: number, t: number, flags: byte) {
    requires no_overlap(nd, input)
    requires len <= 1024
    ensures nd = chunk_node(nd.h, t, flags, input)
    trace depends on len
    stack 64
}

contract b3l_wide4_fast_arm64(out: block, input: 4096 bytes, kf: keyed, t: number) {
    requires no_overlap(out, input, kf)
    requires 1024 * t + 4096 <= 18446744073709551615
    ensures out = children(kf.key, kf.flags, t, input)
    stack 544
}

contract b3l_subtree_fast_arm64(out: cv, input: len bytes, len: number, kf: keyed, t: number) {
    requires no_overlap(out, input, kf)
    requires len >= 1
    requires 1024 * t + len <= 18446744073709551615
    ensures out = subtree(kf.key, kf.flags, t, input)
    trace depends on len
    decreases len
    stack 816 + 272 * bits((len - 1) / 1024)
}

contract b3l_hashr_long_arm64(out: 32 bytes, input: len bytes, len: number, key: 32 bytes, flags: byte) {
    requires no_overlap(out, input, key)
    requires len >= 1025
    ensures out = bytes_of(hash_words(words(key), flags, input))
    trace depends on len
    stack 1120 + 272 * bits(len / 1024)
}

contract b3l_hashr_arm64(out: 32 bytes, input: len bytes, len: number, key: 32 bytes, flags: byte) {
    requires no_overlap(out, input, key)
    ensures out = bytes_of(hash_words(words(key), flags, input))
    trace depends on len
    stack 1120 + 272 * bits(len / 1024)
}
