// Contracts for the complete single-threaded AArch64 BLAKE3 hash (`hash_arm64.ode`),
// using `blake3.spec` definitions (`padded`, `compress`, `chunk_node`, `node_value`,
// `subtree`, `hash_words`, `words`, `bytes_of`).
//
// Together with `compress_arm64.spec` (`blake3_servil_compress_in_place_arm64`) and
// `pad_arm64.spec` (`b3l_pad_arm64`), these six functions implement arbitrary-length
// BLAKE3 hashing and keyed hashing on AArch64, with every instruction verified in Lean 4.
//
// Notice the trace guarantee on `b3l_hashr_arm64`: `trace depends on len` only — neither
// `input`, `key`, nor `flags` can influence which instructions run or which addresses
// are accessed.

layout node120 120 { h: cv at 0, block: 64 bytes at 32, counter: number at 96, length: number at 104 below 65, flags: byte at 112 }
layout keyed 40 { key: cv at 0, flags: byte at 32 }

contract b3l_node_out_arm64(out: cv, nd: node120, root: byte) {
    requires no_overlap(out, nd)
    ensures out = node_value(nd, root)
    stack 16
}

contract b3l_chunk_node_arm64(nd: node120, input: len bytes, len: number, t: number, flags: byte) {
    requires no_overlap(nd, input)
    requires len <= 1024
    ensures nd = chunk_node(nd.h, t, flags, input)
    trace depends on len
    stack 64
}

contract b3l_subtree_arm64(out: cv, input: len bytes, len: number, kf: keyed, t: number) {
    requires no_overlap(out, input, kf)
    requires len >= 1
    requires 1024 * t + len <= 18446744073709551615
    ensures out = subtree(kf.key, kf.flags, t, input)
    trace depends on len
    decreases len
    stack 352 + 272 * bits((len - 1) / 1024)
}

contract b3l_hashr_arm64(out: 32 bytes, input: len bytes, len: number, key: 32 bytes, flags: byte) {
    requires no_overlap(out, input, key)
    ensures out = bytes_of(hash_words(words(key), flags, input))
    trace depends on len
    stack 656 + 272 * bits(len / 1024)
}
