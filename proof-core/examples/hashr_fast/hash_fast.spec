// Helper contracts with custom Ode calling conventions for the fast short-input BLAKE3 path.
// Used together with `kcheck/blake3.spec` and `kcheck/proofs/inner.spec`.

contract b3l_pad_fast(block: 64 bytes, src: n bytes, n: number) {
    calling {
        in block = r10, src = rsi, n = rdx
        preserves rdi, rsi, rdx, rbx, rbp, r12, r13, r14, r15
    }
    requires no_overlap(block, src)
    requires n <= 64
    ensures block = padded(src)
    trace depends on n
    stack 0
}

contract b3l_chunk_node_fast(nd: node120, input: len bytes, len: number, t: number, flags: byte, plat: any) {
    requires no_overlap(nd, input)
    requires len <= 1024
    ensures nd = chunk_node(nd.h, t, flags, input)
    trace depends on len, plat
    stack 256
    needs sse41
    needs avx512 if plat == 5
}

contract b3l_hashr_long(out: 32 bytes, input: len bytes, len: number, key: 32 bytes, flags: byte, plat: any) {
    requires no_overlap(out, input, key)
    ensures out = bytes_of(hash_words(words(key), flags, input))
    trace depends on len, flags, plat
    stack 18672 + 384 * bits(len / 1024)
    needs sse41
    needs avx512 if plat == 5
}
