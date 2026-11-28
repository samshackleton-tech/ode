// Helper contracts with custom Ode calling conventions for the fast short-input BLAKE3 path.
// Used together with `kcheck/blake3.spec` and `kcheck/proofs/inner.spec`.

contract b3l_pad_fast(block: 64 bytes, src: n bytes, n: number) {
    calling {
        in block = r10, src = rsi, n = rdx
        preserves rdi, rsi, rdx, rbx, rbp, r12, r13, r14, r15
    }
    requires disjoint(block, src, 1)
    requires n <= 64
    ensures block = padded(src)
    trace depends on n
    stack 0
}

contract b3l_chunk_node_fast(nd: node120, input: len bytes, len: number, t: number, flags: byte, plat: any) {
    requires disjoint(nd, input, 1)
    requires len <= 1024
    ensures nd = chunk_node(nd.h, t, flags, input)
    trace depends on len, plat
    stack 256
    needs sse41
    needs avx512 if plat == 5
}

contract blake3_servil_avx512_k16(inputs: 16 inputs, n: number, key: cv, t: counter, packed: bytes flags start end length, out: 16 cvs) {
    requires n >= 1
    requires disjoint(inputs, key, out, 1)
    ensures out[i] = chunk(key, t + i, flags, start, end, length, n, inputs[i]) for i in 0..16
    trace depends on n
    stack 4096
    needs avx512
}

contract b3l_hashr_k16(out: 32 bytes, input: len bytes, len: number, key: 32 bytes, flags: byte) {
    requires disjoint(out, input, key, 1)
    requires len >= 1025
    requires len <= 16384
    ensures out = bytes_of(hash_words(words(key), flags, input))
    trace depends on len, flags
    stack 6000
    needs sse41
    needs avx512
}

contract b3l_hashr_long(out: 32 bytes, input: len bytes, len: number, key: 32 bytes, flags: byte, plat: any) {
    requires disjoint(out, input, key, 1)
    ensures out = bytes_of(hash_words(words(key), flags, input))
    trace depends on len, flags, plat
    stack 18672 + 384 * bits(len / 1024)
    needs sse41
    needs avx512 if plat == 5
}
