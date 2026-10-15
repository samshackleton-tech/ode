"""BLAKE3 (unkeyed, 32-byte output), implemented from the C2SP specification.

Ode names every definition by the BLAKE3 hash of its canonical form (SPEC s2).
This module is the one hash implementation the toolchain shares; the checker
uses the same published algorithm through it. Test vectors from the BLAKE3
paper / C2SP appendix live in tests/test_canon.py.
"""
import struct

IV = [0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
      0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]
MSG_PERMUTATION = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]
CHUNK_START = 1 << 0
CHUNK_END = 1 << 1
PARENT = 1 << 2
ROOT = 1 << 3
MASK32 = 0xFFFFFFFF


def _rotr(x, n):
    return ((x >> n) | (x << (32 - n))) & MASK32


def _g(v, a, b, c, d, x, y):
    v[a] = (v[a] + v[b] + x) & MASK32
    v[d] = _rotr(v[d] ^ v[a], 16)
    v[c] = (v[c] + v[d]) & MASK32
    v[b] = _rotr(v[b] ^ v[c], 12)
    v[a] = (v[a] + v[b] + y) & MASK32
    v[d] = _rotr(v[d] ^ v[a], 8)
    v[c] = (v[c] + v[d]) & MASK32
    v[b] = _rotr(v[b] ^ v[c], 7)


def _round(v, m):
    _g(v, 0, 4, 8, 12, m[0], m[1])
    _g(v, 1, 5, 9, 13, m[2], m[3])
    _g(v, 2, 6, 10, 14, m[4], m[5])
    _g(v, 3, 7, 11, 15, m[6], m[7])
    _g(v, 0, 5, 10, 15, m[8], m[9])
    _g(v, 1, 6, 11, 12, m[10], m[11])
    _g(v, 2, 7, 8, 13, m[12], m[13])
    _g(v, 3, 4, 9, 14, m[14], m[15])
    return v


def _permute(m):
    return [m[MSG_PERMUTATION[i]] for i in range(16)]


def _compress(cv, block, counter, block_len, flags):
    words = list(struct.unpack("<16I", block))
    v = cv[:] + IV[:]
    v[12] = counter & MASK32
    v[13] = (counter >> 32) & MASK32
    v[14] = block_len
    v[15] = flags
    m = words
    for _ in range(7):
        v = _round(v, m)
        m = _permute(m)
    out = [(v[i] ^ v[i + 8]) & MASK32 for i in range(8)] + \
          [(v[i + 8] ^ cv[i]) & MASK32 for i in range(8)]
    return out


def _chunk_node(data, counter):
    """The last compression's inputs for one chunk: (cv, block, counter,
    block_len, flags), with every earlier block already chained in."""
    cv = IV[:]
    blocks = [data[i:i + 64] for i in range(0, len(data), 64)] or [b""]
    for i, block in enumerate(blocks):
        flags = (CHUNK_START if i == 0 else 0) | \
                (CHUNK_END if i == len(blocks) - 1 else 0)
        node = (cv, block + b"\x00" * (64 - len(block)), counter,
                len(block), flags)
        if i < len(blocks) - 1:
            cv = _compress(*node)[:8]
    return node


def _cv(node):
    return _compress(*node)[:8]


def _root(node):
    cv, block, counter, block_len, flags = node
    return struct.pack("<8I", *_compress(cv, block, counter, block_len,
                                         flags | ROOT)[:8])


def blake3(data: bytes) -> bytes:
    """The 32-byte BLAKE3 hash of data (unkeyed)."""
    assert isinstance(data, bytes)
    nodes = [_chunk_node(data[off:off + 1024], off // 1024)
             for off in range(0, max(len(data), 1), 1024)]
    # Pair chaining values left to right; an odd one carries up a level.
    while len(nodes) > 1:
        nxt = [(IV[:], struct.pack("<16I", *(_cv(nodes[i]) + _cv(nodes[i + 1]))),
                0, 64, PARENT) for i in range(0, len(nodes) - 1, 2)]
        if len(nodes) % 2:
            nxt.append(nodes[-1])
        nodes = nxt
    return _root(nodes[0])
