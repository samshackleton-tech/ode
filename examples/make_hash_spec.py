#!/usr/bin/env pypy3
"""Write BLAKE3's hash of a message of one fixed length as a specification.

    pypy3 examples/make_hash_spec.py LENGTH > examples/blake3-hash-LENGTH.sexp

The output composes the compression specification -- embedded under
(defs ...) by hash -- as C2SP BLAKE3 sections 2.4-2.6 state: chunks of
1024 bytes, each a chain of compressions from the IV, CHUNK_START on the
first and CHUNK_END on the last; chaining values paired left to right
into PARENT nodes, an odd one carried up; ROOT on the last compression.
Inputs m0..m(N-1) are the message as little-endian words, zero-padded to
whole 64-byte blocks; outputs are the 8 words of the 32-byte hash.
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
from ode.canon import canonical_bytes, hash_of, parse  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
IV = [str(v) for v in (0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
                       0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19)]
CHUNK_START, CHUNK_END, PARENT, ROOT = 1, 2, 4, 8


def main(length):
    with open(os.path.join(HERE, "blake3-compress.sexp"), "rb") as f:
        compress = parse(f.read())
    chash = hash_of(compress).hex()
    steps = []

    def compression(node, flags, tag):
        cv, words, counter, block_len, node_flags = node
        outs = [f"{tag}_{i}" for i in range(16)]
        args = cv + words + [str(counter & 0xFFFFFFFF), str(counter >> 32),
                             str(block_len), str(node_flags | flags)]
        steps.append(f"(({' '.join(outs)}) (call #{chash} {' '.join(args)}))")
        return outs[:8]

    # A node is the last compression's inputs, not yet run (as in blake3.py).
    nodes = []
    for c in range(max(1, -(-length // 1024))):
        chunk_len = max(0, min(1024, length - 1024 * c))
        blocks = max(1, -(-chunk_len // 64))
        cv = IV
        for b in range(blocks):
            off = 1024 * c + 64 * b
            node = (cv, [f"m{off // 4 + i}" for i in range(16)], c,
                    max(0, min(64, length - off)),
                    (CHUNK_START if b == 0 else 0)
                    | (CHUNK_END if b == blocks - 1 else 0))
            if b < blocks - 1:
                cv = compression(node, 0, f"c{c}b{b}")
        nodes.append(node)
    level = 0
    while len(nodes) > 1:
        nxt = [(IV, compression(nodes[i], 0, f"l{level}n{i}")
                + compression(nodes[i + 1], 0, f"l{level}n{i + 1}"),
                0, 64, PARENT) for i in range(0, len(nodes) - 1, 2)]
        if len(nodes) % 2:
            nxt.append(nodes[-1])
        nodes, level = nxt, level + 1
    outputs = compression(nodes[0], ROOT, "root")

    n_words = 16 * max(1, -(-length // 64))
    out = [f"; BLAKE3 of a {length}-byte message (C2SP BLAKE3, sections 2.4-2.6),",
           "; composed from the compression embedded under (defs ...).",
           "; Written by examples/make_hash_spec.py.",
           "(spec", f"  (name blake3-hash-{length})",
           f"  (inputs ({' '.join(f'm{i}' for i in range(n_words))}))",
           f"  (defs ((#{chash} {canonical_bytes(compress).decode()})))",
           "  (steps ("] + [f"    {s}" for s in steps] + [
           "    ))", f"  (outputs ({' '.join(outputs)})))"]
    sys.stdout.write("\n".join(out) + "\n")


if __name__ == "__main__":
    main(int(sys.argv[1]))
