#!/usr/bin/env pypy3
"""Write the chaining value of one full BLAKE3 chunk as a specification.

    pypy3 examples/make_chunk_spec.py > examples/blake3-chunk.sexp

A full chunk is 1024 bytes: 16 compressions chained from the IV, the
first with CHUNK_START and the last with CHUNK_END, each with the chunk
counter and block length 64 (C2SP BLAKE3, section 2.4). The output names
the compression by hash; examples/blake3.sexp calls this for every full
chunk that is not the whole message, so one native call covers 1 KB.
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
from ode.canon import hash_of, parse  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
IV = (0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
      0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19)

with open(os.path.join(HERE, "blake3-compress.sexp"), "rb") as f:
    chash = hash_of(parse(f.read())).hex()
steps, cv = [], [str(v) for v in IV]
for b in range(16):
    flags = (1 if b == 0 else 0) | (2 if b == 15 else 0)
    outs = [f"b{b}_{i}" for i in range(16)]
    args = cv + [f"m{16 * b + i}" for i in range(16)] + [
        "counter-lo", "counter-hi", "64", str(flags)]
    steps.append(f"(({' '.join(outs)}) (compress {' '.join(args)}))")
    cv = outs[:8]
print("; The chaining value of one full 1024-byte BLAKE3 chunk (C2SP BLAKE3,")
print("; section 2.4): 16 compressions chained from the IV. Written by")
print("; examples/make_chunk_spec.py.")
print("(spec")
print("  (name blake3-chunk)")
print(f"  (inputs (counter-lo counter-hi {' '.join(f'm{i}' for i in range(256))}))")
print(f"  (uses ((compress #{chash})))")
print("  (steps (")
for s in steps:
    print(f"    {s}")
print("    ))")
print(f"  (outputs ({' '.join(cv)})))")
