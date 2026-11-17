#!/bin/sh
# b3hashr.o made again from its sources, and compared with the file kept here.
#
#     sh make_hash.sh OUT        (needs python3, clang, and Lean's `lake` for the word-level functions)
#
# 1. hash.ode's nine functions: the Ode compiler prints each as assembly (../lang/build.sh), clang assembles.
# 2. The five kernels: ../wide/*.ode, Ode's instruction layer (kernels.py), clang assembles.
# 3. klink.py takes the functions' bytes from those objects, lays them out as one section with nothing left
#    for a linker to fill in, finds the arithmetic proofs, and writes OUT/b3hashr.o with the specification
#    and the proof inside (about a minute).
#
# A maker's tool: nothing here is relied on by a verification, which reads the finished file's bytes
# (python3 verify.py OUT/b3hashr.o blake3.spec). Exit 0 where OUT/b3hashr.o is, byte for byte, the b3hashr.o
# kept in this folder; exit 1 where it differs.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
out=$1
mkdir -p "$out"
out=$(cd "$out" && pwd)
sh "$here/../lang/build.sh" "$here/hash.ode" b3l_ "$out" pad chunk_node node_out wide32 wide128 take part32 subtree hashr
python3 "$here/kernels.py" "$out" > "$out/kernels.txt"
python3 "$here/klink.py" "$out" "$out/b3hashr.o" > "$out/klink.txt"
if cmp -s "$out/b3hashr.o" "$here/b3hashr.o"; then
    echo "b3hashr.o: made again from the sources, the same bytes as the file kept ($(wc -c < "$out/b3hashr.o" | tr -d ' ') bytes)"
else
    echo "b3hashr.o: made again from the sources, and NOT the file kept: $out/b3hashr.o"
    exit 1
fi
