#!/bin/sh
# Ode's word-level functions, from source to assembly to objects.
#
#     sh lang/build.sh SOURCE.ode PREFIX OUT FUNCTION...
#     sh lang/build.sh kcheck/hash.ode b3l_ /tmp/objs pad chunk_node node_out wide32 wide128 take part32 subtree hashr
#
# odec.py reads the source and writes it as a Lean value (OUT/OdeSource.lean). Lang.lean prints that value as
# assembly, one file a function (OUT/FUNCTION.S); this step needs Lean (`lake`, the version lean-toolchain
# names). clang assembles each for x86-64 Linux (OUT/FUNCTION.o). Nothing made here is relied on: the
# verifier reads the bytes of the file that is shipped (kcheck/klink.py makes it from these objects).
#
# Kernels, written in Ode's instruction layer, take no Lean: kcheck/kernels.py makes their objects.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
src=$1; prefix=$2; out=$3; shift 3
mkdir -p "$out"
out=$(cd "$out" && pwd)
python3 "$here/odec.py" "$src" "$out/OdeSource.lean" > "$out/odec.txt"
cd "$here"
lake build Lang > "$out/lake.txt" 2>&1 || { echo "Lang.lean does not build:"; tail -n 8 "$out/lake.txt"; exit 1; }
for f in "$@"; do
    lake env lean --run "$out/OdeSource.lean" asm "$prefix" only "$f" > "$out/$f.S" 2> "$out/$f.err" || { echo "$f: not printed"; head -n 8 "$out/$f.err"; exit 1; }
    clang --target=x86_64-unknown-linux-gnu -c -o "$out/$f.o" "$out/$f.S"
done
echo "$# functions of $(basename "$src"): assembly and objects in $out"
