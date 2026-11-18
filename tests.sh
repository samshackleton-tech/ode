#!/bin/sh
# Every test file of this repository, each in a process of its own, all at once.
#
#     sh tests.sh [OUTPUT]         (default OUTPUT: tests.out here; one line a file as each ends)
#
# kcheck/test_kbyte.py is run a class at a time (whole, it takes over twenty minutes; so, about seven).
# Tests that run code on a processor need x86-64 Linux with AVX-512 and skip elsewhere; the tests of
# proof-core need Lean's lake and skip where it is not installed. Exit 0 only where every line ends OK.
# This is the whole suite. The check before a merge is shorter: python3 kcheck/gate.py (under five minutes).
here=$(cd "$(dirname "$0")" && pwd)
out=${1:-$here/tests.out}
: > "$out"
one() {     # DIRECTORY FILE [CLASS]
    s=$(date +%s)
    last=$(cd "$here/$1" && python3 "$2" $3 2>&1 | tail -n 4 | tr '\n' ' ')
    echo "$1/$2 $3| $(( $(date +%s) - s )) s | $last" >> "$out"
}
for t in test_ode.py test_kcheck.py test_kone.py test_kloop.py test_varith.py test_varith2.py \
         test_kbinary.py test_lemma_audit.py test_kguess.py test_kplace.py test_kfn.py test_kends.py \
         test_refute.py test_kholes.py test_made.py programs/test_files.py programs/test_specs.py programs/test_decimal.py; do
    one kcheck "$t" "" &
done
for c in Adler32 Adler32Blocks Adler32Blocks4 Lz4Decode Frame Lemmas Lz4Store Lz4Pack Utf8 Base64 Inet Contracts Arithmetic Varint Common; do
    one kcheck test_kbyte.py "$c" &
done
for t in test_sources.py test_p16_source.py test_k32_source.py; do one wide "$t" "" & done
one core test_core.py "" &
one lang test_asm.py "" &
# (the nine of proof-core one after another: each asks Lean's lake to build in the same folder)
( one proof-core test_sound.py ""; one proof-core test_arith.py ""; one proof-core test_machine.py ""; one proof-core test_spec.py ""; one proof-core test_verify.py ""; one proof-core test_call.py ""; one proof-core test_blocks.py ""; one proof-core test_blocks4.py ""; one proof-core test_adler.py "" ) &
wait
total=$(grep -c '' "$out")
good=$(grep -c -E ' OK( \(skipped=[0-9]+\))? *$' "$out")
echo "tests: $good of $total files and classes OK ($out)"
[ "$good" = "$total" ]
