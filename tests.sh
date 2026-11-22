#!/bin/sh
# Every test file of this repository, each in a process of its own, all at once.
#
#     sh tests.sh [OUTPUT]         (default OUTPUT: tests.out here; one line a file as each ends)
#     PYTHON=pypy3 sh tests.sh     (choose the interpreter; the default is python3)
#
# kcheck/test_kbyte.py is run a class at a time (whole, it takes over twenty minutes; so, about seven).
# Tests that run code on a processor need x86-64 Linux with AVX-512 and skip elsewhere; the tests of
# proof-core need Lean's lake and skip where it is not installed. Exit 0 only where every line ends OK.
# This is the whole suite. The check before a merge is shorter: python3 kcheck/gate.py (under five minutes).
#
# Where ODE_TEST_CACHE names a folder, a test that passed is written down there under a hash of every file
# it can read, and is not run again on the same files (tests_key.py): after a change to proof-core alone
# only proof-core's tests run. Its line then says `kept`. Without ODE_TEST_CACHE every test runs. A change to
# a page (`.md`) alone runs nothing again.
#
#     ODE_TESTS=proof-core sh tests.sh [OUTPUT]      only the tests of proof-core (under a minute on a laptop)
here=$(cd "$(dirname "$0")" && pwd)
out=${1:-$here/tests.out}
python=${PYTHON:-python3}
command -v "$python" >/dev/null || { echo "tests: cannot find $python" >&2; exit 1; }
: > "$out"
cache=${ODE_TEST_CACHE:-}
key_rest=""; key_pc=""
if [ -n "$cache" ]; then
    mkdir -p "$cache" && key_rest=$("$python" "$here/tests_key.py" rest) && key_pc=$("$python" "$here/tests_key.py" proof-core) || cache=""
fi
kept() {    # DIRECTORY FILE [CLASS]: the file of this test's passing on these very files
    [ -n "$cache" ] || return 1
    if [ "$1" = proof-core ] || [ "$1" = . ]; then k=$key_pc; else k=$key_rest; fi
    echo "$cache/$k-$(echo "$1-$2-$3" | tr '/ ' '__')"
}
one() {     # DIRECTORY FILE [CLASS]
    if f=$(kept "$1" "$2" "$3") && [ -f "$f" ]; then
        echo "$1/$2 $3| kept ($(cut -d'|' -f2 "$f" | tr -d ' ') then) | $(cut -d'|' -f3- "$f")" >> "$out"; return
    fi
    s=$(date +%s)
    last=$(cd "$here/$1" && "$python" "$2" $3 2>&1 | tail -n 4 | tr '\n' ' ')
    line="$1/$2 $3| $(( $(date +%s) - s )) s | $last"
    echo "$line" >> "$out"
    if f=$(kept "$1" "$2" "$3") && echo "$line" | grep -q -E ' OK( \(skipped=[0-9]+\))? *$'; then
        echo "$line" > "$f.new" && mv "$f.new" "$f"
    fi
}
if [ "${ODE_TESTS:-all}" != proof-core ]; then
for t in test_ode.py test_kdecode.py test_kone.py test_kloop.py test_varith.py test_varith2.py \
         test_kbinary.py test_lemma_audit.py test_kguess.py test_kplace.py test_kfn.py test_kends.py \
         test_refute.py test_kholes.py test_made.py programs/test_files.py programs/test_specs.py programs/test_decimal.py; do
    one kcheck "$t" "" &
done
for c in Adler32 Adler32Blocks Adler32Blocks4 Lz4Decode Frame Lemmas Lz4Store Lz4Pack Utf8 Base64 Inet Contracts Arithmetic Varint Common; do
    one kcheck test_kbyte.py "$c" &
done
for t in test_sources.py test_p16_source.py test_k32_source.py; do one wide "$t" "" & done
one core test_core.py "" &
[ -n "${IN_TEST_TESTS:-}" ] || one . test_tests.py "" &         # (not inside itself)
one lang test_asm.py "" &
fi
# proof-core: Lean's lake builds everything once, here; then its tests run side by side (ODE_LEAN_BUILT tells
# them not to ask lake again: built.py). Where lake does not build, that is one failed line and they are not run.
lake=$(command -v lake || { [ -x "$HOME/.elan/bin/lake" ] && echo "$HOME/.elan/bin/lake"; })
lean=""
pc="test_sound.py test_arith.py test_machine.py test_spec.py test_verify.py test_call.py test_low.py test_table.py test_limits.py test_varint.py test_adler.py test_blocks.py test_blocks4.py test_session.py test_kernel.py test_node.py test_p16_one.py test_p16_table.py test_p16.py test_p32.py test_k32.py test_pad.py test_part.py test_record.py test_tail.py test_chunk.py test_meaning.py test_keyed.py test_left.py test_split.py test_doubling.py test_far.py test_empty.py test_parent.py test_turns.py test_high.py test_quad.py"
torun=""
for t in $pc; do { f=$(kept proof-core "$t" "") && [ -f "$f" ]; } || torun="$torun $t"; done
if [ -n "$lake" ] && [ -n "$torun" ]; then
    if ( cd "$here/proof-core" && PATH="$(dirname "$lake"):$PATH" "$lake" build > /dev/null 2>&1 ); then lean=built
    else lean=broken; echo "proof-core/lake build | 0 s | FAILED" >> "$out"; fi
fi
if [ "$lean" != broken ]; then
    for t in $pc; do
        ( [ "$lean" = built ] && export ODE_LEAN_BUILT=1; one proof-core "$t" "" ) &
    done
fi
wait
total=$(grep -c '' "$out")
good=$(grep -c -E ' OK( \(skipped=[0-9]+\))? *$' "$out")
echo "tests: $good of $total files and classes OK ($out)"
[ "$good" = "$total" ]
