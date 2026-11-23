"""A place written where it holds (odec.py).

`place { LINES }` before an instruction says what holds whenever the code comes there: a loop's invariant, in
the lines the prover of proof-core reads. The prover wants each place with the count of bytes from the
function's first byte to that instruction. odec.places() works the count out, so it moves with the code; no
count is typed. A place is no part of the object. `place "SYMBOL" { LINES }` is a place for the proof of
another entry of the function, counted from that entry.

The repository's sources hold their loops' places this way, and the counts they give are those of the kept
proofs (../proof-core/proofs).

    python3 test_places.py"""
from pathlib import Path
import re, sys, tempfile, unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "lang"))
import odec

# Whether every byte of an array is zero; the loop's place stands at the loop.
SCAN = """fn all_zero as "ode_all_zero" {
  xor ecx, ecx
  @loop:
  // what holds each time the code comes here
  place {
    name i = rcx
    fact i <= n      // (a comment in a place is not given to the prover)

    decreases n - i
  }
  cmp rcx, rsi
  jae @yes
  mov rdx, rdi
  add rdx, rcx
  movzx eax, byte ptr [rdx + 0]
  cmp rax, 0
  jne @no
  add rcx, 1
  jmp @loop
  @yes:
  mov rax, 1
  jmp @done
  @no:
  xor eax, eax
  @done:
  ret
}
"""
PLACE = "place +0x2 {\n    name i = rcx\n    fact i <= n\n    decreases n - i\n}\n"
WITHOUT = SCAN[:SCAN.index("  // what holds")] + SCAN[SCAN.index("  cmp rcx, rsi"):]
# A function entered at two symbols, with a place for each proof at one instruction, and a second place of its own.
TWO = """fn both as "ode_both" {
  add rdi, 1
  entry "ode_second"
  xor ecx, ecx
  @loop:
  place {
    name i = rcx
    decreases n - i
  }
  place "ode_second" {
    name j = rcx
    decreases n - j
  }
  add rcx, 1
  cmp rcx, rsi
  jb @loop
  @tail:
  place {
    name k = rsi
    decreases k
  }
  dec rsi
  jne @tail
  ret
}
"""
# (the source, the function, the entry or None, the kept proof's name): the loops of the repository's sources
KEPT = [
    ("kcheck/programs/adler32/adler32.ode", "adler32", None, "ode_adler32"),
    ("kcheck/programs/adler32/blocks.ode", "adler32_blocks", None, "ode_adler32_blocks"),
    ("kcheck/programs/adler32/blocks4.ode", "adler32_blocks4", None, "ode_adler32_blocks4"),
    ("kcheck/hash.ode", "pad", None, "b3l_pad"),
    ("wide/p16.ode", "p16", None, "blake3_servil_avx512_p16"),
    ("wide/k32.ode", "k32", None, "blake3_servil_avx512_k32"),
    ("wide/k32.ode", "k32", "blake3_servil_avx512_p32", "blake3_servil_avx512_p32"),
]


def changed(text, old, new):
    assert text.count(old) == 1, old
    return text.replace(old, new)


def line_of(text, piece):
    got = [i + 1 for i, line in enumerate(text.split("\n")) if piece in line]
    assert len(got) == 1, (piece, got)
    return got[0]


class Places(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.folder = tempfile.TemporaryDirectory()

    @classmethod
    def tearDownClass(cls):
        cls.folder.cleanup()

    def source(self, text):
        path = Path(self.folder.name) / "s.ode"
        path.write_text(text)
        return str(path)

    def built(self, text, name):
        obj = Path(self.folder.name) / "s.o"
        odec.build(self.source(text), name, str(obj))
        return obj.read_bytes()

    def refused(self, said, line, call, *args):
        with self.assertRaises(SystemExit) as stopped: call(*args)
        self.assertIn(said, str(stopped.exception))
        if line is not None: self.assertIn(f": line {line}: ", str(stopped.exception))

    def test_the_count_of_bytes_is_worked_out(self):
        self.assertEqual(odec.places(self.source(SCAN), "all_zero"), PLACE)
        self.assertEqual(odec.places(self.source(WITHOUT), "all_zero"), "")

    def test_the_count_moves_with_the_code(self):
        longer = changed(SCAN, "  xor ecx, ecx\n", "  xor ecx, ecx\n  nop\n")
        self.assertEqual(odec.places(self.source(longer), "all_zero"), PLACE.replace("+0x2", "+0x3"))
        # before the label or after it: the same instruction
        before = changed(changed(SCAN, "  @loop:\n", ""), "  cmp rcx, rsi\n", "  @loop:\n  cmp rcx, rsi\n")
        self.assertEqual(odec.places(self.source(before), "all_zero"), PLACE)

    def test_a_place_is_no_part_of_the_object(self):
        self.assertEqual(self.built(SCAN, "all_zero"), self.built(WITHOUT, "all_zero"))
        self.assertEqual(odec.assembly(self.source(SCAN), "all_zero"), odec.assembly(self.source(WITHOUT), "all_zero"))
        self.assertEqual(odec.instructions(SCAN, "all_zero"), odec.instructions(WITHOUT, "all_zero"))

    def test_places_in_their_order_and_a_place_for_another_entry(self):
        src = self.source(TWO)
        self.assertEqual(odec.places(src, "both"), "place +0x6 {\n    name i = rcx\n    decreases n - i\n}\nplace +0xf {\n    name k = rsi\n    decreases k\n}\n")
        self.assertEqual(odec.places(src, "both", "ode_both"), odec.places(src, "both"))
        # the entry is four bytes in (`add rdi, 1`): its place is counted from there
        self.assertEqual(odec.places(src, "both", "ode_second"), "place +0x2 {\n    name j = rcx\n    decreases n - j\n}\n")
        named = changed(TWO, "  place {\n    name i = rcx", "  place \"ode_both\" {\n    name i = rcx")
        self.assertEqual(odec.places(self.source(named), "both"), odec.places(src, "both"))

    def test_what_cannot_stand_is_refused(self):
        other = changed(TWO, 'place "ode_second" {', 'place "ode_third" {')
        self.refused("a place for `ode_third`, which is no entry of the function", line_of(other, 'place "ode_third" {'), odec.places, self.source(other), "both")
        self.refused("has no entry `ode_third`", None, odec.places, self.source(TWO), "both", "ode_third")
        looped = changed(SCAN, "  // what holds each time the code comes here\n  place {", "  for k in 0..2 {\n  place {").replace("  cmp rcx, rsi\n", "  }\n  cmp rcx, rsi\n")
        self.refused("a place inside a for or an inline function", line_of(looped, "  place {"), odec.instructions, looped, "all_zero", "s.ode")
        inline = "inline fn step(i: gpr) changes i {\n  place {\n    decreases i\n  }\n  add i, 1\n}\n\n" + WITHOUT
        self.refused("a place or an entry inside an inline function", 2, odec.instructions, inline, "all_zero", "s.ode")
        open_ = changed(SCAN, "    decreases n - i\n  }\n", "    decreases n - i\n")
        self.refused("the `}` that ends this is missing", line_of(open_, "  place {"), odec.instructions, open_, "all_zero", "s.ode")

    def test_a_kernels_place_for_kcheck_stands_beside(self):
        """`place B { ... }` (kfn.py's, with its count's name) is read as before, and goes into the object."""
        both = changed(SCAN, "  cmp rcx, rsi\n", "  place b {\n    keep rsp\n  }\n  cmp rcx, rsi\n")
        src = self.source(both)
        self.assertEqual(odec.places(src, "all_zero"), PLACE)
        self.assertEqual(odec.place_of(src, "all_zero"), {"registers": {"rsp": "keep"}, "vectors": {}, "frame": {}})
        self.assertIn(".ode.place", odec.assembly(src, "all_zero"))
        self.assertNotIn(".ode.place", odec.assembly(self.source(SCAN), "all_zero"))

    def test_the_sources_places_are_those_of_the_kept_proofs(self):
        for source, fn, entry, symbol in KEPT:
            with self.subTest(symbol=symbol):
                got = [int(h, 16) for h in re.findall(r"^place \+0x([0-9a-f]+) \{$", odec.places(str(ROOT / source), fn, entry), re.M)]
                kept = (ROOT / "proof-core" / "proofs" / f"{symbol}.proof").read_text()
                part = kept[kept.index(f"for {symbol}\n"):]
                part = part[:part.index("\nfor ", 1)] if "\nfor " in part[1:] else part
                self.assertEqual(got, [int(n) for n in re.findall(r"^place (\d+)$", part, re.M)])
                self.assertGreaterEqual(len(got), 1)


if __name__ == "__main__": unittest.main()
