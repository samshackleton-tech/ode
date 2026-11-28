"""Inline functions in odec.py.

A use of an inline function is the function's instructions, with the registers given put for its parameters,
and nothing else. What breaks the function's head is refused at its line: a register of another class, one
register for two that must differ, a register named outright in the function, a register changed that
`changes` does not list. The text macro (`def`) these take the place of is refused, and no source of the
repository has one.

    python3 test_inline.py"""
from pathlib import Path
import re, sys, tempfile, unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "lang"))
import odec

MIX = """target x86_64

inline fn mix16(d: zmm, a: zmm) distinct(d, a) changes d {
  vpxord d, d, a
  vprord d, d, 16
}

fn mix16_3 as "ode_mix16_3" {
  vmovdqu32 zmm0, [rsi + 0]
  vmovdqu32 zmm1, [rdx + 0]
  mix16(zmm0, zmm1)
  mix16(zmm1, zmm0)
  mix16(zmm0, zmm1)
  vmovdqu32 [rdi + 0], zmm0
  vzeroupper
  ret
}
"""
RAW = """fn mix16_3 as "ode_mix16_3" {
  vmovdqu32 zmm0, [rsi + 0]
  vmovdqu32 zmm1, [rdx + 0]
  vpxord zmm0, zmm0, zmm1
  vprord zmm0, zmm0, 16
  vpxord zmm1, zmm1, zmm0
  vprord zmm1, zmm1, 16
  vpxord zmm0, zmm0, zmm1
  vprord zmm0, zmm0, 16
  vmovdqu32 [rdi + 0], zmm0
  vzeroupper
  ret
}
"""
# A loop of its own in an inline function: the count in `n` down to zero, `d` doubled each turn.
LOOP = """inline fn doubled(d: gpr, n: gpr) distinct(d, n) changes d, n {
  @again:
  add d, d
  dec n
  jne @again
}

fn twice as "ode_twice" {
  doubled(rax, rcx)
  doubled(rdx, rsi)
  ret
}
"""
LOOP_RAW = """fn twice as "ode_twice" {
  @first:
  add rax, rax
  dec rcx
  jne @first
  @second:
  add rdx, rdx
  dec rsi
  jne @second
  ret
}
"""


def changed(text, old, new):
    assert text.count(old) == 1, old
    return text.replace(old, new)


def line_of(text, piece):
    """The number of the one line of a source that holds `piece`."""
    got = [i + 1 for i, line in enumerate(text.split("\n")) if piece in line]
    assert len(got) == 1, (piece, got)
    return got[0]


class Inline(unittest.TestCase):
    def built(self, text, name):
        with tempfile.TemporaryDirectory() as d:
            src, obj = Path(d) / "s.ode", Path(d) / "s.o"
            src.write_text(text)
            odec.build(str(src), name, str(obj))
            return obj.read_bytes()

    def refused(self, text, name, line, said):
        """The source is refused at that line, in those words."""
        with self.assertRaises(SystemExit) as stopped: odec.instructions(text, name, "s.ode")
        self.assertEqual(str(stopped.exception).split(": ", 2)[:2], ["s.ode", f"line {line}"], str(stopped.exception))
        self.assertIn(said, str(stopped.exception))

    def test_a_use_is_the_instructions_and_nothing_else(self):
        self.assertEqual(odec.instructions(MIX, "mix16_3"), odec.instructions(RAW, "mix16_3"))
        self.assertEqual(self.built(MIX, "mix16_3"), self.built(RAW, "mix16_3"))

    def test_a_label_is_each_uses_own(self):
        got = odec.instructions(LOOP, "twice")
        self.assertEqual(len([s for s in got if s.endswith(":")]), 2)
        self.assertEqual(len(set(s for s in got if s.endswith(":"))), 2)
        self.assertEqual(self.built(LOOP, "twice"), self.built(LOOP_RAW, "twice"))
        # a label, a loop's `$i` and a name of data are not parameters, whatever they are called
        named = LOOP.replace("@again", "@n")
        self.assertEqual(self.built(named, "twice"), self.built(LOOP_RAW, "twice"))
        # a label that is not the inline function's own is the function's: the jump leaves the use
        out = "inline fn unless_zero(n: gpr) {\n  cmp n, n\n  jne @out\n}\n\nfn f as \"ode_f\" {\n  unless_zero(rdi)\n  add rax, rax\n  @out:\n  ret\n}\n"
        self.assertEqual(odec.instructions(out, "f"), ["cmp rdi, rdi", "jne .Lode_f_out", "add rax, rax", ".Lode_f_out:", "ret"])

    def test_a_use_in_a_for_and_in_another_inline_function(self):
        text = changed(MIX, "  mix16(zmm0, zmm1)\n  mix16(zmm1, zmm0)\n  mix16(zmm0, zmm1)\n", "  for i in 0..3 {\n    mix16(zmm$i, zmm7)\n  }\n")
        self.assertEqual(odec.instructions(text, "mix16_3")[2:8], [f"{op} zmm{i}, zmm{i}, {last}" for i in range(3) for op, last in (("vpxord", "zmm7"), ("vprord", "16"))])
        text = changed(MIX, "fn mix16_3", "inline fn both(p: zmm, q: zmm) distinct(p, q) changes p, q {\n  mix16(p, q)\n  mix16(q, p)\n}\n\nfn mix16_3")
        text = changed(text, "  mix16(zmm0, zmm1)\n  mix16(zmm1, zmm0)\n  mix16(zmm0, zmm1)\n", "  both(zmm0, zmm1)\n  mix16(zmm0, zmm1)\n")
        self.assertEqual(odec.instructions(text, "mix16_3"), odec.instructions(RAW, "mix16_3"))

    def test_a_register_of_another_class_is_refused_at_the_use(self):
        text = changed(MIX, "  mix16(zmm1, zmm0)\n", "  mix16(rax, zmm0)\n")
        self.refused(text, "mix16_3", line_of(text, "mix16(rax, zmm0)"), "`d` is a register of the class zmm, and `rax` is not one")
        text = changed(MIX, "  mix16(zmm1, zmm0)\n", "  mix16(zmm1, xmm0)\n")
        self.refused(text, "mix16_3", line_of(text, "mix16(zmm1, xmm0)"), "`a` is a register of the class zmm, and `xmm0` is not one")

    def test_one_register_for_two_that_must_differ_is_refused_at_the_use(self):
        text = changed(MIX, "  mix16(zmm1, zmm0)\n", "  mix16(zmm1, zmm1)\n")
        self.refused(text, "mix16_3", line_of(text, "mix16(zmm1, zmm1)"), "`d` and `a` must differ, and both are given zmm1")
        # two names of one register: its whole and a part of it
        text = changed(changed(MIX, "(d: zmm, a: zmm)", "(d: zmm, a: xmm)"), "  vpxord d, d, a\n", "")
        text = text.replace("mix16(zmm0, zmm1)", "mix16(zmm0, xmm1)").replace("mix16(zmm1, zmm0)", "mix16(zmm1, xmm1)")
        self.refused(text, "mix16_3", line_of(text, "mix16(zmm1, xmm1)"), "`d` and `a` must differ, and zmm1 and xmm1 are parts of one register")
        # without `distinct` nothing is asked
        self.assertEqual(len(odec.instructions(changed(changed(MIX, " distinct(d, a)", ""), "  mix16(zmm1, zmm0)\n", "  mix16(zmm1, zmm1)\n"), "mix16_3")), 11)

    def test_a_register_named_outright_in_the_function_is_refused_at_its_line(self):
        text = changed(MIX, "  vprord d, d, 16\n", "  vprord zmm2, d, 16\n")
        self.refused(text, "mix16_3", line_of(text, "vprord zmm2, d, 16"), "names the register `zmm2`")
        text = changed(MIX, "  vprord d, d, 16\n", "  vprord d, d, 16\n  mov eax, 1\n")
        self.refused(text, "mix16_3", line_of(text, "mov eax, 1"), "names the register `eax`")

    def test_a_change_of_a_register_that_changes_does_not_list_is_refused_at_its_line(self):
        text = changed(MIX, "  vprord d, d, 16\n", "  vprord a, d, 16\n")
        self.refused(text, "mix16_3", line_of(text, "vprord a, d, 16"), "mix16, used at line 11: `vprord zmm1, zmm0, 16` changes zmm1, which `changes` of mix16 does not list")
        # without `changes`, no register may be changed
        text = changed(MIX, " changes d {", " {")
        self.refused(text, "mix16_3", line_of(text, "vpxord d, d, a"), "changes zmm0, which `changes` of mix16 does not list")
        # a part of a register is the register: a 32-bit name written changes the whole
        low = "inline fn zero(d: gpr32) {\n  xor d, d\n}\n\nfn f as \"ode_f\" {\n  zero(ecx)\n  ret\n}\n"
        self.refused(low, "f", 2, "`xor ecx, ecx` changes rcx")
        self.assertEqual(odec.instructions(changed(low, "(d: gpr32) {", "(d: gpr32) changes d {"), "f"), ["xor ecx, ecx", "ret"])
        # the flags and bytes of memory are not registers
        quiet = "inline fn put(b: gpr, s: gpr) {\n  cmp s, b\n  mov qword ptr [b + 8], s\n}\n\nfn f as \"ode_f\" {\n  put(rdi, rax)\n  ret\n}\n"
        self.assertEqual(odec.instructions(quiet, "f"), ["cmp rax, rdi", "mov qword ptr [rdi + 8], rax", "ret"])
        # an inline function used in another: the outer one's `changes` holds for the inner one's instructions too
        text = changed(MIX, "fn mix16_3", "inline fn outer(p: zmm, q: zmm) changes q {\n  mix16(p, q)\n}\n\nfn mix16_3")
        text = changed(text, "  mix16(zmm1, zmm0)\n", "  outer(zmm1, zmm0)\n")
        self.refused(text, "mix16_3", line_of(text, "vpxord d, d, a"), f"outer, used at line {line_of(text, 'outer(zmm1, zmm0)')}: `vpxord zmm1, zmm1, zmm0` changes zmm1, which `changes` of outer does not list")

    def test_a_head_that_cannot_be_read_is_refused(self):
        head = line_of(MIX, "inline fn mix16")
        for old, new, said in (
                ("(d: zmm, a: zmm)", "(d: wide, a: zmm)", "`wide` is no class of register"),
                ("(d: zmm, a: zmm)", "(d, a: zmm)", "a parameter is `NAME: CLASS`, not `d`"),
                ("(d: zmm, a: zmm)", "(d: zmm, d: zmm)", "two parameters are named `d`"),
                ("(d: zmm, a: zmm) distinct(d, a)", "(d: zmm, rax: zmm) distinct(d, rax)", "a parameter cannot have a register's name, `rax`"),
                ("distinct(d, a)", "distinct(d, q)", "`distinct` names `q`, which is not a parameter"),
                ("distinct(d, a)", "distinct(d, d)", "`distinct` names `d` twice"),
                ("changes d", "changes q", "`changes` names `q`, which is not a parameter"),
                ("distinct(d, a) changes d", "changes d distinct(d, a)", "after the parameters comes `distinct(P, Q)`, then `changes P, ...`"),
                ("distinct(d, a) changes d", "keeps a", "after the parameters comes `distinct(P, Q)`, then `changes P, ...`")):
            with self.subTest(new=new): self.refused(changed(MIX, old, new), "mix16_3", head, said)
        self.refused(changed(MIX, "fn mix16_3", "inline fn mix16(d: zmm) {\n}\n\nfn mix16_3"), "mix16_3", line_of(MIX, "fn mix16_3 as"), "a second inline fn mix16")
        self.refused(changed(MIX, "(d: zmm, a: zmm)", "(d: zmm, mix16: zmm)").replace("distinct(d, a) ", ""), "mix16_3", head, "the parameter `mix16` has an inline function's name")

    def test_a_use_that_cannot_stand_is_refused_at_its_line(self):
        text = changed(MIX, "  mix16(zmm1, zmm0)\n", "  mix16(zmm1)\n")
        self.refused(text, "mix16_3", line_of(text, "mix16(zmm1)"), "mix16 takes 2 registers, not 1")
        text = changed(MIX, "  mix16(zmm1, zmm0)\n", "  mix61(zmm1, zmm0)\n")
        self.refused(text, "mix16_3", line_of(text, "mix61(zmm1, zmm0)"), "`mix61` is no inline function of this source")
        text = changed(MIX, "  vprord d, d, 16\n", "  vprord d, d, 16\n  mix16(a, d)\n")
        self.refused(text, "mix16_3", line_of(text, "mix16(a, d)"), "the inline function mix16 uses itself")
        text = changed(MIX, "  vprord d, d, 16\n", "  vprord d, d, 16\n  call ode_other\n")
        self.refused(text, "mix16_3", line_of(text, "call ode_other"), "a call inside an inline function: not here yet")
        text = changed(MIX, "  vprord d, d, 16\n", "  vprord d, d, 16\n  place b {\n  }\n")
        self.refused(text, "mix16_3", line_of(text, "place b {"), "a place or an entry inside an inline function")
        text = changed(MIX, "  vprord d, d, 16\n", "  imul d, d, 16\n")
        self.refused(text, "mix16_3", line_of(text, "imul d, d, 16"), "`imul zmm0, zmm0, 16`")

    def test_the_head_may_go_over_lines(self):
        text = changed(MIX, "inline fn mix16(d: zmm, a: zmm) distinct(d, a) changes d {", "inline fn mix16(d: zmm,     // the one mixed\n                a: zmm)     // the one mixed in\n    distinct(d, a)\n    changes d {")
        self.assertEqual(odec.instructions(text, "mix16_3"), odec.instructions(RAW, "mix16_3"))
        text = changed(text, "  vprord d, d, 16\n", "  vprord a, d, 16\n")
        self.refused(text, "mix16_3", line_of(text, "vprord a, d, 16"), "changes zmm1")

    def test_the_target(self):
        self.refused(changed(MIX, "target x86_64", "target aarch64"), "mix16_3", 1, "odec.py makes code for x86_64, arm64 only, not for aarch64")
        self.refused(changed(MIX, "fn mix16_3", "target x86_64\nfn mix16_3"), "mix16_3", line_of(MIX, "fn mix16_3 as"), "`target` stands once, before the functions")
        self.assertEqual(odec.instructions(changed(MIX, "target x86_64\n", ""), "mix16_3"), odec.instructions(RAW, "mix16_3"))

    def test_the_text_macro_is_gone(self):
        text = changed(RAW, "  vmovdqu32 zmm0, [rsi + 0]\n", "  def mix16(dst, src) {\n    vpxord $dst, $dst, $src\n  }\n  vmovdqu32 zmm0, [rsi + 0]\n")
        self.refused(text, "mix16_3", 2, "`def` is not a form of Ode any more")
        sources = sorted(ROOT.glob("**/*.ode"))
        self.assertGreaterEqual(len(sources), 25)
        for path in sources:
            with self.subTest(source=str(path.relative_to(ROOT))):
                # Indented `def` text macros inside function bodies are forbidden (top-level `def` is a pure spec definition)
                self.assertIsNone(re.search(r"^[ \t]+def\s", path.read_text(), re.M))


if __name__ == "__main__": unittest.main()
