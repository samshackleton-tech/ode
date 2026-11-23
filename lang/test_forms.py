"""Names for registers, `:=`, and a frame of named fields (odec.py).

`reg NAME = REGISTER` gives a register a name for the rest of the function. `DST := SRC` is one `mov` (or
one `lea`, for the address of a field), fixed by what stands on its two sides; sides of two sizes are
refused. `frame { ... }` says the function's frame as fields in order; a slot `FIELD[I]` is `[rsp + N]`, and
a slot outside its field is refused at its line. Each form gives the instructions that the same function
has with every instruction written out, and nothing else.

    python3 test_forms.py"""
from pathlib import Path
import sys, tempfile, unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "lang"))
import odec

# A function with a frame: it fills a table of four addresses, calls another function with the table and a
# place for two results, and gives back the second result's first eight bytes.
NAMED = """fn fill as "ode_fill" {
  reg out = rbx
  reg tmp = rax

  frame {
    table: 4 * u64
    got:   2 * cv
    pad:   8
  }

  push out
  sub rsp, frame.size
  out := rdi
  tmp := rsi
  table[0] := tmp
  for i in 1..4 {
    tmp := rdx
    table[$i] := tmp
  }
  tmp := qword [out + 32]
  or tmp, 4
  r8 := tmp
  rdi := &table
  rsi := 1
  r9 := &got
  call ode_other
  for w in 0..2 {
    tmp := got.u64[4 + $w]
    qword [out + $w * 8] := tmp
  }
  byte [out + 16] := 7
  tmp := 0
  add rsp, frame.size
  pop out
  ret
}
"""
RAW = """fn fill as "ode_fill" {
  push rbx
  sub rsp, 104
  mov rbx, rdi
  mov rax, rsi
  mov qword ptr [rsp + 0], rax
  mov rax, rdx
  mov qword ptr [rsp + 8], rax
  mov rax, rdx
  mov qword ptr [rsp + 16], rax
  mov rax, rdx
  mov qword ptr [rsp + 24], rax
  mov rax, qword ptr [rbx + 32]
  or rax, 4
  mov r8, rax
  lea rdi, [rsp + 0]
  mov rsi, 1
  lea r9, [rsp + 32]
  call ode_other
  mov rax, qword ptr [rsp + 64]
  mov qword ptr [rbx + 0], rax
  mov rax, qword ptr [rsp + 72]
  mov qword ptr [rbx + 8], rax
  mov byte ptr [rbx + 16], 7
  mov rax, 0
  add rsp, 104
  pop rbx
  ret
}
"""


def changed(text, old, new):
    assert text.count(old) == 1, old
    return text.replace(old, new)


def line_of(text, piece):
    got = [i + 1 for i, line in enumerate(text.split("\n")) if piece in line]
    assert len(got) == 1, (piece, got)
    return got[0]


class Forms(unittest.TestCase):
    def built(self, text, name):
        with tempfile.TemporaryDirectory() as d:
            src, obj = Path(d) / "s.ode", Path(d) / "s.o"
            src.write_text(text)
            odec.build(str(src), name, str(obj))
            return obj.read_bytes()

    def refused(self, text, piece, said, name="fill"):
        """The source is refused at the one line that holds `piece`, in those words."""
        with self.assertRaises(SystemExit) as stopped: odec.instructions(text, name, "s.ode")
        self.assertEqual(str(stopped.exception).split(": ", 2)[:2], ["s.ode", f"line {line_of(text, piece)}"], str(stopped.exception))
        self.assertIn(said, str(stopped.exception))

    def test_the_forms_are_the_instructions_written_out(self):
        self.assertEqual(odec.instructions(NAMED, "fill"), odec.instructions(RAW, "fill"))
        self.assertEqual(self.built(NAMED, "fill"), self.built(RAW, "fill"))

    def test_a_name_stands_for_its_register_in_operands_only(self):
        text = "inline fn twice(d: gpr) changes d {\n  add d, d\n}\n\nfn f as \"ode_f\" {\n  reg add = rcx\n  reg i = rsi\n  add add, i\n  twice(i)\n  @i:\n  jmp @i\n  mov rax, qword ptr [i + 8]\n  ret\n}\n"
        self.assertEqual(odec.instructions(text, "f"), ["add rcx, rsi", "add rsi, rsi", ".Lode_f_i:", "jmp .Lode_f_i", "mov rax, qword ptr [rsi + 8]", "ret"])
        # a name is known from its line on, and not inside an inline function
        early = changed(NAMED, "  push out\n", "  push tmp2\n  reg tmp2 = rcx\n")
        self.assertIn("push tmp2", odec.instructions(early, "fill"))
        inner = "inline fn bad(d: gpr) changes d {\n  add d, i\n}\n\nfn f as \"ode_f\" {\n  reg i = rsi\n  bad(i)\n  ret\n}\n"
        with self.assertRaises(SystemExit) as stopped: odec.instructions(inner, "f", "s.ode")
        self.assertIn("`add rsi, i`", str(stopped.exception))
        # `call` takes a linker's name: a register's name there is refused, and a name is known only from its line on
        self.refused(changed(NAMED, "  call ode_other\n", "  call tmp\n"), "call tmp", "`tmp` is the name of a register here (rax), and `call` takes the name a linker knows a function by")
        self.assertIn("call CALL(later)", odec.instructions(changed(NAMED, "  call ode_other\n", "  call later\n  reg later = rcx\n"), "fill"))

    def test_a_name_that_cannot_be_given_is_refused(self):
        for new, said in (("  reg out = rbx\n  reg out = rcx\n", "`out` is a name already"),
                          ("  reg out = rbx\n  reg rcx = rbx\n", "a register cannot be named `rcx`"),
                          ("  reg out = rbx\n  reg qword = rcx\n", "a register cannot be named `qword`"),
                          ("  reg out = rbx\n  reg low = rbq\n", "`rbq` is no register")):
            with self.subTest(new=new): self.refused(changed(NAMED, "  reg out = rbx\n", new), new.split("\n")[1].strip(), said)
        looped = changed(NAMED, "    tmp := rdx\n", "    reg again = rcx\n    tmp := rdx\n")
        self.refused(looped, "reg again = rcx", "a name for a register inside a for or an inline function")
        self.refused(changed(NAMED, "    pad:   8\n", "    pad:   8\n    out:   8\n"), "out:   8", "`out` is a name already")
        self.refused(changed(NAMED, "  push out\n", "  reg table = rcx\n  push out\n"), "reg table = rcx", "`table` is a name already")

    def test_each_store_is_one_instruction(self):
        for form, instruction in (("rax := rcx", "mov rax, rcx"), ("eax := ecx", "mov eax, ecx"), ("rax := 1 + 2 * 3", "mov rax, 7"), ("rax := -1", "mov rax, -1"),
                                  ("rax := qword [rdi + 8]", "mov rax, qword ptr [rdi + 8]"), ("eax := dword [rdi]", "mov eax, dword ptr [rdi + 0]"),
                                  ("rax := qword [rdi + rsi + 4 * 4 - 8]", "mov rax, qword ptr [rdi + rsi + 8]"), ("rax := qword [rdi - 8]", "mov rax, qword ptr [rdi - 8]"),
                                  ("qword [rsp + (1 + 1) * 8] := rax", "mov qword ptr [rsp + 16], rax"), ("byte [rdi + 3] := 65", "mov byte ptr [rdi + 3], 65"),
                                  ("byte [rdi] := al", "mov byte ptr [rdi + 0], al"), ("dword [rdi] := 65", "mov dword ptr [rdi + 0], 65"), ("ax := cx", "mov ax, cx")):
            with self.subTest(form=form):
                self.assertEqual(odec.instructions(f"fn f as \"ode_f\" {{\n  {form}\n  ret\n}}\n", "f"), [instruction, "ret"])

    def test_a_store_that_is_not_one_instruction_is_refused(self):
        for form, said in (("qword [rdi] := qword [rsi]", "`:=` is one `mov`"), ("rax := &table", "`table` is no field of the function's frame"),
                           ("zmm0 := zmm1", "`zmm0` is moved by an instruction that the coder names"), ("rax := xmm1", "`xmm1` is moved by an instruction"),
                           ("5 := rax", "`:=` is one `mov`"), ("rax := qword [rdi * 2]", "an address of `:=` is a register (or two) and a number"),
                           ("rax := qword [8]", "an address of `:=` is a register (or two) and a number"), ("rax := qword [rdi + rsi + rdx]", "an address of `:=` is a register (or two) and a number"),
                           ("rax := qword [rdi - rsi]", "an address of `:=` is a register (or two) and a number"), ("rax := word [rdi]", "is nothing that `:=` moves"),
                           ("rax := rcx + 1", "is nothing that `:=` moves"), ("rax := table[0]", "`table` is no field of the function's frame")):
            with self.subTest(form=form):
                text = f"fn f as \"ode_f\" {{\n  {form}\n  ret\n}}\n"
                self.refused(text, form, said, "f")

    def test_the_two_sides_of_a_store_have_one_size(self):
        """`:=` never widens or cuts: where both sides have a size, a store of two sizes is refused at its line."""
        for form, said in (("rax := ecx", "`rax` has 8 and `ecx` has 4"), ("eax := rcx", "`eax` has 4 and `rcx` has 8"), ("al := ecx", "`al` has 1 and `ecx` has 4"),
                           ("byte [rdi] := rax", "`byte [rdi]` has 1 and `rax` has 8"), ("rax := byte [rdi]", "`rax` has 8 and `byte [rdi]` has 1"),
                           ("dword [rdi + 4] := rax", "`dword [rdi + 4]` has 4 and `rax` has 8"), ("eax := qword [rdi]", "`eax` has 4 and `qword [rdi]` has 8"),
                           ("qword [rdi] := al", "`qword [rdi]` has 8 and `al` has 1"), ("ax := byte [rdi]", "`ax` has 2 and `byte [rdi]` has 1")):
            with self.subTest(form=form):
                self.refused(f"fn f as \"ode_f\" {{\n  {form}\n  ret\n}}\n", form, "`:=` moves as many bytes as both sides have: " + said, "f")
        for old, new, said in (("  table[0] := tmp\n", "  table[0] := eax\n", "`table[0]` has 8 and `eax` has 4"),
                               ("    tmp := got.u64[4 + $w]\n", "    tmp := pad.u32[$w]\n", "`tmp` has 8 and `pad.u32[0]` has 4"),          # (the side as it was typed, the first turn's number in it)
                               ("    tmp := got.u64[4 + $w]\n", "    al := got.u64[4 + $w]\n", "`al` has 1 and `got.u64[4 + 0]` has 8"),
                               ("  rdi := &table\n", "  edi := &table\n", "`edi` has 4 and `&table` has 8")):
            with self.subTest(new=new): self.refused(changed(NAMED, old, new), new.strip(), "`:=` moves as many bytes as both sides have: " + said)

    def test_a_slot_outside_its_field_is_refused(self):
        for old, new, said in (("  table[0] := tmp\n", "  table[4] := tmp\n", "`table[4]`: the slots of `table` are 0 to 3"),
                               ("  table[0] := tmp\n", "  table[0 - 1] := tmp\n", "`table[0 - 1]`: the slots of `table` are 0 to 3"),
                               ("    tmp := got.u64[4 + $w]\n", "    tmp := got.u64[7 + $w]\n", "`got.u64[7 + 1]`: the slots of `got.u64` are 0 to 7"),
                               ("  table[0] := tmp\n", "  got[0] := tmp\n", "`:=` moves 1, 4 or 8 bytes, and a slot of `got` has 32"),
                               ("  table[0] := tmp\n", "  missing[0] := tmp\n", "`missing` is no field of the function's frame"),
                               ("  r9 := &got\n", "  r9 := &gone\n", "`gone` is no field of the function's frame"),
                               ("  table[0] := tmp\n", "  table[rcx] := tmp\n", "a slot is a number: not `rcx`"),
                               ("    tmp := got.u64[4 + $w]\n", "    tmp := got.wide[4 + $w]\n", "`wide` is no kind of a field"),
                               ("    tmp := got.u64[4 + $w]\n", "    tmp := pad.cv[$w]\n", "`pad` has 8 bytes: not a whole count of cv"),
                               ("    tmp := got.u64[4 + $w]\n", "    eax := pad.u32[$w]\n", None)):
            with self.subTest(new=new):
                text = changed(NAMED, old, new)
                if said is None: self.assertIn("mov eax, dword ptr [rsp + 100]", odec.instructions(text, "fill"))        # (the bytes of a field as another kind)
                else: self.refused(text, new.strip(), said)
        # the loop's last turn is the one refused: the table's fifth slot
        self.refused(changed(NAMED, "  for i in 1..4 {\n", "  for i in 1..5 {\n"), "table[$i] := tmp", "`table[4]`: the slots of `table` are 0 to 3")

    def test_a_frame_that_cannot_be_read_is_refused(self):
        for old, new, said in (("    table: 4 * u64\n", "    table: 4 * wide\n", "`wide` is no kind of a field"),
                               ("    table: 4 * u64\n", "    table: 0 * u64\n", "a field holds a count of things, one or more"),
                               ("    table: 4 * u64\n", "    table 4 u64\n", "a field of a frame is `NAME: COUNT * KIND` or `NAME: BYTES`"),
                               ("    got:   2 * cv\n", "    table: 2 * cv\n", "`table` is a name already"),
                               ("    got:   2 * cv\n", "    rsp:   2 * cv\n", "a field cannot be named `rsp`"),
                               ("    pad:   8\n", "    pad:   n\n", "a field holds a count of things, one or more")):
            with self.subTest(new=new): self.refused(changed(NAMED, old, new), new.strip(), said)
        twice = changed(NAMED, "  push out\n", "  frame {\n    more: 8\n  }\n  push out\n")
        with self.assertRaises(SystemExit) as stopped: odec.instructions(twice, "fill", "s.ode")
        self.assertIn("a second frame", str(stopped.exception))
        none = "fn f as \"ode_f\" {\n  sub rsp, frame.size\n  ret\n}\n"
        self.refused(none, "frame.size", "`frame.size`, and fn f has said no frame yet", "f")
        empty = "fn f as \"ode_f\" {\n  frame {\n  }\n  ret\n}\n"
        self.refused(empty, "frame {", "a frame with no field", "f")
        inline = "inline fn put(r: gpr) {\n  table[0] := r\n}\n\n" + changed(NAMED, "  table[0] := tmp\n", "  put(tmp)\n")
        self.refused(inline, "table[0] := r", "a field of the frame inside an inline function")

    def test_the_frames_size_and_its_fields_addresses(self):
        got = odec.instructions(NAMED, "fill")
        self.assertEqual(got[1], "sub rsp, 104")                      # 4 * 8 + 2 * 32 + 8
        self.assertIn("lea rdi, [rsp + 0]", got)
        self.assertIn("lea r9, [rsp + 32]", got)
        wider = changed(NAMED, "    table: 4 * u64\n", "    table: 2 * 4 * u64\n")
        self.assertEqual(odec.instructions(wider, "fill")[1], "sub rsp, 136")
        self.assertIn("lea r9, [rsp + 64]", odec.instructions(wider, "fill"))


if __name__ == "__main__": unittest.main()
