"""The table assembler (../core/asm.py), as odec.py uses it.

Each Ode function of the sources is the same bytes as the independent clang build of it. An instruction is
laid down as the instruction it names, or it is refused: every instruction of the sources is changed in
every way of a list (another name, another kind of operand, an operand fewer or more), and what the table
assembler then takes must be what clang writes for the same text. A size word before a memory operand
(`byte ptr`, `qword ptr`, ...) is read: one that disagrees with what the instruction moves there is
refused. And a refusal names the source line.

    python3 test_asm.py"""
from pathlib import Path
import re, shutil, subprocess, sys, tempfile, unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT / "kcheck"), str(ROOT / "core"), str(ROOT / "arm64")]
import asm, kdecode, obj as aobj, odec

# The names that asm.py has a branch for, and some that it has none for (those are refused whatever follows).
NAMES = ("""nop endbr64 ret vzeroupper prefetcht0 jmp je jz jne jnz jae jb ja jbe call push pop dec test xor shl shr add sub and or cmp lea movzx mov
            cmove cmovz cmovne cmovnz cmovb cmovc cmovae cmovnc cmova cmovnbe cmovbe cmovna
            movq vmovq movups vmovups vmovdqu movaps vmovaps movdqa vmovdqa vmovdqa32 vmovdqu32 pslld vpslld psrld vpsrld pshufb pblendw pshufd vpshufd shufps
            vshufps vpblendd vpalignr sha256rnds2 sha256msg1 sha256msg2 vprord vpbroadcastd vpcmpud vshufi32x4 paddd vpaddd pxor vpxor vpxord pand vpand por vpor punpckldq vpunpckldq punpckhdq
            vpunpckhdq punpcklqdq vpunpcklqdq vpunpckhqdq""".split())
STRANGERS = "imul neg not adc sbb inc xchg bswap setb movsx movsxd movdqu vmovdqu8 vmovdqu64 vmovdqa64 vpxorq vpord".split()
# An operand of each kind, to stand where another stood.
OTHERS = (["rcx", "ecx", "cx", "cl", "al", "xmm5", "ymm5", "zmm5", "zmm5 {k2}", "k2", "7", "[rdi + 8]", "[rdi + rsi + 8]"]
          + [f"{word} ptr [rdi + 8]" for word in ("byte", "word", "dword", "qword", "xmmword", "ymmword", "zmmword")])


def parts(line):
    mn, _, rest = line.partition(" ")
    return mn, [o.strip() for o in rest.split(",")] if rest.strip() else []


def iter_ode_targets(path):
    """Yield `(target, fns)` for every architecture implemented in `path` (skips spec-only `.ode` files)."""
    text = path.read_text()
    try:
        target, _, _, fns = odec.source(text, str(path))
        if fns:
            yield target, fns
        return
    except Exception as e:
        msg = str(e)
        if "multiple architectures" not in msg:
            return
    for tgt in ("arm64", "x86_64"):
        try:
            target, _, _, fns = odec.source(text, str(path), target=tgt)
            if fns:
                yield target, fns
        except Exception:
            pass


def shapes():
    """One instruction of each shape that the x86-64 sources have (its name; each operand's class and size word; whether
    memory is the file's data, and whether it has an index): the first one met."""
    seen = {}
    for path in sorted(ROOT.glob("**/*.ode")):
        text = path.read_text()
        for target, fns in iter_ode_targets(path):
            if target != "x86_64": continue
            for name, _, _, _ in fns:
                for x in odec.instructions(text, name, str(path), target=target):
                    if x.endswith(":") or x.startswith("."): continue
                    mn, ops = parts(x)
                    seen.setdefault((mn,) + tuple(asm.operand(o) + ("rip" in o, o.count("+") > 1) for o in ops), x)
    return list(seen.values())


def changed(line):
    """The instruction with each operand replaced in turn by an operand of each other kind, with an operand
    fewer and with one more, and under each other name."""
    mn, ops = parts(line)
    out = []
    for i in range(len(ops)):
        out += [mn + " " + ", ".join(ops[:i] + [other] + ops[i + 1:]) for other in OTHERS if other != ops[i]]
    if ops: out.append((mn + " " + ", ".join(ops[:-1])).strip())
    out += [line + (", " if ops else " ") + more for more in ("rcx", "7")]
    out += [(other + " " + ", ".join(ops)).strip() for other in NAMES + STRANGERS if other != mn]
    return out


def table(line):
    """The bytes the table assembler writes for an instruction; None where it refuses (a jump or a call is
    written only within a function: its form alone is asked here)."""
    try: item = asm.instruction(line)
    except ValueError: return None
    return None if item[0] == "jump" else bytes(item[1])


def by_clang(lines, folder):
    """For each instruction, the bytes clang writes for it; None where clang refuses it."""
    source, obj = Path(folder) / "lines.s", Path(folder) / "lines.o"
    data = sorted({name for line in lines for name in re.findall(r"\.Lode_data_\w+", line)})
    head = ".intel_syntax noprefix\n.data\n" + "".join(f"{name}:\n" for name in data) + ".long 1\n.text\n"
    refused = set()
    while True:
        text = "".join(f"at_{k}:\n" + ("" if k in refused else f"    {line}\n") for k, line in enumerate(lines))
        source.write_text(head + re.sub(r"CALL\((\w+)\)", r"\1@PLT", text) + f"at_{len(lines)}:\n")            # (CALL(f): how odec's listing writes a function's name)
        r = subprocess.run(["clang", "--target=x86_64-unknown-linux-gnu", "-c", "-o", str(obj), str(source)], capture_output=True, text=True)
        if r.returncode == 0: break
        more = {(int(m.group(1)) - head.count("\n") - 1) // 2 for m in re.finditer(r"lines\.s:(\d+):\d+: error", r.stderr)} - refused
        if not more: raise AssertionError(r.stderr[:1000])
        refused |= more
    elf = kdecode.Elf(obj)
    code, at = elf.bytes_of(".text"), [kdecode.address(elf.b, f"at_{k}") for k in range(len(lines) + 1)]
    return [None if k in refused else bytes(code[at[k]:at[k + 1]]) for k in range(len(lines))]


def read_back(blobs, folder):
    """Each run of bytes as a disassembler reads it: the instructions' text, without their bytes."""
    source, obj = Path(folder) / "bytes.s", Path(folder) / "bytes.o"
    source.write_text(".text\n" + "".join(f"at_{k}:\n    .byte " + ", ".join(str(b) for b in blob) + "\n" for k, blob in enumerate(blobs)))
    subprocess.run(["clang", "--target=x86_64-unknown-linux-gnu", "-c", "-o", str(obj), str(source)], check=True, capture_output=True)
    listing = subprocess.run(["objdump", "-d", "--no-show-raw-insn", str(obj)], check=True, capture_output=True, text=True).stdout
    read, k = [[] for _ in blobs], None
    for row in listing.splitlines():
        label = re.fullmatch(r"[0-9a-f]+ <at_(\d+)>:", row.strip())
        if label: k = int(label.group(1))
        elif k is not None and re.match(r"\s*[0-9a-f]+:\s", row): read[k].append(" ".join(row.split(":", 1)[1].split()))
    return read


@unittest.skipUnless(shutil.which("clang"), "clang is needed only for the comparison")
class Assembler(unittest.TestCase):
    def test_every_ode_function(self):
        with tempfile.TemporaryDirectory() as d:
            source, clang, own = (Path(d) / f for f in ("ref.S", "ref.o", "ode.o"))
            count = 0
            for path in sorted(ROOT.glob("**/*.ode")):
                for target, fns in iter_ode_targets(path):
                    for name, sym, _, _ in fns:
                        count += 1
                        with self.subTest(source=path.relative_to(ROOT), target=target, function=name):
                            source.write_text(odec.assembly(str(path), name, target=target))
                            odec.assemble(str(source), str(clang), target=target)
                            odec.build(str(path), name, str(own), target=target)
                            if target == "arm64":
                                self.assertEqual(aobj.words(str(own), sym)[0], aobj.words(str(clang), sym)[0])
                                self.assertEqual(aobj.read(str(own), sym), aobj.read(str(clang), sym))
                                continue
                            got, want = kdecode.Elf(own), kdecode.Elf(clang)
                            for section in (".text", ".rodata", ".ode.place", ".note.GNU-stack"):
                                self.assertEqual(got.bytes_of(section), want.bytes_of(section), section)
                                self.assertEqual(section in got.index, section in want.index, section)
                                if section in got.index:
                                    self.assertEqual(got.sections[got.index[section]]["align"], want.sections[want.index[section]]["align"], section)
                            self.assertEqual(got.relocations(".text"), want.relocations(".text"))
                            for entry in got.symbols:
                                if entry["bind"] != 1 or entry["shndx"] != got.index[".text"]: continue
                                self.assertEqual(entry["value"], kdecode.address(want.b, entry["name"]))
            self.assertGreaterEqual(count, 26)

    @unittest.skipUnless(shutil.which("objdump"), "objdump reads back the bytes that differ from clang's")
    def test_what_is_taken_is_the_instruction_named(self):
        """Each instruction of the sources, changed in each way of changed(): the table assembler refuses it, or
        writes the bytes clang writes for it, or bytes that a disassembler reads as the same instruction as
        clang's (another way of writing it; these are counted, and are few)."""
        kept = shapes()
        self.assertGreaterEqual(len(kept), 90)
        for x in kept:                                   # (the list of names is the whole of what the sources and the table have)
            self.assertIn(parts(x)[0], NAMES)
        for row, _ in asm.ROWS.values():
            if row.asm != "-": self.assertIn(row.asm.split()[0], NAMES)
        lines = list(dict.fromkeys(line for x in kept for line in [x] + changed(x)))
        self.assertGreaterEqual(len(lines), 10000)
        taken = [(line, table(line)) for line in lines]
        taken = [(line, mine) for line, mine in taken if mine is not None]
        self.assertGreaterEqual(len(taken), 600)
        with tempfile.TemporaryDirectory() as d:
            theirs = by_clang([line for line, _ in taken], d)
            other = [(line, mine, c) for (line, mine), c in zip(taken, theirs) if c is not None and c != mine]
            read = read_back([blob for _, mine, c in other for blob in (mine, c)], d) if other else []
        for (line, mine), c in zip(taken, theirs):
            with self.subTest(line=line): self.assertIsNotNone(c, f"the table writes {mine.hex()} for what clang refuses")
        for k, (line, mine, c) in enumerate(other):
            with self.subTest(line=line):
                self.assertEqual(len(read[2 * k]), 1, read[2 * k])
                self.assertEqual(read[2 * k], read[2 * k + 1], f"the table writes {mine.hex()} and clang {c.hex()}")
        self.assertLessEqual(len(other), 8, [line for line, _, _ in other])

    def test_what_the_table_lacks_is_refused(self):
        """The controls: an instruction with no row, an immediate too wide, an operand too many: no object,
        and the line is named."""
        text = (ROOT / "kcheck" / "programs" / "common" / "common.ode").read_text()
        old = "  mov r13, rax\n"
        self.assertGreaterEqual(text.count(old), 1)
        line = text[:text.index(old)].count("\n") + 1
        with tempfile.TemporaryDirectory() as d:
            src, obj = Path(d) / "changed.ode", Path(d) / "changed.o"
            for new in ("  imul r13, rax\n", "  mov r13d, 0x100000000\n", "  ret rax\n", "  mov r13, [rax + 0x80000000]\n"):
                with self.subTest(line=new.strip()):
                    src.write_text(text.replace(old, new, 1))
                    with self.assertRaises(SystemExit) as stopped: odec.build(str(src), "common", str(obj))
                    self.assertTrue(str(stopped.exception).startswith(f"{src}: line {line}: `{new.strip()}`: "), str(stopped.exception))
                    self.assertFalse(obj.exists())
            src.write_text(text)
            odec.build(str(src), "common", str(obj))
            self.assertTrue(obj.exists())


# An instruction with a memory operand, and the size word of what it moves there.
SIZED = [("mov rax, [rdi + 8]", "qword"), ("mov eax, [rdi + 8]", "dword"), ("mov [rdi + 8], rax", "qword"), ("mov [rdi + 8], al", "byte"),
         ("add rax, [rdi + 8]", "qword"), ("sub rax, [rdi + 8]", "qword"), ("cmp rax, [rdi + 8]", "qword"),
         ("movups xmm1, [rdi + 16]", "xmmword"), ("movups [rdi + 16], xmm1", "xmmword"), ("vmovdqu xmm1, [rdi + 16]", "xmmword"),
         ("movaps xmm1, [rip + .Lode_data_t]", "xmmword"),
         ("vmovdqu32 zmm1, [rdi + 64]", "zmmword"), ("vmovdqu32 [rdi + 64], zmm1", "zmmword"), ("vmovdqa32 zmm1, [rdi + 64]", "zmmword"),
         ("vmovdqu32 zmm1, [rdi + rsi + 64]", "zmmword"),
         ("vpbroadcastd zmm1, [rdi + 4]", "dword"), ("vpbroadcastd zmm1, [rip + .Lode_data_t]", "dword"),
         ("vpaddd zmm1, zmm2, [rdi + rsi + 64]", "zmmword"), ("vpaddd zmm1, zmm2, [rip + .Lode_data_t]", "zmmword")]
# Where no register says the size, the word must stand: a store of a number, and movzx from memory.
WORDED = [("mov [rdi + 8], 65", "byte", "x86.tab has a store of a number for one byte only"), ("movzx eax, [rdi + 8]", "byte", "movzx from memory needs the size word")]
WORDS = ("byte", "word", "dword", "qword", "xmmword", "ymmword", "zmmword")


def worded(line, word):
    """The instruction with a size word before its memory operand."""
    assert line.count("[") == 1, line
    return line.replace("[", f"{word} ptr [")


class Refused(unittest.TestCase):
    def said(self, body):
        """What odec.build says of a function with these lines; None where it builds."""
        with tempfile.TemporaryDirectory() as d:
            src, obj = Path(d) / "s.ode", Path(d) / "s.o"
            src.write_text("fn f as \"ode_f\" {\n" + body + "  ret\n}\n")
            try: odec.build(str(src), "f", str(obj))
            except SystemExit as e:
                self.assertFalse(obj.exists())
                return str(e).replace(str(src), "s.ode")
            return None

    def test_a_size_word_that_agrees_changes_nothing(self):
        for line, word in SIZED:
            with self.subTest(line=line):
                self.assertEqual(asm.instruction(worded(line, word)), asm.instruction(line))
                self.assertEqual(asm.instruction(worded(line, word.upper()).replace(" ptr ", " PTR ")), asm.instruction(line))
        for line, word, said in WORDED:
            with self.subTest(line=line):
                self.assertEqual(asm.instruction(worded(line, word))[0], "fixed")
                with self.assertRaises(ValueError) as stopped: asm.instruction(line)
                self.assertIn(said, str(stopped.exception))

    def test_a_size_word_that_disagrees_is_refused(self):
        """Without this the word was passed over: `mov byte ptr [rdi + 8], rax` was a store of eight bytes."""
        for line, word in SIZED:
            for other in WORDS:
                if other == word: continue
                with self.subTest(line=worded(line, other)):
                    with self.assertRaises(ValueError) as stopped: asm.instruction(worded(line, other))
                    self.assertIn(f"`{other} ptr` where x86.tab's `", str(stopped.exception))
                    self.assertTrue(str(stopped.exception).endswith(f"` moves a {word}"), str(stopped.exception))
        for line, word, _ in WORDED:
            for other in WORDS:
                if other == word: continue
                with self.subTest(line=worded(line, other)):
                    with self.assertRaises(ValueError): asm.instruction(worded(line, other))
        # lea moves nothing: any word may stand before its address; a prefetch takes `byte ptr` or no word
        for other in WORDS:
            with self.subTest(line=worded("lea rax, [rdi + 8]", other)):
                self.assertEqual(asm.instruction(worded("lea rax, [rdi + 8]", other)), asm.instruction("lea rax, [rdi + 8]"))
            with self.subTest(line=worded("prefetcht0 [rdi + 64]", other)):
                if other == "byte": self.assertEqual(asm.instruction(worded("prefetcht0 [rdi + 64]", other)), asm.instruction("prefetcht0 [rdi + 64]"))
                else:
                    with self.assertRaises(ValueError): asm.instruction(worded("prefetcht0 [rdi + 64]", other))

    def test_an_operand_of_another_class_is_refused(self):
        """Each of these was laid down before as another instruction that the table has."""
        for line, said in (("movzx rax, byte ptr [rdi + 8]", "`rax` where x86.tab's `movzx D32, byte ptr [B64 + N]` has a register of 32 bits"),
                           ("movzx rax, al", "`rax` where x86.tab's `movzx D32, S8` has a register of 32 bits"),
                           ("vprord ymm1, ymm2, 7", "`ymm1` where x86.tab's `vprord zmmX, zmmY, I` has a zmm register"),
                           ("vmovdqu32 [rdi + 0], xmm1", "`xmm1` where x86.tab's `vmovdqu32 [B64 + N], zmmX` has a zmm register"),
                           ("movups [rdi + 0], zmm1", "`zmm1` where x86.tab's `vmovdqu [B64 + N], xmmX` has an xmm register"),
                           ("vpbroadcastd xmm1, eax", "`xmm1` where x86.tab's `vpbroadcastd zmmX, S32` has a zmm register"),
                           ("pslld zmm1, 5", "`zmm1` where x86.tab's `vpslld xmmX, xmmY, I` has an xmm register"),
                           ("vpaddd xmm1, ymm2, zmm3", "`ymm2` where x86.tab's `vpaddd xmmX, xmmY, xmmZ` has an xmm register"),
                           ("mov rax, rcx, rdx", "3 operands where x86.tab's `mov D64, S64` has 2"),
                           ("vpaddd zmm1, zmm2, [rdi + 64]", "its memory has an index register"),
                           ("paddd xmm3, xmm3, xmm4", "3 operands where x86.tab's `vpaddd xmmX, xmmY, xmmZ` has 2"),
                           ("movaps xmm2, xmmword ptr [rdi + 8]", "x86.tab has the move of an xmm register from memory as movups, vmovups and vmovdqu"),
                           ("movaps xmmword ptr [rdi + 8], xmm2", "x86.tab has the move of an xmm register to memory as movups, vmovups and vmovdqu"),
                           ("movups xmm0, xmm5", "x86.tab has the move between xmm registers as movaps, movdqa, vmovaps and vmovdqa"),
                           ("lea rbx, [rdi + 8], rcx", "lea takes a register and an address"),
                           ("prefetcht0 byte ptr [rdi + 8], rcx", "a prefetch names one address"),
                           ("jmp .Lode_f_a, .Lode_f_b", "a jump names one label"), ("jmp rcx", "a jump names one label"),
                           ("call rax", "x86.tab has no call of a register"), ("call CALL(f), rcx", "cannot read call target")):
            with self.subTest(line=line):
                with self.assertRaises(ValueError) as stopped: asm.instruction(line)
                self.assertIn(said, str(stopped.exception))

    def test_a_refusal_names_the_line(self):
        for body, line, said in (
                ("  mov rax, rdi\n  mov byte ptr [rdi + 0], rax\n", 3, "`mov byte ptr [rdi + 0], rax`: `byte ptr` where x86.tab's `mov [B64 + N], S64` moves a qword"),
                ("  mov eax, qword ptr [rdi + 0]\n", 2, "`mov eax, qword ptr [rdi + 0]`: `qword ptr` where x86.tab's `mov D32, [B64 + N]` moves a dword"),
                ("  movzx rax, byte ptr [rdi + 0]\n", 2, "`movzx rax, byte ptr [rdi + 0]`: `rax` where x86.tab's `movzx D32, byte ptr [B64 + N]` has a register of 32 bits"),
                ("  nop\n  @a:\n  imul rax, rdi\n  jmp @a\n", 4, "`imul rax, rdi`: instruction not in x86.tab"),
                ("  mov qword ptr [rsp + 0], 5\n", 2, "`mov qword ptr [rsp + 0], 5`: x86.tab has a store of a number for one byte only"),
                ("  mov dword ptr [rdi + 0], eax\n", 2, "`mov dword ptr [rdi + 0], eax`: x86.tab has a store of an 8-bit register, of a 64-bit register, and of an 8-bit number: not of eax"),
                ("  mov al, byte ptr [rdi + 0]\n", 2, "`mov al, byte ptr [rdi + 0]`: x86.tab has `mov al, I` alone into al"),
                ("  mov byte ptr [rdi + 0], 256\n", 2, "`mov byte ptr [rdi + 0], 256`: immediate outside 8 bits: 256"),
                ("  mov rax, 0x100000000000\n", 2, "`mov rax, 0x100000000000`: no way in x86.tab writes mov64_ri"),
                ("  mov rax, rdi\n  call rax\n", 3, "`call rax`: x86.tab has no call of a register"),
                ("  mov rax, twelve\n", 2, "`mov rax, twelve`: not a number: twelve"),
                ("  push eax\n", 2, "`push eax`: instruction not in x86.tab"),
                ("  shl eax, 3\n", 2, "`shl eax, 3`: instruction not in x86.tab"),
                ("  mov rax, rcx, rdx\n", 2, "`mov rax, rcx, rdx`: 3 operands where x86.tab's `mov D64, S64` has 2"),
                ("  jmp @nowhere\n", 2, "`jmp @nowhere`: the function has no label `@nowhere`"),
                ("  for i in 0..3 {\n    nop\n    mov qword ptr [rsp + $i], 5\n  }\n", 4, "`mov qword ptr [rsp + 0], 5`: x86.tab has a store"),
                ("  reg p = rdi\n  mov byte ptr [p + 0], rax\n", 3, "`mov byte ptr [p + 0], rax`: `byte ptr` where x86.tab's `mov [B64 + N], S64` moves a qword"),
                ("  frame {\n    table: 4 * u64\n  }\n  sub rsp, frame.size\n  table[1] := 5\n", 6, "`table[1] := 5`: x86.tab has a store of a number for one byte only")):
            with self.subTest(body=body):
                got = self.said(body)
                self.assertIsNotNone(got, "it was built")
                self.assertTrue(got.startswith(f"s.ode: line {line}: {said}"), got)
                if "imul" in body: self.assertEqual(got, f"s.ode: line {line}: {said}")              # (the instruction is said once)

    def test_what_is_taken_is_built(self):
        self.assertIsNone(self.said(
            "  mov rax, qword ptr [rdi + 0]\n"
            "  mov byte ptr [rdi + 0], al\n"
            "  mov byte ptr [rdi + 1], dl\n"
            "  mov byte ptr [rdi + 2], sil\n"
            "  mov byte ptr [rdi + 3], r9b\n"
            "  mov byte ptr [rdi + 4], 7\n"
            "  lea r8, [rdi + rcx]\n"
            "  lea r9, [rdi + rcx + 8]\n"
            "  @here:\n  jmp @here\n"
        ))
        self.assertIsNotNone(self.said("  mov byte ptr [rdi + 0], ah\n"))


if __name__ == "__main__": unittest.main()
