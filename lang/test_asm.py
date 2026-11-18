"""Compare the table assembler with the independent clang build of each Ode function."""
from pathlib import Path
import shutil, sys, tempfile, unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "kcheck"))
import kdecode, odec


@unittest.skipUnless(shutil.which("clang"), "clang is needed only for the comparison")
class Assembler(unittest.TestCase):
    def test_every_ode_function(self):
        with tempfile.TemporaryDirectory() as d:
            source, clang, own = (Path(d) / f for f in ("ref.S", "ref.o", "ode.o"))
            count = 0
            for path in sorted(ROOT.glob("**/*.ode")):
                _, functions = odec.functions(path.read_text(), str(path))
                for name, _, _ in functions:
                    count += 1
                    with self.subTest(source=path.relative_to(ROOT), function=name):
                        source.write_text(odec.assembly(str(path), name))
                        odec.assemble(str(source), str(clang))
                        odec.build(str(path), name, str(own))
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

    def test_what_the_table_lacks_is_refused(self):
        """The controls: an instruction with no row, an immediate too wide, an operand too many: no object."""
        text = (ROOT / "kcheck" / "programs" / "common" / "common.ode").read_text()
        old = "  mov r13, rax\n"
        self.assertGreaterEqual(text.count(old), 1)
        with tempfile.TemporaryDirectory() as d:
            src, obj = Path(d) / "changed.ode", Path(d) / "changed.o"
            for new in ("  imul r13, rax\n", "  mov r13d, 0x100000000\n", "  ret rax\n", "  mov r13, [rax + 0x80000000]\n"):
                with self.subTest(line=new.strip()):
                    src.write_text(text.replace(old, new, 1))
                    with self.assertRaises(SystemExit): odec.build(str(src), "common", str(obj))
                    self.assertFalse(obj.exists())
            src.write_text(text)
            odec.build(str(src), "common", str(obj))
            self.assertTrue(obj.exists())


if __name__ == "__main__": unittest.main()
