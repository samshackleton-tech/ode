#!/usr/bin/env python3
"""The shipped files' code is what the Ode sources give.

    python3 test_made.py

Every function of every shipped file (b3hashr.o, programs/NAME/odeNAME.o) is made again from its source
(../lang/odec.py expands its instructions, ../core/asm.py writes their bytes by the table) and compared, byte for byte, with the
function in the shipped file. Left out of the comparison: the four bytes a linker writes where a function is
called or the file's data is named (the makers of the shipped files, klink.py and programs/kpack.py, wrote
them; the verifier reads what they stand for from the shipped file itself).

The sources are hash.ode (nine functions), ../wide/*.ode (the five kernels) and programs/*/*.ode."""
import os, re, shutil, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, "..", "lang"))
import kdecode, kernels, klink, odec


def body(path, symbol):
    """(the function's bytes from its first to its `ret`, where in them a linker writes)"""
    e = kdecode.Elf(path)
    text, start, relocs, _ = kdecode.place(e, symbol)
    rows, _ = kdecode.read(path, symbol, 0, 0)
    size = rows[-1][1]
    fields = sorted(at - start for at in (e.relocations(".text") if isinstance(relocs, kdecode.Named) else {}) if start <= at < start + size)
    return bytes(text[start:start + size]), fields


def masked(code, fields):
    b = bytearray(code)
    for at in fields: b[at:at + 4] = bytes(4)
    return bytes(b)


class Made(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.dir = tempfile.mkdtemp(prefix="made-")

    @classmethod
    def tearDownClass(cls): shutil.rmtree(cls.dir)

    def same(self, shipped, symbol, obj):
        fresh, fields = body(obj, symbol)
        kept, none = body(shipped, symbol)
        self.assertEqual(none, [], f"{shipped} has relocations left")
        self.assertEqual(len(kept), len(fresh), f"{symbol}: {len(kept)} bytes shipped, {len(fresh)} from the source")
        self.assertEqual(masked(kept, fields), masked(fresh, fields), f"{symbol}: the shipped bytes are not the source's")
        return len(fresh)

    def test_the_hash(self):
        shipped = os.path.join(HERE, "b3hashr.o")
        odec_dir = os.path.join(self.dir, "hash"); os.makedirs(odec_dir)
        for name in klink.HASH: odec.build(os.path.join(HERE, "hash.ode"), name, os.path.join(odec_dir, name + ".o"))
        kernels.make(odec_dir)
        total = 0
        for obj, symbol in klink.BODIES + [(obj, symbol) for obj, symbol, _ in klink.ENTRIES]:
            total += self.same(shipped, symbol, os.path.join(odec_dir, obj))
        self.assertEqual(sorted(kdecode.linkable(kdecode.Elf(shipped))[1]), sorted(s for _, s in klink.BODIES + [(o, s) for o, s, _ in klink.ENTRIES]), "every name the file gives a linker has a source")
        self.assertGreater(total, 16000)

    def test_the_programs(self):
        programs = os.path.join(HERE, "programs")
        sources = {}        # a function's name -> its source
        for folder in sorted(os.listdir(programs)):
            if not os.path.isdir(os.path.join(programs, folder)): continue
            for f in sorted(os.listdir(os.path.join(programs, folder))):
                if f.endswith(".ode"):
                    for name, symbol, _ in odec.functions(odec.read_source(os.path.join(programs, folder, f)))[1]: sources[symbol] = (os.path.join(programs, folder, f), name)
        files = 0
        for folder in sorted(os.listdir(programs)):
            shipped = os.path.join(programs, folder, f"ode{folder}.o")
            if not os.path.exists(shipped): continue
            files += 1
            names = kdecode.linkable(kdecode.Elf(shipped))[1]
            self.assertTrue(names, shipped)
            for symbol in sorted(names):
                self.assertIn(symbol, sources, f"{shipped}: {symbol} has no source")
                src, name = sources[symbol]
                obj = os.path.join(self.dir, f"{folder}-{name}.o")
                odec.build(src, name, obj)
                self.same(shipped, symbol, obj)
        self.assertEqual(files, 8)

    def test_a_changed_source_is_told(self):
        """The control: one instruction of a source changed, and the comparison fails."""
        with open(os.path.join(HERE, "programs", "common", "common.ode")) as f: text = f.read()
        old = "  mov r13, rax\n"
        self.assertGreaterEqual(text.count(old), 1)
        src = os.path.join(self.dir, "changed.ode")
        with open(src, "w") as f: f.write(text.replace(old, "  mov r14, rax\n", 1))
        odec.build(src, "common", os.path.join(self.dir, "changed.o"))
        with self.assertRaises(AssertionError): self.same(os.path.join(HERE, "programs", "common", "odecommon.o"), "ode_common", os.path.join(self.dir, "changed.o"))


if __name__ == "__main__":
    unittest.main()
