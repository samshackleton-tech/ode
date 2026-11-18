#!/usr/bin/env python3
"""The decoder on the library's own wide kernels, from the library's assembly source.

    python3 test_kdecode.py

c/blake3_avx512_32.S is assembled (clang where there is one, else cc) and the object's bytes are read by
kdecode.py. Two things are asked: the decoder stops at encodings that no assembler writes; and, where there
is an llvm-objdump, its reading is a disassembler's (lift_one.py), instruction for instruction. (Until
November 18, 2026 this file was test_kcheck.py, and asked the same kernels of the first trial's machine,
kcheck.py, which ran a kernel to its end for a fixed number of blocks. test_kloop.py asks them of kfn.py.)

`assemble` is here for the other tests."""
import os, shutil, subprocess, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "reference", "blake3-servil"))
sys.path.insert(0, HERE)
import kdecode

BASE, DATA = 0x10000, 0x50000000
OBJDUMP = os.environ.get("OBJDUMP") or shutil.which("llvm-objdump") or shutil.which("objdump")
# the lifter reads llvm-objdump's listing (macOS's objdump is LLVM's; GNU's is another format)
LLVM_OBJDUMP = bool(OBJDUMP) and shutil.which(OBJDUMP) is not None and "LLVM" in subprocess.run([OBJDUMP, "--version"], capture_output=True, text=True).stdout


def assemble(s_path, o_path):
    for cc in (["clang", "--target=x86_64-unknown-linux-gnu"], ["cc", "-target", "x86_64-unknown-linux-gnu"]):
        if shutil.which(cc[0]) and subprocess.run(cc + ["-c", "-o", o_path, s_path], capture_output=True).returncode == 0: return
    subprocess.run(["cc", "-c", "-o", o_path, s_path], check=True)


class Kdecode(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.dir = tempfile.mkdtemp(prefix="kdecode-")
        cls.obj = os.path.join(cls.dir, "k.o")
        assemble(os.path.join(ROOT, "c", "blake3_avx512_32.S"), cls.obj)

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.dir)

    def test_the_decoder_stops_at_encodings_no_assembler_writes(self):
        with open(self.obj, "rb") as f: obj = f.read()
        e = kdecode.Elf(obj); sec = e.sections[e.index[".text"]]
        start = sec["off"] + kdecode.address(obj, "blake3_servil_avx512_p16")
        rows, _ = kdecode.read(obj, "blake3_servil_avx512_p16", BASE, DATA)
        def changed(ins, byte, bit):
            r = next(r for r in rows if r[2] == ins)
            b = bytearray(obj); b[start + r[0] - BASE + byte] ^= 1 << bit
            return bytes(b)
        for ins, byte, bit, what in ((".push .r15", 0, 3, "REX.W on a push"), (".push .r15", 0, 1, "REX.X on a push"),
                                     (".zprord 4 4 12", 1, 7, "EVEX.R beside an opcode digit"), (".zload true 19 .rsp 0x0", 6, 6, "a scale with no index"),
                                     (".sub 64 (.reg .rsp) (.imm 0x100)", 0, 3, "an empty REX prefix"), (".cmp 64 (.reg .r13) (.imm 0x1)", 0, 2, "REX.R beside an opcode digit")):
            with self.assertRaises(kdecode.Stop, msg=what):
                kdecode.read(changed(ins, byte, bit), "blake3_servil_avx512_p16", BASE, DATA)

    @unittest.skipUnless(LLVM_OBJDUMP, "no llvm-objdump: the lifter's reading is not made, and the two are not compared")
    def test_the_decoder_reads_what_the_lifter_reads(self):
        listing = os.path.join(self.dir, "k.listing")
        with open(listing, "w") as f:
            subprocess.run([OBJDUMP, "-d", "-r", "--x86-asm-syntax=intel", self.obj], stdout=f, check=True)
        lift = os.path.join(HERE, "lift_one.py")
        for symbol, base in (("blake3_servil_avx512_p16", "0x18000"), ("blake3_servil_avx512_p32", "0x1000C")):
            out = os.path.join(self.dir, symbol)
            subprocess.run([sys.executable, lift, listing, symbol, base, out + ".lean", "L", "--object", self.obj, "--rodata", "0x50000000"], check=True, capture_output=True, env=dict(os.environ, OBJDUMP=OBJDUMP))
            r = subprocess.run([sys.executable, os.path.join(HERE, "kdecode.py"), "--compare", self.obj, symbol, base, "0x50000000", out + ".lean.rows", out + ".lean.data"], capture_output=True, text=True)
            self.assertEqual(r.returncode, 0, r.stdout)
            self.assertIn("the same, every one", r.stdout)


if __name__ == "__main__":
    unittest.main()
