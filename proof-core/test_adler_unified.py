#!/usr/bin/env pypy3
"""Verify unified two-target RFC 1950 Adler-32 (`examples/adler32/adler32_unified.ode`,
using `use a32 = "adler32_spec.ode"`, `stack 0`) on both x86-64 and AArch64, and run
against Python's `zlib.adler32` on native AArch64 hardware.
"""
import os
import platform
import shutil
import subprocess
import sys
import tempfile
import unittest
import zlib

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
ADLER = os.path.join(HERE, "examples", "adler32")
sys.path[:0] = [
    HERE,
    os.path.join(ROOT, "lang"),
    os.path.join(ROOT, "arm64"),
    os.path.join(ROOT, "core"),
    os.path.join(ROOT, "kcheck"),
]

import obj as aobj
import ode_audit
import ode_canon
import odec

HAVE_LEAN = os.path.isfile(os.path.join(HERE, ".lake", "build", "bin", "odeverify"))
ARM_MACHINE = platform.machine() in ("arm64", "aarch64")
CC = shutil.which("clang") or shutil.which("cc")
SRC = os.path.join(ADLER, "adler32_unified.ode")
CONTRACT_B32 = "b5iqymd2phvrbvo5m7phsovky36ggo7mhezt2husy3qmuyge5qua"


class TestAdlerUnified(unittest.TestCase):
    def test_01_same_canonical_contract_both_targets(self):
        c_x86 = ode_canon.canonicalize_file(SRC, target="x86_64")
        c_arm = ode_canon.canonicalize_file(SRC, target="arm64")
        self.assertEqual(c_x86["contract_id"], CONTRACT_B32)
        self.assertEqual(c_arm["contract_id"], CONTRACT_B32)

    @unittest.skipUnless(HAVE_LEAN, "requires built proof-core odeverify binary")
    def test_02_pack_and_audit_both_targets(self):
        with tempfile.TemporaryDirectory() as d:
            for tgt, want_insns in (("x86_64", 22), ("arm64", 21)):
                out_o = os.path.join(d, f"adler_{tgt}.o")
                out_p = os.path.join(d, f"adler_{tgt}.proof")
                res = ode_audit.pack_verified(SRC, None, out_o, out_p, target=tgt)
                self.assertEqual(res["verdict"], "shown", res)
                self.assertEqual(res["contract_b32"], CONTRACT_B32)
                self.assertEqual(res["coverage"]["instructions"], want_insns)

    @unittest.skipUnless(ARM_MACHINE and CC, "requires AArch64 hardware with C compiler")
    def test_03_native_arm64_matches_zlib(self):
        inf = odec.compile_info(SRC, "adler32", target="arm64")
        with tempfile.TemporaryDirectory() as d:
            obj_p = os.path.join(d, "adler.o")
            with open(obj_p, "wb") as f:
                f.write(inf["elf"])
            e = aobj.Elf(obj_p)
            _, _, size, at = aobj.place(e, "adler32")
            code = e.b[at:at + size]
            asm_lines = [
                "#ifdef __APPLE__",
                "#define SYM(x) _##x",
                "#else",
                "#define SYM(x) x",
                "#endif",
                ".text",
                ".p2align 4",
                ".globl SYM(ode_adler32_arm64)",
                "SYM(ode_adler32_arm64):",
            ]
            for off in range(0, size, 4):
                w = int.from_bytes(code[off:off + 4], "little")
                asm_lines.append(f"  .word 0x{w:08x}")
            asm_p = os.path.join(d, "adler.S")
            with open(asm_p, "w", encoding="utf-8") as f:
                f.write("\n".join(asm_lines) + "\n")
            vecs = [b"", b"a", b"Wikipedia", bytes(range(256)), b"\xff" * 6000]
            c_checks = []
            for idx, v in enumerate(vecs):
                want = zlib.adler32(v) & 0xFFFFFFFF
                arr = ", ".join(str(b) for b in v) if v else "0"
                c_checks.append(
                    f"  {{ static const uint8_t d{idx}[] = {{{arr}}}; "
                    f"uint64_t g = ode_adler32_arm64(d{idx}, {len(v)}); "
                    f"if (g != {want}ULL) return {idx + 1}; }}"
                )
            c_p = os.path.join(d, "run.c")
            with open(c_p, "w", encoding="utf-8") as f:
                f.write(
                    "#include <stdint.h>\n#include <stdio.h>\n"
                    "uint64_t ode_adler32_arm64(const uint8_t *p, uint64_t n);\n"
                    "int main(void) {\n" + "\n".join(c_checks) + "\n  printf(\"adler32_arm64: OK\\n\"); return 0;\n}\n"
                )
            bin_p = os.path.join(d, "run")
            subprocess.run([CC, "-O2", c_p, asm_p, "-o", bin_p], check=True)
            r = subprocess.run([bin_p], capture_output=True, text=True, check=True)
            self.assertIn("adler32_arm64: OK", r.stdout)


if __name__ == "__main__":
    unittest.main()
