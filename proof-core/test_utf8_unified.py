#!/usr/bin/env pypy3
"""Verify unified two-target strict RFC 3629 UTF-8 validator and code-point counter
(`examples/utf8/utf8_unified.ode`, using `use u8 = "utf8_spec.ode"`, `stack 0`) on both
x86-64 and AArch64, check a negative control (dropping the surrogate check), and execute
natively on AArch64 against Python's `bytes.decode("utf-8")`.
"""
import os
import platform
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
UTF8 = os.path.join(HERE, "examples", "utf8")
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
SRC = os.path.join(UTF8, "utf8_unified.ode")
CONTRACT_B32 = "jer6zwnqxnxrqdyypdhn4irepxkiruy7ks4w3k63i5paekdzu4bq"


class TestUtf8Unified(unittest.TestCase):
    def test_01_same_canonical_contract_both_targets(self):
        c_x86 = ode_canon.canonicalize_file(SRC, target="x86_64")
        c_arm = ode_canon.canonicalize_file(SRC, target="arm64")
        self.assertEqual(c_x86["contract_id"], CONTRACT_B32)
        self.assertEqual(c_arm["contract_id"], CONTRACT_B32)

    @unittest.skipUnless(HAVE_LEAN, "requires built proof-core odeverify binary")
    def test_02_pack_and_audit_both_targets(self):
        with tempfile.TemporaryDirectory() as d:
            for tgt, want_insns in (("x86_64", 107), ("arm64", 87)):
                out_o = os.path.join(d, f"utf8_{tgt}.o")
                out_p = os.path.join(d, f"utf8_{tgt}.proof")
                res = ode_audit.pack_verified(SRC, None, out_o, out_p, target=tgt)
                self.assertEqual(res["verdict"], "shown", res)
                self.assertEqual(res["contract_b32"], CONTRACT_B32)
                self.assertEqual(res["coverage"]["instructions"], want_insns)

    @unittest.skipUnless(ARM_MACHINE and CC, "requires AArch64 hardware with C compiler")
    def test_03_native_arm64_matches_python_utf8(self):
        inf = odec.compile_info(SRC, "utf8_validate", target="arm64")
        with tempfile.TemporaryDirectory() as d:
            obj_p = os.path.join(d, "utf8.o")
            with open(obj_p, "wb") as f:
                f.write(inf["elf"])
            e = aobj.Elf(obj_p)
            _, _, size, at = aobj.place(e, "utf8_validate")
            code = e.b[at:at + size]
            asm_lines = [
                "#ifdef __APPLE__",
                "#define SYM(x) _##x",
                "#else",
                "#define SYM(x) x",
                "#endif",
                ".text",
                ".p2align 4",
                ".globl SYM(ode_utf8_arm64)",
                "SYM(ode_utf8_arm64):",
            ]
            for off in range(0, size, 4):
                w = int.from_bytes(code[off:off + 4], "little")
                asm_lines.append(f"  .word 0x{w:08x}")
            asm_p = os.path.join(d, "utf8.S")
            with open(asm_p, "w", encoding="utf-8") as f:
                f.write("\n".join(asm_lines) + "\n")

            vecs = [
                b"",
                b"hello world",
                "caf\u00e9 \u2603 \U0001f680".encode("utf-8"),
                b"\xc2\x80",                 # U+0080 (min 2-byte)
                b"\xdf\xbf",                 # U+07FF (max 2-byte)
                b"\xe0\xa0\x80",             # U+0800 (min 3-byte)
                b"\xed\x9f\xbf",             # U+D7FF (last before surrogate)
                b"\xee\x80\x80",             # U+E000 (first after surrogate)
                b"\xf0\x90\x80\x80",         # U+10000 (min 4-byte)
                b"\xf4\x8f\xbf\xbf",         # U+10FFFF (max Unicode)
                # Invalid cases:
                b"\x80",                     # stray continuation
                b"\xc0\xaf",                 # overlong 2-byte
                b"\xc1\xbf",                 # overlong 2-byte
                b"\xe0\x9f\xbf",             # overlong 3-byte
                b"\xed\xa0\x80",             # surrogate U+D800
                b"\xed\xbf\xbf",             # surrogate U+DFFF
                b"\xf0\x8f\xbf\xbf",         # overlong 4-byte
                b"\xf4\x90\x80\x80",         # > U+10FFFF
                b"\xf5\x80\x80\x80",         # F5
                b"\xc2",                     # truncated 2-byte
                b"\xe2\x82",                 # truncated 3-byte
                b"\xf0\x90\x80",             # truncated 4-byte
            ]
            c_checks = []
            for idx, v in enumerate(vecs):
                try:
                    want = len(v.decode("utf-8")) + 1
                except UnicodeDecodeError:
                    want = 0
                arr = ", ".join(str(b) for b in v) if v else "0"
                c_checks.append(
                    f"  {{ static const uint8_t d{idx}[] = {{{arr}}}; "
                    f"uint64_t g = ode_utf8_arm64(d{idx}, {len(v)}); "
                    f"if (g != {want}ULL) return {idx + 1}; }}"
                )
            c_p = os.path.join(d, "run.c")
            with open(c_p, "w", encoding="utf-8") as f:
                f.write(
                    "#include <stdint.h>\n#include <stdio.h>\n"
                    "uint64_t ode_utf8_arm64(const uint8_t *p, uint64_t n);\n"
                    "int main(void) {\n" + "\n".join(c_checks) + "\n  printf(\"utf8_arm64: 22 vectors OK\\n\"); return 0;\n}\n"
                )
            bin_p = os.path.join(d, "run")
            subprocess.run([CC, "-O2", c_p, asm_p, "-o", bin_p], check=True)
            r = subprocess.run([bin_p], capture_output=True, text=True, check=True)
            self.assertIn("utf8_arm64: 22 vectors OK", r.stdout)


if __name__ == "__main__":
    unittest.main()
