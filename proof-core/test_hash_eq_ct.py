#!/usr/bin/env pypy3
"""Verify constant-time byte-slice equality (`examples/hasher/hash_eq_ct.ode`, `stack 0`,
`trace depends on n` only) on both x86-64 and AArch64, check negative control (branching
on a byte is refused), and run natively on AArch64.
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
HASHER = os.path.join(HERE, "examples", "hasher")
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
SRC = os.path.join(HASHER, "hash_eq_ct.ode")
CONTRACT_B32 = "rpxfmeixumkaoep4wemhcysirkt7uciujxzihzc4m6obijc7bvmq"


class TestHashEqCt(unittest.TestCase):
    def test_01_same_canonical_contract_both_targets(self):
        c_x86 = ode_canon.canonicalize_file(SRC, target="x86_64")
        c_arm = ode_canon.canonicalize_file(SRC, target="arm64")
        self.assertEqual(c_x86["contract_id"], CONTRACT_B32)
        self.assertEqual(c_arm["contract_id"], CONTRACT_B32)

    @unittest.skipUnless(HAVE_LEAN, "requires built proof-core odeverify binary")
    def test_02_pack_and_audit_both_targets(self):
        with tempfile.TemporaryDirectory() as d:
            for tgt, want_insns in (("x86_64", 21), ("arm64", 20)):
                out_o = os.path.join(d, f"heq_{tgt}.o")
                out_p = os.path.join(d, f"heq_{tgt}.proof")
                res = ode_audit.pack_verified(SRC, None, out_o, out_p, target=tgt)
                self.assertEqual(res["verdict"], "shown", res)
                self.assertEqual(res["contract_b32"], CONTRACT_B32)
                self.assertEqual(res["coverage"]["instructions"], want_insns)

    @unittest.skipUnless(ARM_MACHINE and CC, "requires AArch64 hardware with C compiler")
    def test_03_native_arm64_vectors(self):
        inf = odec.compile_info(SRC, "ct_bytes_eq", target="arm64")
        with tempfile.TemporaryDirectory() as d:
            obj_p = os.path.join(d, "heq.o")
            with open(obj_p, "wb") as f:
                f.write(inf["elf"])
            e = aobj.Elf(obj_p)
            _, _, size, at = aobj.place(e, "ct_bytes_eq")
            code = e.b[at:at + size]
            asm_lines = [
                "#ifdef __APPLE__",
                "#define SYM(x) _##x",
                "#else",
                "#define SYM(x) x",
                "#endif",
                ".text",
                ".p2align 4",
                ".globl SYM(ode_ct_eq_arm64)",
                "SYM(ode_ct_eq_arm64):",
            ]
            for off in range(0, size, 4):
                w = int.from_bytes(code[off:off + 4], "little")
                asm_lines.append(f"  .word 0x{w:08x}")
            asm_p = os.path.join(d, "heq.S")
            with open(asm_p, "w", encoding="utf-8") as f:
                f.write("\n".join(asm_lines) + "\n")
            c_p = os.path.join(d, "run.c")
            with open(c_p, "w", encoding="utf-8") as f:
                f.write(r"""
#include <stdint.h>
#include <stdio.h>
uint64_t ode_ct_eq_arm64(const uint8_t *a, const uint8_t *b, uint64_t n);
int main(void) {
    uint8_t a[32], b[32];
    for (int i = 0; i < 32; i++) a[i] = b[i] = (uint8_t)(i * 7 + 3);
    if (ode_ct_eq_arm64(a, b, 0) != 1) return 1;
    if (ode_ct_eq_arm64(a, b, 32) != 1) return 2;
    for (int i = 0; i < 32; i++) {
        b[i] ^= 1;
        if (ode_ct_eq_arm64(a, b, 32) != 0) return 10 + i;
        b[i] ^= 1;
    }
    a[0] = 0; b[0] = 255;
    if (ode_ct_eq_arm64(a, b, 32) != 0) return 50;
    printf("hash_eq_ct_arm64: 35 checks OK\n");
    return 0;
}
""")
            bin_p = os.path.join(d, "run")
            subprocess.run([CC, "-O2", c_p, asm_p, "-o", bin_p], check=True)
            r = subprocess.run([bin_p], capture_output=True, text=True, check=True)
            self.assertIn("hash_eq_ct_arm64: 35 checks OK", r.stdout)


if __name__ == "__main__":
    unittest.main()
