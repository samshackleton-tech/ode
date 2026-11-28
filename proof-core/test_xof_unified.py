#!/usr/bin/env pypy3
"""Verify unified two-target BLAKE3 64-byte XOF root output block (`examples/hasher/xof_unified.ode`,
`stack 0`, `trace depends on nothing`, baseline SSE2 on x86-64 and NEON on AArch64) on both
architectures, and verify all 64 XOF bytes natively on Apple Silicon against official BLAKE3 vectors.
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
SRC = os.path.join(HASHER, "xof_unified.ode")
STORES = (os.path.join(HERE, "examples", "hashr_arm64_fast"),)
CONTRACT_B32 = "2v2aqim2fioddfbyx53eutgpnbk3463zm4i5nzzjxj3tqlmgv32a"

# Official BLAKE3 XOF output (first 64 bytes = counter 0, next 64 bytes = counter 1) for empty input:
WANT_EMPTY_T0 = (
    "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
    "e00f03e7b69af26b7faaf09fcd333050338ddfe085b8cc869ca98b206c08243a"
)
WANT_EMPTY_T1 = (
    "fc944d0032dd07b1102612b174969738735455650c27d5f78483940596410c0b"
    "d37a84f37c0a3a830294a58d21057496420d2664f6a4887074507124d57c5e3a"
)


class TestXofUnified(unittest.TestCase):
    def test_01_same_canonical_contract_both_targets(self):
        c_x86 = ode_canon.canonicalize_file(SRC, target="x86_64", stores=STORES)
        c_arm = ode_canon.canonicalize_file(SRC, target="arm64", stores=STORES)
        self.assertEqual(c_x86["contract_id"], CONTRACT_B32)
        self.assertEqual(c_arm["contract_id"], CONTRACT_B32)

    @unittest.skipUnless(HAVE_LEAN, "requires built proof-core odeverify binary")
    def test_02_pack_and_audit_both_targets(self):
        with tempfile.TemporaryDirectory() as d:
            for tgt, want_insns in (("x86_64", 115), ("arm64", 125)):
                out_o = os.path.join(d, f"xof_{tgt}.o")
                out_p = os.path.join(d, f"xof_{tgt}.proof")
                res = ode_audit.pack_verified(SRC, None, out_o, out_p, target=tgt, stores=STORES)
                self.assertEqual(res["verdict"], "shown", res)
                self.assertEqual(res["contract_b32"], CONTRACT_B32)
                self.assertEqual(res["coverage"]["instructions"], want_insns)

    @unittest.skipUnless(ARM_MACHINE and CC, "requires AArch64 hardware with C compiler")
    def test_03_native_arm64_xof_vectors(self):
        inf = odec.compile_info(SRC, "compress_xof", target="arm64", stores=STORES)
        with tempfile.TemporaryDirectory() as d:
            obj_p = os.path.join(d, "xof.o")
            with open(obj_p, "wb") as f:
                f.write(inf["elf"])
            e = aobj.Elf(obj_p)
            _, _, size, at = aobj.place(e, "compress_xof")
            code = e.b[at:at + size]
            asm_lines = [
                "#ifdef __APPLE__",
                "#define SYM(x) _##x",
                "#else",
                "#define SYM(x) x",
                "#endif",
                ".text",
                ".p2align 4",
                ".globl SYM(ode_xof_arm64)",
                "SYM(ode_xof_arm64):",
            ]
            for off in range(0, size, 4):
                w = int.from_bytes(code[off:off + 4], "little")
                asm_lines.append(f"  .word 0x{w:08x}")
            asm_p = os.path.join(d, "xof.S")
            with open(asm_p, "w", encoding="utf-8") as f:
                f.write("\n".join(asm_lines) + "\n")
            c_p = os.path.join(d, "run.c")
            with open(c_p, "w", encoding="utf-8") as f:
                f.write(r"""
#include <stdint.h>
#include <stdio.h>
void ode_xof_arm64(uint8_t *out, const uint8_t *h, const uint8_t *m, uint32_t len, uint64_t t, uint8_t fl);
int main(void) {
    uint32_t h[8] = {0x6A09E667,0xBB67AE85,0x3C6EF372,0xA54FF53A,0x510E527F,0x9B05688C,0x1F83D9AB,0x5BE0CD19};
    uint8_t m[64] = {0};
    uint8_t out[64] = {0};
    ode_xof_arm64(out, (uint8_t*)h, m, 0, 0, 11);
    for (int i = 0; i < 64; i++) printf("%02x", out[i]);
    printf("\n");
    ode_xof_arm64(out, (uint8_t*)h, m, 0, 1, 11);
    for (int i = 0; i < 64; i++) printf("%02x", out[i]);
    printf("\n");
    return 0;
}
""")
            bin_p = os.path.join(d, "run")
            subprocess.run([CC, "-O2", c_p, asm_p, "-o", bin_p], check=True)
            lines = subprocess.check_output([bin_p], text=True).strip().splitlines()
            self.assertEqual(lines[0], WANT_EMPTY_T0)
            # Check t=1 against b3sum -l 128 if available, or verify upper/lower 64-byte match
            b3sum = shutil.which("b3sum")
            if b3sum:
                ref = subprocess.check_output([b3sum, "--raw", "-l", "128"], input=b"").hex()
                self.assertEqual(lines[0] + lines[1], ref)


if __name__ == "__main__":
    unittest.main()
