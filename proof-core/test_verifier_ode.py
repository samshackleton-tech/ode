#!/usr/bin/env pypy3
"""Verify the cross-platform Verifier-in-Ode building blocks (`examples/verifier/arith_x86.ode`,
`arith_arm64.ode`, and `arith.spec`) on both x86-64 and AArch64 under the Lean 4 soundness
theorem, check false-code and false-contract controls, and execute the verified AArch64
functions on hardware where available.

    pypy3 test_verifier_ode.py        (Lean tests skipped without `lake`; hardware run on AArch64)
"""
import os, platform, shutil, subprocess, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
VER = os.path.join(HERE, "examples", "verifier")
sys.path[:0] = [HERE, os.path.join(ROOT, "lang"), os.path.join(ROOT, "arm64"),
                os.path.join(ROOT, "core")]
import built, obj as aobj, ode_tool, odec

ARM_MACHINE = platform.machine() in ("arm64", "aarch64")
SPEC_PATH = os.path.join(VER, "arith.spec")
X86_PATH = os.path.join(VER, "arith_x86.ode")
ARM_PATH = os.path.join(VER, "arith_arm64.ode")


def once(old, new):
    def edit(text):
        assert text.count(old) == 1, f"expected 1 occurrence of {old!r}, got {text.count(old)}"
        return text.replace(old, new, 1)
    return edit


NATIVE_C = r"""
#include <stdint.h>
#include <stdio.h>
#include <string.h>

uint64_t v_row_contradicts_arm64(const uint8_t *coeffs, uint64_t n, uint64_t pos, uint64_t neg);
void v_row_sum16_arm64(uint32_t *out, const uint32_t *a, const uint32_t *b);
uint64_t v_bytes_eq_arm64(const uint8_t *a, const uint8_t *b, uint64_t n);

int main(void) {
    uint8_t z[16] = {0};
    uint8_t nz[16] = {0}; nz[9] = 1;
    // 1. row_contradicts: all zero + pos < neg -> 1; non-zero or pos >= neg -> 0
    if (v_row_contradicts_arm64(z, 16, 3, 5) != 1) return 1;
    if (v_row_contradicts_arm64(z, 0, 0, 1) != 1) return 2;
    if (v_row_contradicts_arm64(z, 16, 5, 5) != 0) return 3;
    if (v_row_contradicts_arm64(z, 16, 9, 5) != 0) return 4;
    if (v_row_contradicts_arm64(nz, 16, 3, 5) != 0) return 5;
    if (v_row_contradicts_arm64(nz, 9, 3, 5) != 1) return 6;

    // 2. row_sum16: 16-lane 32-bit wrapping addition
    uint32_t a[16], b[16], out[16];
    for (uint32_t i = 0; i < 16; i++) {
        a[i] = 0xFFFFFFF8u + i;
        b[i] = 10u + 3u * i;
    }
    v_row_sum16_arm64(out, a, b);
    for (uint32_t i = 0; i < 16; i++) {
        if (out[i] != (uint32_t)(a[i] + b[i])) return 7;
    }

    // 3. bytes_eq: exact byte-slice equality
    uint8_t p[16], q[16];
    for (int i = 0; i < 16; i++) p[i] = q[i] = (uint8_t)(i * 17 + 3);
    if (v_bytes_eq_arm64(p, q, 0) != 1) return 8;
    if (v_bytes_eq_arm64(p, q, 16) != 1) return 9;
    q[15] ^= 1;
    if (v_bytes_eq_arm64(p, q, 16) != 0) return 10;
    if (v_bytes_eq_arm64(p, q, 15) != 1) return 11;

    printf("verifier_ode_arm64: 11 checks OK\n");
    return 0;
}
"""


@unittest.skipUnless(shutil.which("lake"), "Lean's `lake` is not installed here")
class VerifierInOde(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        built.built("odeprove")

    def test_all_6_cross_platform_verifier_functions_shown(self):
        cases = [
            (X86_PATH, "row_contradicts", "v_row_contradicts_x86"),
            (X86_PATH, "row_sum16",       "v_row_sum16_x86"),
            (X86_PATH, "bytes_eq",        "v_bytes_eq_x86"),
            (ARM_PATH, "row_contradicts", "v_row_contradicts_arm64"),
            (ARM_PATH, "row_sum16",       "v_row_sum16_arm64"),
            (ARM_PATH, "bytes_eq",        "v_bytes_eq_arm64"),
        ]
        for src, fn, sym in cases:
            with self.subTest(sym=sym):
                resp = ode_tool.handle_request({"cmd": "check", "source": src, "spec": SPEC_PATH, "fn": [fn]})
                self.assertTrue(resp["ok"], f"{sym} failed: {resp}")
                self.assertEqual(resp["result"]["verdict"], "shown")

    def test_mutated_verifier_code_is_refused(self):
        mutations = [
            (X86_PATH, "row_contradicts", "flip ult -> uge",
             once("  cmp pos, neg\n  if ult {", "  cmp pos, neg\n  if uge {")),
            (ARM_PATH, "row_contradicts", "flip ult -> uge",
             once("  cmp pos, neg\n  if ult {", "  cmp pos, neg\n  if uge {")),
            (X86_PATH, "row_sum16", "vpaddd -> vpxord",
             once("  vpaddd zmm0, zmm0, zmm1", "  vpxord zmm0, zmm0, zmm1")),
            (ARM_PATH, "row_sum16", "add -> eor",
             once("  add va.4s, va.4s, vb.4s", "  eor va.16b, va.16b, vb.16b")),
            (X86_PATH, "bytes_eq", "return 1 on mismatch",
             once("    cmp r8, r9\n    if ne {\n      res := 0\n",
                  "    cmp r8, r9\n    if ne {\n      res := 1\n")),
            (ARM_PATH, "bytes_eq", "return 1 on mismatch",
             once("    cmp x6, x8\n    if ne {\n      res := 0\n",
                  "    cmp x6, x8\n    if ne {\n      res := 1\n")),
        ]
        for src, fn, what, mutate in mutations:
            with self.subTest(src=os.path.basename(src), fn=fn, what=what):
                with tempfile.TemporaryDirectory() as d:
                    p = os.path.join(d, "mut.ode")
                    with open(src) as f:
                        text = mutate(f.read())
                    with open(p, "w") as f:
                        f.write(text)
                    resp = ode_tool.handle_request({"cmd": "check", "source": p, "spec": SPEC_PATH, "fn": [fn]})
                    self.assertFalse(resp["ok"], f"mutated verifier code accepted ({what}): {resp}")

    @unittest.skipUnless(ARM_MACHINE and shutil.which("clang"),
                         "an AArch64 processor and clang are needed")
    def test_arm64_verifier_functions_run_on_hardware(self):
        with tempfile.TemporaryDirectory() as d:
            asm_lines = [
                "#ifdef __APPLE__",
                "#define SYM(x) _##x",
                "#else",
                "#define SYM(x) x",
                "#endif",
                ".text",
            ]
            for fn, sym in (
                ("row_contradicts", "v_row_contradicts_arm64"),
                ("row_sum16",       "v_row_sum16_arm64"),
                ("bytes_eq",        "v_bytes_eq_arm64"),
            ):
                obj_p = os.path.join(d, sym + ".o")
                odec.build(ARM_PATH, fn, obj_p)
                words, _ = aobj.words(obj_p, sym)
                asm_lines += [".p2align 2", f".globl SYM({sym})", f"SYM({sym}):"]
                for w in words:
                    asm_lines.append(f"  .word 0x{int.from_bytes(w, 'little'):08x}")
            asm_p = os.path.join(d, "ver.S")
            c_p = os.path.join(d, "run.c")
            exe_p = os.path.join(d, "run")
            with open(asm_p, "w") as f:
                f.write("\n".join(asm_lines) + "\n")
            with open(c_p, "w") as f:
                f.write(NATIVE_C)
            subprocess.run(["clang", "-O1", "-o", exe_p, c_p, asm_p],
                           check=True, capture_output=True)
            r = subprocess.run([exe_p], check=True, capture_output=True, text=True)
            self.assertEqual(r.stdout.strip(), "verifier_ode_arm64: 11 checks OK")


if __name__ == "__main__":
    unittest.main()
