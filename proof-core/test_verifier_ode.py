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
import built, obj as aobj, ode_audit, ode_tool, odec

ARM_MACHINE = platform.machine() in ("arm64", "aarch64")
IS_LINUX_X86 = platform.system() == "Linux" and platform.machine() in ("x86_64", "amd64")
SPEC_PATH = os.path.join(VER, "arith.spec")
X86_PATH = os.path.join(VER, "arith_x86.ode")
ARM_PATH = os.path.join(VER, "arith_arm64.ode")
HL_PATH = os.path.join(VER, "verifier_hl.ode")
STD_DIR = os.path.join(ROOT, "std")


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

    def test_hl_verifier_stage2_dual_verify_and_native_x86(self):
        """All 8 Verifier-in-Ode Stage 2 kernels in `verifier_hl.ode` pass `--verifier both`
        (Lean `odeverify` + standalone pure-Python `verify2.py`) on BOTH x86-64 and AArch64,
        share identical contract IDs on all 7 portable kernels, and pass native C tests."""
        odeverify = os.path.join(HERE, ".lake", "build", "bin", "odeverify")
        if not os.path.isfile(odeverify):
            self.skipTest("odeverify binary not built")
        portable = [
            "v_all_zero", "v_row_contradicts", "v_bytes_eq",
            "v_plain_match", "v_step_ok", "v_parse_u64", "v_tag_kind",
        ]
        all_fns = portable + ["v_row_sum16"]
        cids = {}
        x86_objs = {}
        x86_syms = {}
        with tempfile.TemporaryDirectory() as d:
            for fn in all_fns:
                for target in ("x86_64", "arm64"):
                    out_o = os.path.join(d, f"{fn}_{target}.o")
                    out_p = os.path.join(d, f"{fn}_{target}.proof")
                    res = ode_audit.pack_verified(
                        HL_PATH, None, out_o, out_p,
                        fn_name=fn, target=target, c_abi=True,
                        stores=[STD_DIR], verifier="both",
                    )
                    self.assertEqual(res["verdict"], "shown", (fn, target, res))
                    self.assertEqual(list(res["verifiers"].keys()), ["odeverify", "verify2"])
                    cids[(fn, target)] = res["contract_b32"]
                    if target == "x86_64":
                        x86_objs[fn] = out_o
                        x86_syms[fn] = res["symbol"]
            for fn in portable:
                self.assertEqual(
                    cids[(fn, "x86_64")], cids[(fn, "arm64")],
                    f"cross-arch contract hash mismatch on {fn}",
                )
            cc = shutil.which("cc") or shutil.which("gcc") or shutil.which("clang")
            if IS_LINUX_X86 and cc:
                with open("/proc/cpuinfo", "r", encoding="utf-8") as ci:
                    has_avx512 = "avx512f" in ci.read()
                run_fns = all_fns if has_avx512 else portable
                avx_decl = (
                    "void " + x86_syms["v_row_sum16"] + "(uint32_t *, const uint32_t *, const uint32_t *);"
                    if has_avx512 else ""
                )
                avx_body = (
                    "_Alignas(64) uint32_t a[16], b[16], out[16];\n"
                    "    for (uint32_t k = 0; k < 16; k++) { a[k] = k * 100U; b[k] = 7U + k; }\n"
                    "    " + x86_syms["v_row_sum16"] + "(out, a, b);\n"
                    "    for (uint32_t k = 0; k < 16; k++) CHK(out[k] == a[k] + b[k]);"
                    if has_avx512 else ""
                )
                c_src = f"""
#include <stdint.h>
#include <stdio.h>
#include <string.h>
uint64_t {x86_syms["v_all_zero"]}(const uint8_t *, uint64_t);
uint64_t {x86_syms["v_row_contradicts"]}(const uint8_t *, uint64_t, uint64_t, uint64_t);
uint64_t {x86_syms["v_bytes_eq"]}(const uint8_t *, const uint8_t *, uint64_t);
uint64_t {x86_syms["v_plain_match"]}(const uint8_t *, const uint8_t *, uint64_t, uint64_t, uint64_t);
uint64_t {x86_syms["v_step_ok"]}(uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
uint64_t {x86_syms["v_parse_u64"]}(const uint8_t *, uint64_t);
uint64_t {x86_syms["v_tag_kind"]}(const uint8_t *, uint64_t);
{avx_decl}
#define CHK(cond) do {{ if (!(cond)) {{ fprintf(stderr, "FAIL line %d\\n", __LINE__); return 1; }} }} while (0)
int main(void) {{
    uint8_t z[4] = {{0, 0, 0, 0}}, nz[4] = {{0, 0, 1, 0}};
    CHK({x86_syms["v_all_zero"]}(z, 0) == 1);
    CHK({x86_syms["v_all_zero"]}(z, 4) == 1);
    CHK({x86_syms["v_all_zero"]}(nz, 4) == 0);
    CHK({x86_syms["v_row_contradicts"]}(z, 4, 3, 5) == 1);
    CHK({x86_syms["v_row_contradicts"]}(z, 4, 5, 5) == 0);
    CHK({x86_syms["v_row_contradicts"]}(nz, 4, 3, 5) == 0);
    CHK({x86_syms["v_bytes_eq"]}((const uint8_t *)"place", (const uint8_t *)"place", 5) == 1);
    CHK({x86_syms["v_bytes_eq"]}((const uint8_t *)"place", (const uint8_t *)"placx", 5) == 0);
    CHK({x86_syms["v_plain_match"]}(z, z, 4, 10, 12) == 1);
    CHK({x86_syms["v_plain_match"]}(z, z, 4, 13, 12) == 0);
    CHK({x86_syms["v_plain_match"]}(z, nz, 4, 10, 12) == 0);
    CHK({x86_syms["v_step_ok"]}(0, 1, 2, 3, 1, 5) == 1);
    CHK({x86_syms["v_step_ok"]}(5, 1, 2, 3, 1, 5) == 0);
    CHK({x86_syms["v_step_ok"]}(0, 0, 2, 3, 1, 5) == 0);
    CHK({x86_syms["v_step_ok"]}(0, 1, 2, 3, 0, 5) == 0);
    const uint64_t ERR = 1152921504606846976ULL;
    CHK({x86_syms["v_parse_u64"]}((const uint8_t *)"", 0) == ERR);
    CHK({x86_syms["v_parse_u64"]}((const uint8_t *)"0", 1) == 0);
    CHK({x86_syms["v_parse_u64"]}((const uint8_t *)"12345678901234567", 17) == 12345678901234567ULL);
    CHK({x86_syms["v_parse_u64"]}((const uint8_t *)"720575940379279360", 18) == ERR);
    CHK({x86_syms["v_parse_u64"]}((const uint8_t *)"12a3", 4) == ERR);
    CHK({x86_syms["v_tag_kind"]}((const uint8_t *)"r", 1) == 1);
    CHK({x86_syms["v_tag_kind"]}((const uint8_t *)"s", 1) == 2);
    CHK({x86_syms["v_tag_kind"]}((const uint8_t *)"q", 1) == 3);
    CHK({x86_syms["v_tag_kind"]}((const uint8_t *)"t", 1) == 4);
    CHK({x86_syms["v_tag_kind"]}((const uint8_t *)"k", 1) == 5);
    CHK({x86_syms["v_tag_kind"]}((const uint8_t *)"for", 3) == 6);
    CHK({x86_syms["v_tag_kind"]}((const uint8_t *)"place", 5) == 7);
    CHK({x86_syms["v_tag_kind"]}((const uint8_t *)"bad", 3) == 0);
    {avx_body}
    puts("verifier_hl_x86: OK");
    return 0;
}}
"""
                c_p = os.path.join(d, "run_hl.c")
                exe_p = os.path.join(d, "run_hl")
                with open(c_p, "w", encoding="utf-8") as f:
                    f.write(c_src)
                subprocess.run(
                    [cc, "-O1", "-o", exe_p, c_p] + [x86_objs[fn] for fn in run_fns],
                    check=True, capture_output=True, text=True,
                )
                r = subprocess.run([exe_p], check=True, capture_output=True, text=True)
                self.assertEqual(r.stdout.strip(), "verifier_hl_x86: OK")


if __name__ == "__main__":
    unittest.main()
