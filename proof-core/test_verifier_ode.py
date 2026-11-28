#!/usr/bin/env pypy3
"""Verify the cross-platform Verifier-in-Ode building blocks (`examples/verifier/arith_x86.ode`,
`arith_arm64.ode`, and `arith.spec`) on both x86-64 and AArch64 under the Lean 4 soundness
theorem, check false-code and false-contract controls, and execute the verified AArch64
functions on hardware where available.

    pypy3 test_verifier_ode.py        (Lean tests skipped without `lake`; hardware run on AArch64)
"""
import os, platform, re, shutil, struct, subprocess, sys, tempfile, unittest

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
STAGE3_PATH = os.path.join(VER, "verifier_stage3.ode")
STD_DIR = os.path.join(ROOT, "std")
IS_MAC_ARM64 = platform.system() == "Darwin" and ARM_MACHINE


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

    def test_hl_verifier_stage3_dual_verify_and_native(self):
        """All 8 Verifier-in-Ode Stage 3 kernels (`verifier_stage3.ode`) pass `--verifier both`
        across x86-64 and AArch64, share identical contract IDs on all 6 portable kernels,
        and tokenize/parse a real `.proof` line + SIMD row ops natively on x86-64 and Apple M6."""
        odeverify = os.path.join(HERE, ".lake", "build", "bin", "odeverify")
        if not os.path.isfile(odeverify):
            self.skipTest("odeverify binary not built")
        portable = [
            "v_skip_spaces", "v_line_end", "v_token_end",
            "v_next_token_span", "v_parse_i64", "v_hex_byte",
        ]
        all_fns = portable + ["v_row_xor16", "v_row_2a_plus_b16"]
        cids, objs, syms = {}, {}, {}
        with tempfile.TemporaryDirectory() as d:
            for fn in all_fns:
                for tgt in ("x86_64", "arm64"):
                    out_o = os.path.join(d, f"{fn}_{tgt}.o")
                    out_p = os.path.join(d, f"{fn}_{tgt}.proof")
                    res = ode_audit.pack_verified(
                        STAGE3_PATH, None, out_o, out_p,
                        fn_name=fn, target=tgt, c_abi=True,
                        stores=[STD_DIR], verifier="both",
                    )
                    self.assertEqual(res["verdict"], "shown", (fn, tgt, res))
                    self.assertEqual(list(res["verifiers"].keys()), ["odeverify", "verify2"])
                    cids[(fn, tgt)] = res["contract_b32"]
                    objs[(fn, tgt)] = out_o
                    syms[(fn, tgt)] = res["symbol"]
            for fn in portable:
                self.assertEqual(
                    cids[(fn, "x86_64")], cids[(fn, "arm64")],
                    f"cross-arch contract hash mismatch on {fn}",
                )

            def stage3_c_body(p, run_simd):
                simd_block = (
                    f"_Alignas(64) uint32_t a[16], b[16], xo[16], co[16];\n"
                    f"    for (uint32_t k = 0; k < 16; k++) {{ a[k] = 10U + k; b[k] = 3U * k + 1U; }}\n"
                    f"    {p}v_row_xor16(xo, a, b);\n"
                    f"    {p}v_row_2a_plus_b16(co, a, b);\n"
                    f"    for (uint32_t k = 0; k < 16; k++) {{\n"
                    f"        CHK(xo[k] == (a[k] ^ b[k]));\n"
                    f"        CHK(co[k] == (a[k] + a[k] + b[k]));\n"
                    f"    }}\n"
                    if run_simd else ""
                )
                return f"""
    const char *line = "  r\\t1 0 -16 42\\n";
    uint64_t n = strlen(line);
    CHK({p}v_line_end((const uint8_t *)line, n, 0) == n - 1);
    uint64_t sp0 = {p}v_next_token_span((const uint8_t *)line, n, 0);
    CHK((sp0 & 0xFFFFFFFFULL) == 2 && (sp0 >> 32) == 3); /* "r" */
    uint64_t sp1 = {p}v_next_token_span((const uint8_t *)line, n, sp0 >> 32);
    CHK((sp1 & 0xFFFFFFFFULL) == 4 && (sp1 >> 32) == 5); /* "1" */
    uint64_t sp2 = {p}v_next_token_span((const uint8_t *)line, n, sp1 >> 32);
    CHK((sp2 & 0xFFFFFFFFULL) == 6 && (sp2 >> 32) == 7); /* "0" */
    uint64_t sp3 = {p}v_next_token_span((const uint8_t *)line, n, sp2 >> 32);
    uint64_t s3 = sp3 & 0xFFFFFFFFULL, e3 = sp3 >> 32;
    CHK(s3 == 8 && e3 == 11); /* "-16" */
    const uint64_t SBIT = 1ULL << 60, ERR = 1ULL << 61;
    CHK({p}v_parse_i64((const uint8_t *)(line + s3), e3 - s3) == (SBIT | 16ULL));
    uint64_t sp4 = {p}v_next_token_span((const uint8_t *)line, n, e3);
    uint64_t s4 = sp4 & 0xFFFFFFFFULL, e4 = sp4 >> 32;
    CHK(s4 == 12 && e4 == 14); /* "42" */
    CHK({p}v_parse_i64((const uint8_t *)(line + s4), e4 - s4) == 42ULL);
    CHK({p}v_parse_i64((const uint8_t *)"-", 1) == ERR);
    CHK({p}v_parse_i64((const uint8_t *)"", 0) == ERR);
    CHK({p}v_hex_byte('f', '9') == 0xF9);
    CHK({p}v_hex_byte('A', '0') == 0xA0);
    CHK({p}v_hex_byte('g', '0') == 256);
    {simd_block}
"""

            cc = shutil.which("cc") or shutil.which("gcc") or shutil.which("clang")
            if IS_LINUX_X86 and cc:
                with open("/proc/cpuinfo", "r", encoding="utf-8") as ci:
                    has_avx512 = "avx512f" in ci.read()
                run_fns = all_fns if has_avx512 else portable
                decls = "\n".join([
                    f'uint64_t {syms[("v_skip_spaces", "x86_64")]}(const uint8_t *, uint64_t, uint64_t);',
                    f'uint64_t {syms[("v_line_end", "x86_64")]}(const uint8_t *, uint64_t, uint64_t);',
                    f'uint64_t {syms[("v_token_end", "x86_64")]}(const uint8_t *, uint64_t, uint64_t);',
                    f'uint64_t {syms[("v_next_token_span", "x86_64")]}(const uint8_t *, uint64_t, uint64_t);',
                    f'uint64_t {syms[("v_parse_i64", "x86_64")]}(const uint8_t *, uint64_t);',
                    f'uint64_t {syms[("v_hex_byte", "x86_64")]}(uint64_t, uint64_t);',
                ] + ([
                    f'void {syms[("v_row_xor16", "x86_64")]}(uint32_t *, const uint32_t *, const uint32_t *);',
                    f'void {syms[("v_row_2a_plus_b16", "x86_64")]}(uint32_t *, const uint32_t *, const uint32_t *);',
                ] if has_avx512 else []))
                aliases = "\n".join(f'#define fn_{fn} {syms[(fn, "x86_64")]}' for fn in run_fns)
                c_src = f"""
#include <stdint.h>
#include <stdio.h>
#include <string.h>
{decls}
{aliases}
#define CHK(cond) do {{ if (!(cond)) {{ fprintf(stderr, "FAIL line %d\\n", __LINE__); return 1; }} }} while (0)
int main(void) {{
{stage3_c_body("fn_", has_avx512)}
    puts("verifier_stage3_x86: OK");
    return 0;
}}
"""
                c_p = os.path.join(d, "run_s3.c")
                exe_p = os.path.join(d, "run_s3")
                with open(c_p, "w", encoding="utf-8") as f:
                    f.write(c_src)
                subprocess.run(
                    [cc, "-O1", "-o", exe_p, c_p] + [objs[(fn, "x86_64")] for fn in run_fns],
                    check=True, capture_output=True, text=True,
                )
                r = subprocess.run([exe_p], check=True, capture_output=True, text=True)
                self.assertEqual(r.stdout.strip(), "verifier_stage3_x86: OK")

            elif IS_MAC_ARM64 and shutil.which("clang"):
                def reloc_text(elf_path, sym_name):
                    with open(elf_path, "rb") as f:
                        b = f.read()
                    e_shoff = struct.unpack_from("<Q", b, 40)[0]
                    e_shentsize, e_shnum, e_shstrndx = struct.unpack_from("<HHH", b, 58)
                    secs = [struct.unpack_from("<IIQQQQI", b, e_shoff + i * e_shentsize) for i in range(e_shnum)]
                    shstr_off = secs[e_shstrndx][4]
                    sname = lambda idx: b[shstr_off + idx:b.index(0, shstr_off + idx)].decode("ascii", "replace")
                    tb, eoff, sv = b"", 0, {}
                    for sn, st, _, _, so, sz, sl in secs:
                        if sname(sn) == ".text":
                            tb = b[so:so + sz]
                        elif st == 2:
                            stro = secs[sl][4]
                            for idx, pos in enumerate(range(so, so + sz, 24)):
                                nm, _, _, _, val, _ = struct.unpack_from("<IBBHQQ", b, pos)
                                sv[idx] = val
                                if b[stro + nm:b.index(0, stro + nm)].decode("ascii", "replace") == sym_name:
                                    eoff = val
                    buf = bytearray(tb)
                    for sn, st, _, _, so, sz, _ in secs:
                        if st == 4 and sname(sn) == ".rela.text":
                            for pos in range(so, so + sz, 24):
                                ro, ri, ra = struct.unpack_from("<QQq", b, pos)
                                if (ri & 0xFFFFFFFF) in (282, 283):
                                    imm26 = (((sv[ri >> 32] + ra) - ro) >> 2) & 0x03FFFFFF
                                    ins = struct.unpack_from("<I", buf, ro)[0]
                                    struct.pack_into("<I", buf, ro, (ins & 0xFC000000) | imm26)
                    return bytes(buf), eoff

                types = {
                    "v_skip_spaces": "uint64_t (*)(const uint8_t *, uint64_t, uint64_t)",
                    "v_line_end": "uint64_t (*)(const uint8_t *, uint64_t, uint64_t)",
                    "v_token_end": "uint64_t (*)(const uint8_t *, uint64_t, uint64_t)",
                    "v_next_token_span": "uint64_t (*)(const uint8_t *, uint64_t, uint64_t)",
                    "v_parse_i64": "uint64_t (*)(const uint8_t *, uint64_t)",
                    "v_hex_byte": "uint64_t (*)(uint64_t, uint64_t)",
                    "v_row_xor16": "void (*)(uint32_t *, const uint32_t *, const uint32_t *)",
                    "v_row_2a_plus_b16": "void (*)(uint32_t *, const uint32_t *, const uint32_t *)",
                }
                load_lines = []
                for fn in all_fns:
                    code, entry = reloc_text(objs[(fn, "arm64")], syms[(fn, "arm64")])
                    bp = os.path.join(d, f"{fn}.bin")
                    with open(bp, "wb") as bf:
                        bf.write(code)
                    ty = types[fn]
                    load_lines.append(
                        f'    {ty.replace("(*)", "(*fn_" + fn + ")")} = ({ty})load_jit("{bp}", {len(code)}, {entry});'
                    )
                loads = "\n".join(load_lines)
                c_src = f"""
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <pthread.h>
#include <libkern/OSCacheControl.h>
static void *load_jit(const char *path, size_t n, size_t entry_off) {{
    uint8_t *tmp = (uint8_t *)malloc(n);
    FILE *fp = fopen(path, "rb");
    if (!tmp || !fp || fread(tmp, 1, n, fp) != n) {{ fprintf(stderr, "read %s\\n", path); exit(2); }}
    fclose(fp);
    void *p = mmap(NULL, (n + 4095) & ~4095ULL, PROT_READ|PROT_WRITE|PROT_EXEC, MAP_PRIVATE|MAP_ANON|MAP_JIT, -1, 0);
    if (p == MAP_FAILED) {{ perror("mmap"); exit(2); }}
    pthread_jit_write_protect_np(0);
    memcpy(p, tmp, n);
    pthread_jit_write_protect_np(1);
    sys_icache_invalidate(p, n);
    free(tmp);
    return (uint8_t *)p + entry_off;
}}
#define CHK(cond) do {{ if (!(cond)) {{ fprintf(stderr, "FAIL line %d\\n", __LINE__); return 1; }} }} while (0)
int main(void) {{
{loads}
{stage3_c_body("fn_", True)}
    puts("verifier_stage3_arm64: OK");
    return 0;
}}
"""
                c_p = os.path.join(d, "run_s3_arm64.c")
                exe_p = os.path.join(d, "run_s3_arm64")
                with open(c_p, "w", encoding="utf-8") as f:
                    f.write(c_src)
                subprocess.run(["clang", "-O1", "-o", exe_p, c_p], check=True, capture_output=True, text=True)
                r = subprocess.run([exe_p], check=True, capture_output=True, text=True)
                self.assertEqual(r.stdout.strip(), "verifier_stage3_arm64: OK")

    def test_hl_verifier_stage4_rsq_cert_dual_verify_and_native(self):
        """Stage 4: dual-verify all 9 pure High-Level Ode r/s/q certificate verifier kernels on both
        x86-64 and AArch64 (`--verifier both`), verify cross-arch contract hash identity, and
        execute real r/s/q proof blocks from Ode's own .proof files on Linux x86-64 and Apple M6."""
        src = os.path.join(HERE, "examples", "verifier", "verifier_stage4.ode")
        ode_tool = os.path.join(ROOT, "lang", "ode_tool.py")
        self.assertTrue(os.path.exists(src))
        portable = [
            "v_rsq_line_kind",
            "v_rsq_eol",
            "v_scan_rsq_block",
            "v_row_contradicts_at",
            "v_row_unit_add_match",
            "v_mul_mod32",
            "v_check_s_comb_coeff",
            "v_verify_rsq_unit_cert",
        ]
        all_fns = portable + ["v_row_2a_plus_2b16"]
        root_fns = [
            "v_rsq_line_kind",
            "v_scan_rsq_block",
            "v_check_s_comb_coeff",
            "v_verify_rsq_unit_cert",
            "v_row_2a_plus_2b16",
        ]

        with tempfile.TemporaryDirectory() as d:
            cids = {}
            syms = {}
            objs = {}
            prfs = {}
            for fn in all_fns:
                for tgt in ("x86_64", "arm64"):
                    obj_p = os.path.join(d, f"{fn}_{tgt}.o")
                    prf_p = os.path.join(d, f"{fn}_{tgt}.proof")
                    res = subprocess.run(
                        [sys.executable, ode_tool, "pack", src, "--fn", fn, "--target", tgt,
                         "--c-abi", "--verifier", "both", "--out", obj_p, "--proof", prf_p],
                        capture_output=True, text=True,
                    )
                    self.assertEqual(res.returncode, 0,
                                     f"Stage 4 pack failed ({fn}, {tgt}):\n{res.stdout}\n{res.stderr}")
                    self.assertIn("VERDICT:           shown", res.stdout)
                    self.assertIn("odeverify (shown), verify2 (shown)", res.stdout)
                    m = re.search(r"SYMBOL:\s+(ode_[a-z2-7]{52})", res.stdout)
                    self.assertIsNotNone(m, res.stdout)
                    syms[(fn, tgt)] = m.group(1)
                    cids[(fn, tgt)] = m.group(1)[4:]
                    objs[(fn, tgt)] = obj_p
                    prfs[(fn, tgt)] = prf_p
            for fn in portable:
                self.assertEqual(cids[(fn, "x86_64")], cids[(fn, "arm64")],
                                 f"Stage 4 cross-arch contract hash mismatch for {fn}")

            # Extract real r/s/q refutation blocks directly from Ode's own freshly generated .proof file!
            def parse_real_rsq_blocks(proof_path):
                with open(proof_path, "r", encoding="utf-8") as f:
                    lines = f.read().splitlines()
                blocks = []
                i = 0
                while i < len(lines):
                    if lines[i].startswith("r "):
                        start = i
                        rows = []
                        steps = []
                        while i < len(lines) and (lines[i].startswith("r ") or lines[i].startswith("s ")):
                            if lines[i].startswith("r "):
                                rows.append([int(x) for x in lines[i].split()[1:]])
                            else:
                                steps.append(tuple(int(x) for x in lines[i].split()[1:]))
                            i += 1
                        if i < len(lines) and lines[i] == "q":
                            raw = "\n".join(lines[start:i + 1]) + "\n"
                            blocks.append((raw.encode("ascii"), rows, steps))
                    i += 1
                return blocks

            own_blocks = parse_real_rsq_blocks(prfs[("v_verify_rsq_unit_cert", "x86_64")])
            self.assertGreater(len(own_blocks), 0, "expected real r/s/q blocks in own .proof")

            # Pick a real unit-weight (a=1, b=1, d=1, <= 16 vars, signed i32 coeffs) block from own .proof,
            # falling back to factory/verified/utf8_is_ascii_x86_64.proof if needed.
            unit_block = None
            for cand_blocks in (own_blocks, parse_real_rsq_blocks(os.path.join(ROOT, "factory", "verified", "utf8_is_ascii_x86_64.proof"))):
                for raw_b, r_rows, s_steps in cand_blocks:
                    if not r_rows or not s_steps:
                        continue
                    if all(a == 1 and b == 1 and div == 1 for _, a, _, b, div in s_steps):
                        # Project nonzero columns down to <= 16 lanes (preserving exact linear algebra)
                        nz_cols = sorted({c for row in r_rows for c in range(1, len(row)) if row[c] != 0})
                        if len(nz_cols) <= 15:
                            proj = []
                            ok_i32 = True
                            for row in r_rows:
                                c0 = row[0] if row else 0
                                vec = [c0] + [row[c] if c < len(row) else 0 for c in nz_cols]
                                vec += [0] * (16 - len(vec))
                                if any(v < -(1 << 31) or v >= (1 << 31) for v in vec):
                                    ok_i32 = False
                                proj.append(vec)
                            if ok_i32:
                                unit_block = (raw_b, proj, s_steps)
                                break
                if unit_block is not None:
                    break
            self.assertIsNotNone(unit_block, "expected a real unit-weight r/s/q block from Ode .proof")
            real_raw, real_init_rows, real_steps = unit_block

            # Build the derived rows table & steps buffer for the real proof block
            sim_rows = [list(r) for r in real_init_rows]
            for ia, _, ib, _, _ in real_steps:
                ra, rb = sim_rows[ia], sim_rows[ib]
                sim_rows.append([((ra[k] + rb[k]) & 0xFFFFFFFF) for k in range(16)])
            rows_bytes = b"".join(
                struct.pack("<16I", *[(v & 0xFFFFFFFF) for v in row]) for row in sim_rows
            )
            steps_bytes = b"".join(struct.pack("<II", ia, ib) for ia, _, ib, _, _ in real_steps)
            real_raw_hex = ", ".join(str(b) for b in real_raw)
            rows_hex = ", ".join(str(b) for b in rows_bytes)
            steps_hex = ", ".join(str(b) for b in steps_bytes)

            def stage4_c_body(p, run_simd):
                simd_block = ""
                if run_simd:
                    simd_block = f"""
    _Alignas(64) uint32_t va[16], vb[16], vout[16];
    for (int k = 0; k < 16; k++) {{ va[k] = (uint32_t)(k * 100 + 7); vb[k] = (uint32_t)(k * 50 + 3); }}
    {p}v_row_2a_plus_2b16(vout, va, vb);
    for (int k = 0; k < 16; k++) {{ CHK(vout[k] == (uint32_t)(2U * (va[k] + vb[k]))); }}
"""
                return f"""
    /* 1. Directive line tag classifier across all 256 byte values */
    for (uint64_t b = 0; b < 256; b++) {{
        uint64_t want = (b == 'r') ? 1 : (b == 's') ? 2 : (b == 'q') ? 3 :
                        (b == 't') ? 4 : (b == 'f') ? 5 : (b == 'p') ? 6 :
                        (b == 'n') ? 7 : (b == 'k') ? 8 : (b == 'd') ? 9 : 0;
        CHK({p}v_rsq_line_kind(b) == want);
    }}
    /* 2. Real r/s/q block structural scanner on Ode's own live .proof block */
    static const uint8_t real_blk[] = {{ {real_raw_hex} }};
    CHK({p}v_scan_rsq_block(real_blk, sizeof(real_blk), 0) == sizeof(real_blk));
    /* Truncated block (missing q) must fail with 2^32 */
    CHK({p}v_scan_rsq_block(real_blk, sizeof(real_blk) - 2, 0) == (1ULL << 32));
    /* Malformed directive tag ('x ...') must fail with 2^32 */
    const char *bad_blk = "r 0 1\\nx 1 2\\nq\\n";
    CHK({p}v_scan_rsq_block((const uint8_t *)bad_blk, strlen(bad_blk), 0) == (1ULL << 32));
    /* 3. Weighted Gomory/Fourier-Motzkin column verifier (s i wa j wb d) */
    CHK({p}v_check_s_comb_coeff(7, 3, 5, 4, 1, 41) == 1);      /* 3*7 + 4*5 = 1*41 */
    CHK({p}v_check_s_comb_coeff(7, 3, 5, 4, 1, 42) == 0);      /* wrong output */
    CHK({p}v_check_s_comb_coeff(0xFFFFFFFFU, 64, 64, 1, 1, 0) == 1); /* -1*64 + 64 == 0 (mod 2^32) */
    CHK({p}v_check_s_comb_coeff(10, 2, 4, 5, 4, 10) == 1);     /* (2*10 + 5*4) == 4*10 */
    /* 4. Self-verification of real multi-step r/s/q certificate from Ode's own .proof */
    uint8_t real_rows[] = {{ {rows_hex} }};
    uint8_t real_steps[] = {{ {steps_hex} }};
    uint64_t n_init = {len(real_init_rows)}ULL, n_steps = {len(real_steps)}ULL;
    CHK({p}v_verify_rsq_unit_cert(real_rows, sizeof(real_rows), real_steps, sizeof(real_steps), n_init, n_steps) == 1);
    /* Tamper A: corrupt 1 byte in final derived row -> must refuse (0) */
    real_rows[sizeof(real_rows) - 1] ^= 1;
    CHK({p}v_verify_rsq_unit_cert(real_rows, sizeof(real_rows), real_steps, sizeof(real_steps), n_init, n_steps) == 0);
    real_rows[sizeof(real_rows) - 1] ^= 1;
    /* Tamper B: forward/self reference a_idx == cur -> must refuse (0) */
    uint32_t saved_a = 0;
    memcpy(&saved_a, real_steps, 4);
    uint32_t bad_a = (uint32_t)n_init;
    memcpy(real_steps, &bad_a, 4);
    CHK({p}v_verify_rsq_unit_cert(real_rows, sizeof(real_rows), real_steps, sizeof(real_steps), n_init, n_steps) == 0);
    memcpy(real_steps, &saved_a, 4);
    /* Tamper C: synthetic 2-step cert whose final c0 == 0 (no contradiction) -> must refuse (0) */
    uint32_t non_contra[3][16];
    memset(non_contra, 0, sizeof(non_contra));
    non_contra[0][0] = 5; non_contra[0][1] = 1;
    non_contra[1][0] = (uint32_t)(-5); non_contra[1][1] = (uint32_t)(-1);
    /* sum: c0 = 0, c1 = 0 -> NOT a contradiction! */
    uint32_t nc_steps[2] = {{ 0, 1 }};
    CHK({p}v_verify_rsq_unit_cert((const uint8_t *)non_contra, sizeof(non_contra), (const uint8_t *)nc_steps, sizeof(nc_steps), 2, 1) == 0);
    /* Changing row 1's c0 to -6 makes sum c0 = -1, c1 = 0 -> valid contradiction! */
    non_contra[1][0] = (uint32_t)(-6);
    non_contra[2][0] = (uint32_t)(-1);
    CHK({p}v_verify_rsq_unit_cert((const uint8_t *)non_contra, sizeof(non_contra), (const uint8_t *)nc_steps, sizeof(nc_steps), 2, 1) == 1);
    {simd_block}
"""

            cc = shutil.which("cc") or shutil.which("gcc") or shutil.which("clang")
            if IS_LINUX_X86 and cc:
                with open("/proc/cpuinfo", "r", encoding="utf-8") as ci:
                    has_avx512 = "avx512f" in ci.read()
                run_roots = root_fns if has_avx512 else root_fns[:-1]
                decls = "\n".join([
                    f'uint64_t {syms[("v_rsq_line_kind", "x86_64")]}(uint64_t);',
                    f'uint64_t {syms[("v_scan_rsq_block", "x86_64")]}(const uint8_t *, uint64_t, uint64_t);',
                    f'uint64_t {syms[("v_check_s_comb_coeff", "x86_64")]}(uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);',
                    f'uint64_t {syms[("v_verify_rsq_unit_cert", "x86_64")]}(const uint8_t *, uint64_t, const uint8_t *, uint64_t, uint64_t, uint64_t);',
                ] + ([
                    f'void {syms[("v_row_2a_plus_2b16", "x86_64")]}(uint32_t *, const uint32_t *, const uint32_t *);',
                ] if has_avx512 else []))
                aliases = "\n".join(f'#define fn_{fn} {syms[(fn, "x86_64")]}' for fn in run_roots)
                c_src = f"""
#include <stdint.h>
#include <stdio.h>
#include <string.h>
{decls}
{aliases}
#define CHK(cond) do {{ if (!(cond)) {{ fprintf(stderr, "FAIL line %d\\n", __LINE__); return 1; }} }} while (0)
int main(void) {{
{stage4_c_body("fn_", has_avx512)}
    puts("verifier_stage4_x86: OK");
    return 0;
}}
"""
                c_p = os.path.join(d, "run_s4.c")
                exe_p = os.path.join(d, "run_s4")
                with open(c_p, "w", encoding="utf-8") as f:
                    f.write(c_src)
                subprocess.run(
                    [cc, "-O1", "-o", exe_p, c_p] + [objs[(fn, "x86_64")] for fn in run_roots],
                    check=True, capture_output=True, text=True,
                )
                r = subprocess.run([exe_p], check=True, capture_output=True, text=True)
                self.assertEqual(r.stdout.strip(), "verifier_stage4_x86: OK")

            elif IS_MAC_ARM64 and shutil.which("clang"):
                def reloc_text(elf_path, sym_name):
                    with open(elf_path, "rb") as f:
                        b = f.read()
                    e_shoff = struct.unpack_from("<Q", b, 40)[0]
                    e_shentsize, e_shnum, e_shstrndx = struct.unpack_from("<HHH", b, 58)
                    secs = [struct.unpack_from("<IIQQQQI", b, e_shoff + i * e_shentsize) for i in range(e_shnum)]
                    shstr_off = secs[e_shstrndx][4]
                    sname = lambda idx: b[shstr_off + idx:b.index(0, shstr_off + idx)].decode("ascii", "replace")
                    tb, eoff, sv = b"", 0, {}
                    for sn, st, _, _, so, sz, sl in secs:
                        if sname(sn) == ".text":
                            tb = b[so:so + sz]
                        elif st == 2:
                            stro = secs[sl][4]
                            for idx, pos in enumerate(range(so, so + sz, 24)):
                                nm, _, _, _, val, _ = struct.unpack_from("<IBBHQQ", b, pos)
                                sv[idx] = val
                                if b[stro + nm:b.index(0, stro + nm)].decode("ascii", "replace") == sym_name:
                                    eoff = val
                    buf = bytearray(tb)
                    for sn, st, _, _, so, sz, _ in secs:
                        if st == 4 and sname(sn) == ".rela.text":
                            for pos in range(so, so + sz, 24):
                                ro, ri, ra = struct.unpack_from("<QQq", b, pos)
                                if (ri & 0xFFFFFFFF) in (282, 283):
                                    imm26 = (((sv[ri >> 32] + ra) - ro) >> 2) & 0x03FFFFFF
                                    ins = struct.unpack_from("<I", buf, ro)[0]
                                    struct.pack_into("<I", buf, ro, (ins & 0xFC000000) | imm26)
                    return bytes(buf), eoff

                types = {
                    "v_rsq_line_kind": "uint64_t (*)(uint64_t)",
                    "v_scan_rsq_block": "uint64_t (*)(const uint8_t *, uint64_t, uint64_t)",
                    "v_check_s_comb_coeff": "uint64_t (*)(uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t)",
                    "v_verify_rsq_unit_cert": "uint64_t (*)(const uint8_t *, uint64_t, const uint8_t *, uint64_t, uint64_t, uint64_t)",
                    "v_row_2a_plus_2b16": "void (*)(uint32_t *, const uint32_t *, const uint32_t *)",
                }
                load_lines = []
                for fn in root_fns:
                    code, entry = reloc_text(objs[(fn, "arm64")], syms[(fn, "arm64")])
                    bp = os.path.join(d, f"{fn}.bin")
                    with open(bp, "wb") as bf:
                        bf.write(code)
                    ty = types[fn]
                    load_lines.append(
                        f'    {ty.replace("(*)", "(*fn_" + fn + ")")} = ({ty})load_jit("{bp}", {len(code)}, {entry});'
                    )
                loads = "\n".join(load_lines)
                c_src = f"""
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <pthread.h>
#include <libkern/OSCacheControl.h>
static void *load_jit(const char *path, size_t n, size_t entry_off) {{
    uint8_t *tmp = (uint8_t *)malloc(n);
    FILE *fp = fopen(path, "rb");
    if (!tmp || !fp || fread(tmp, 1, n, fp) != n) {{ fprintf(stderr, "read %s\\n", path); exit(2); }}
    fclose(fp);
    void *p = mmap(NULL, (n + 4095) & ~4095ULL, PROT_READ|PROT_WRITE|PROT_EXEC, MAP_PRIVATE|MAP_ANON|MAP_JIT, -1, 0);
    if (p == MAP_FAILED) {{ perror("mmap"); exit(2); }}
    pthread_jit_write_protect_np(0);
    memcpy(p, tmp, n);
    pthread_jit_write_protect_np(1);
    sys_icache_invalidate(p, n);
    free(tmp);
    return (uint8_t *)p + entry_off;
}}
#define CHK(cond) do {{ if (!(cond)) {{ fprintf(stderr, "FAIL line %d\\n", __LINE__); return 1; }} }} while (0)
int main(void) {{
{loads}
{stage4_c_body("fn_", True)}
    puts("verifier_stage4_arm64: OK");
    return 0;
}}
"""
                c_p = os.path.join(d, "run_s4_arm64.c")
                exe_p = os.path.join(d, "run_s4_arm64")
                with open(c_p, "w", encoding="utf-8") as f:
                    f.write(c_src)
                subprocess.run(["clang", "-O1", "-o", exe_p, c_p], check=True, capture_output=True, text=True)
                r = subprocess.run([exe_p], check=True, capture_output=True, text=True)
                self.assertEqual(r.stdout.strip(), "verifier_stage4_arm64: OK")


if __name__ == "__main__":
    unittest.main()
