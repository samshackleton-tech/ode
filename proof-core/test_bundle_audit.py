#!/usr/bin/env pypy3
"""End-to-end tests for Step B: multi-function `ode pack` & `ode audit`, loop-free auto-proving,
adversarial controls on local helpers/gaps/shadowing, and flagship single-`.o` bundles of full
single-threaded BLAKE3 on BOTH AArch64 (7 functions, 1,832 instructions) and x86-64 (14 functions,
3,761 instructions) with native execution on Linux x86-64!

    pypy3 proof-core/test_bundle_audit.py
"""

import os
import platform
import shutil
import subprocess
import sys
import tempfile
import textwrap
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
KCHECK = os.path.join(ROOT, "kcheck")
ARM = os.path.join(HERE, "examples", "arm64")
for d in (os.path.join(ROOT, "lang"), HERE, KCHECK, os.path.join(ROOT, "core"), os.path.join(ROOT, "arm64")):
    if d not in sys.path:
        sys.path.insert(0, d)

import ode_audit
import ode_canon
import odec

ODE_TOOL = os.path.join(ROOT, "lang", "ode_tool.py")
LAKE = shutil.which("lake")
CC = shutil.which("cc") or shutil.which("gcc") or shutil.which("clang")
ARCH = platform.machine()
IS_LINUX_X86 = platform.system() == "Linux" and ARCH in ("x86_64", "amd64")

QUAD_UNIFIED = textwrap.dedent("""\
    def double(n) { n + n }

    fn step(a: number)
      requires a < 1000000000
      returns a + a
      trace depends on a
    {
      for x86_64 stack 0 calling {
        in a = r10
        out = r11
        preserves rdi, rsi, rdx, rcx, r8, rbx, rbp, r12, r13, r14, r15
      } {
        mov r11, r10
        add r11, r10
        ret
      }
      for arm64 stack 0 calling {
        in a = x9
        out = x10
        preserves x0, x1, x2, x3, x5, x6, x7, x8, x11, x12, x13, x14, x15, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29
      } {
        add x10, x9, x9
        ret
      }
    }

    fn quad(x: number)
      requires x < 500000000
      returns double(double(x))
      trace depends on x
    {
      for x86_64 stack 16 {
        mov r10, rdi
        call step
        mov r10, r11
        call step
        mov rax, r11
        ret
      }
      for arm64 stack 16 {
        sub sp, sp, 16
        str x30, [sp, 0]
        mov x9, x0
        bl step
        mov x9, x10
        bl step
        mov x0, x10
        ldr x30, [sp, 0]
        add sp, sp, 16
        ret
      }
    }
""")

INC_UNIFIED = textwrap.dedent("""\
    def plus7(n) { n + 7 }

    fn inc7(x: number)
      requires x < 1000000
      returns plus7(x)
      trace depends on x
    {
      for x86_64 stack 0 {
        mov rax, rdi
        add rax, 7
        ret
      }
      for arm64 stack 0 {
        add x0, x0, 7
        ret
      }
    }
""")


def _replace_section_body(elf_bytes, sec_name, new_body):
    parsed = ode_audit.parse_elf64(elf_bytes)
    secs = [dict(s) for s in parsed["sections"]]
    found = [s for s in secs if s["name"] == sec_name]
    assert len(found) == 1
    found[0]["body"] = bytes(new_body)
    found[0]["size"] = len(new_body)
    return ode_audit._rebuild_elf64(parsed["machine"], parsed["shstrndx"], secs)


@unittest.skipUnless(LAKE, "Lean's lake is not installed")
class BundleAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.mkdtemp(prefix="ode_bundle_test_")
        cls.quad_src = os.path.join(cls.tmp, "quad.ode")
        with open(cls.quad_src, "w", encoding="utf-8") as f:
            f.write(QUAD_UNIFIED)
        cls.inc_src = os.path.join(cls.tmp, "inc.ode")
        with open(cls.inc_src, "w", encoding="utf-8") as f:
            f.write(INC_UNIFIED)

        # Pack multi-function `quad.ode` (custom `calling` on `step`!) on BOTH x86-64 and AArch64!
        cls.quad_x86_o = os.path.join(cls.tmp, "quad_x86.o")
        cls.quad_x86_p = os.path.join(cls.tmp, "quad_x86.proof")
        cls.quad_x86_res = ode_audit.pack_verified(
            cls.quad_src, None, cls.quad_x86_o, cls.quad_x86_p, fn_name="quad", target="x86_64",
        )
        cls.quad_arm_o = os.path.join(cls.tmp, "quad_arm.o")
        cls.quad_arm_p = os.path.join(cls.tmp, "quad_arm.proof")
        cls.quad_arm_res = ode_audit.pack_verified(
            cls.quad_src, None, cls.quad_arm_o, cls.quad_arm_p, fn_name="quad", target="arm64",
        )

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def test_01_multi_fn_quad_pack_audit_and_native_exec(self):
        """Multi-function unified `quad.ode` packs to ONE self-contained `.o` + `.proof` on BOTH
        x86-64 and AArch64 with identical 52-char `.ode.ocl`, 1 exported symbol, 1 local custom-ABI
        helper `h0`, zero author names in `.symtab`, and native execution on Linux x86-64."""
        for label, res, obj_p, prf_p in (
            ("x86_64", self.quad_x86_res, self.quad_x86_o, self.quad_x86_p),
            ("arm64", self.quad_arm_res, self.quad_arm_o, self.quad_arm_p),
        ):
            self.assertEqual(res["verdict"], "shown", f"{label}: {res}")
            self.assertEqual(res["coverage"]["functions"], 2)
            self.assertEqual(res["coverage"]["local_helpers"], 1)
            self.assertEqual(res["coverage"]["exported_symbols"], 1)
            self.assertEqual(res["coverage"]["hooks"], 0)
            with open(obj_p, "rb") as f:
                elf = ode_audit.parse_elf64(f.read())
            syms = [s for s in elf["symbols"] if s["name"]]
            globals_ = [s for s in syms if s["bind"] == ode_audit.STB_GLOBAL]
            locals_ = [s for s in syms if s["bind"] == ode_audit.STB_LOCAL and s["type"] == ode_audit.STT_FUNC]
            undefs = [s for s in syms if s["shndx"] == 0]
            self.assertEqual([s["name"] for s in globals_], [res["symbol"]])
            self.assertEqual([s["name"] for s in locals_], ["h0"])
            self.assertEqual(undefs, [])
            # No author function names leak into ELF symbol table.
            all_names = {s["name"] for s in syms}
            self.assertNotIn("step", all_names)
            self.assertNotIn("quad", all_names)
            # CLI `ode audit` succeeds cleanly.
            cli = subprocess.run(
                [sys.executable, ODE_TOOL, "audit", obj_p, "--proof", prf_p,
                 "--expect-contract", res["contract_b32"]],
                capture_output=True, text=True, check=False,
            )
            self.assertEqual(cli.returncode, 0, cli.stdout + cli.stderr)
            self.assertIn("2 functions (1 exported, 1 local)", cli.stdout)
            self.assertIn("VERDICT:           shown", cli.stdout)

        # Identical canonical `.ocl` hash across x86-64 and AArch64!
        self.assertEqual(self.quad_x86_res["contract_b32"], self.quad_arm_res["contract_b32"])

        if IS_LINUX_X86 and CC:
            sym = self.quad_x86_res["symbol"]
            c_path = os.path.join(self.tmp, "run_quad.c")
            exe_path = os.path.join(self.tmp, "run_quad")
            with open(c_path, "w", encoding="utf-8") as cf:
                cf.write(
                    f"#include <stdint.h>\n#include <stdio.h>\n"
                    f"extern uint64_t {sym}(uint64_t x);\n"
                    f"int main(void) {{\n"
                    f"  uint64_t xs[] = {{0, 1, 7, 12345, 499999999}};\n"
                    f"  for (int i = 0; i < 5; i++) {{\n"
                    f"    uint64_t g = {sym}(xs[i]);\n"
                    f"    if (g != 4 * xs[i]) {{ fprintf(stderr, \"FAIL %llu -> %llu\\n\", (unsigned long long)xs[i], (unsigned long long)g); return 1; }}\n"
                    f"  }}\n"
                    f"  puts(\"QUAD_NATIVE_OK\"); return 0;\n"
                    f"}}\n"
                )
            subprocess.run([CC, c_path, self.quad_x86_o, "-o", exe_path], check=True)
            run = subprocess.run([exe_path], capture_output=True, text=True, check=True)
            self.assertIn("QUAD_NATIVE_OK", run.stdout)

    def test_02_auto_prove_loop_free_single_fn_without_proof(self):
        """`ode audit single.o` WITHOUT `--proof` auto-proves loop-free single-function `.o` on both
        x86-64 and AArch64 (still verified by `odeverify`), and refuses multi-function `.o` without `--proof`."""
        for target in ("x86_64", "arm64"):
            o_p = os.path.join(self.tmp, f"inc_{target}.o")
            p_p = os.path.join(self.tmp, f"inc_{target}.proof")
            packed = ode_audit.pack_verified(self.inc_src, None, o_p, p_p, fn_name="inc7", target=target)
            self.assertEqual(packed["verdict"], "shown")
            # Audit WITHOUT `--proof` via API and CLI!
            res = ode_audit.audit_binary(o_p, proof_path=None, expect_contract=packed["contract_b32"])
            self.assertEqual(res["verdict"], "shown", res)
            self.assertTrue(res.get("auto_proved"))
            cli = subprocess.run(
                [sys.executable, ODE_TOOL, "audit", o_p, "--expect-contract", packed["contract_b32"]],
                capture_output=True, text=True, check=False,
            )
            self.assertEqual(cli.returncode, 0, cli.stdout + cli.stderr)
            self.assertIn("VERDICT:           shown", cli.stdout)

        # Multi-function binary without `--proof` MUST refuse cleanly.
        multi_no_prf = ode_audit.audit_binary(self.quad_x86_o, proof_path=None)
        self.assertEqual(multi_no_prf["verdict"], "refused")
        self.assertTrue(any("--proof" in e for e in multi_no_prf["errors"]), multi_no_prf["errors"])

    def test_03_adversarial_tamper_local_helper_refused(self):
        """Flipping an instruction inside local helper `h0` (`step`) MUST be refused by `ode audit`."""
        with open(self.quad_x86_o, "rb") as f:
            raw = f.read()
        elf = ode_audit.parse_elf64(raw)
        h0_sym = next(s for s in elf["symbols"] if s["name"] == "h0")
        text = bytearray(elf["by_name"][".text"][0]["body"])
        # Corrupt the `add r11, r10` instruction inside `h0` (replace with `sub` or flip a bit).
        text[h0_sym["value"] + 4] ^= 0x08
        bad = _replace_section_body(raw, ".text", bytes(text))
        bad_p = os.path.join(self.tmp, "bad_helper_flip.o")
        with open(bad_p, "wb") as f:
            f.write(bad)
        res = ode_audit.audit_binary(bad_p, self.quad_x86_p)
        self.assertEqual(res["verdict"], "refused", res)

    def test_04_adversarial_missing_local_fn_from_proof_order_refused(self):
        """A `.proof` omitting a `STB_LOCAL` function present in `.text` MUST be refused."""
        with open(self.quad_x86_p, "r", encoding="utf-8") as f:
            prf = f.read()
        # Drop `h0` from `order:` line.
        bad_prf = prf.replace(f"order: h0 {self.quad_x86_res['symbol']}", f"order: {self.quad_x86_res['symbol']}", 1)
        bad_pp = os.path.join(self.tmp, "bad_order.proof")
        with open(bad_pp, "w", encoding="utf-8") as f:
            f.write(bad_prf)
        res = ode_audit.audit_binary(self.quad_x86_o, bad_pp)
        self.assertEqual(res["verdict"], "refused")
        self.assertTrue(any("local function set mismatch" in e for e in res["errors"]), res["errors"])

    def test_05_adversarial_helper_spec_shadowing_ocl_refused(self):
        """A `.proof` helper block trying to redefine `f0` or the exported symbol from `.ode.ocl`
        MUST be refused by `ode.with_proof`."""
        with open(self.quad_x86_p, "r", encoding="utf-8") as f:
            prf = f.read()
        # Attack A: try to shadow `f0` (canonical `double`).
        atk_a = prf.replace(
            ode_audit.PROOF_BEGIN,
            "def f0(x) { x }\n" + ode_audit.PROOF_BEGIN,
            1,
        )
        pa = os.path.join(self.tmp, "atk_shadow_def.proof")
        with open(pa, "w", encoding="utf-8") as f:
            f.write(atk_a)
        ra = ode_audit.audit_binary(self.quad_x86_o, pa)
        self.assertEqual(ra["verdict"], "refused")
        self.assertTrue(any("helper specification" in e and "f0" in e for e in ra["errors"]), ra["errors"])

        # Attack B: try to redeclare the exported contract symbol.
        exp_sym = self.quad_x86_res["symbol"]
        atk_b = prf.replace(
            ode_audit.PROOF_BEGIN,
            f"contract {exp_sym}(a0: number) {{ returns a0  stack 0 }}\n" + ode_audit.PROOF_BEGIN,
            1,
        )
        pb = os.path.join(self.tmp, "atk_shadow_exp.proof")
        with open(pb, "w", encoding="utf-8") as f:
            f.write(atk_b)
        rb = ode_audit.audit_binary(self.quad_x86_o, pb)
        self.assertEqual(rb["verdict"], "refused")
        self.assertTrue(any("helper specification" in e for e in rb["errors"]), rb["errors"])

    def test_06_adversarial_non_nop_byte_in_alignment_gap_refused(self):
        """Putting non-NOP bytes (e.g. `0xcc` int3 or a branch) in the alignment gap between `h0`
        and `ode_<52>` MUST be refused by `ode audit`."""
        with open(self.quad_x86_o, "rb") as f:
            raw = f.read()
        elf = ode_audit.parse_elf64(raw)
        h0_sym = next(s for s in elf["symbols"] if s["name"] == "h0")
        exp_sym = next(s for s in elf["symbols"] if s["name"] == self.quad_x86_res["symbol"])
        self.assertGreater(exp_sym["value"], h0_sym["value"] + h0_sym["size"])
        text = bytearray(elf["by_name"][".text"][0]["body"])
        gap_pos = h0_sym["value"] + h0_sym["size"]
        text[gap_pos] = 0xCC  # int3 (not a pure NOP)
        bad = _replace_section_body(raw, ".text", bytes(text))
        bad_p = os.path.join(self.tmp, "bad_gap.o")
        with open(bad_p, "wb") as f:
            f.write(bad)
        res = ode_audit.audit_binary(bad_p, self.quad_x86_p)
        self.assertEqual(res["verdict"], "refused")
        self.assertTrue(any("non-NOP" in e for e in res["errors"]), res["errors"])

    def test_07_flagship_full_blake3_arm64_bundle(self):
        """Pack & audit ALL 7 functions (1,832 instructions) of single-threaded AArch64 BLAKE3
        into ONE self-contained hash-bound `.o` + `.proof`."""
        fns = [
            ("compress_arm64.ode", "compress1_arm64", "blake3_servil_compress_in_place_arm64"),
            ("pad_arm64.ode",      "pad",             "b3l_pad_arm64"),
            ("hash_arm64.ode",     "node_out_arm64",  "b3l_node_out_arm64"),
            ("hash_arm64.ode",     "chunk_node_arm64","b3l_chunk_node_arm64"),
            ("wide4_arm64.ode",    "wide4_arm64",     "b3l_wide4_arm64"),
            ("hash_arm64.ode",     "subtree_arm64",   "b3l_subtree_arm64"),
            ("hash_arm64.ode",     "hashr_arm64",     "b3l_hashr_arm64"),
        ]
        unit_elfs = []
        orig_order = []
        for src, fn, sym in fns:
            inf = odec.compile_info(os.path.join(ARM, src), fn)
            self.assertEqual(inf["symbol"], sym)
            unit_elfs.append(inf["elf"])
            orig_order.append(sym)
        with open(os.path.join(KCHECK, "blake3.spec"), "r", encoding="utf-8") as f:
            full_spec = f.read()
        for nm in ("compress_arm64.spec", "pad_arm64.spec", "hash_arm64.spec", "wide4_arm64.spec"):
            with open(os.path.join(ARM, nm), "r", encoding="utf-8") as f:
                full_spec += "\n" + f.read()

        out_o = os.path.join(self.tmp, "blake3_arm64_bundle.o")
        out_p = os.path.join(self.tmp, "blake3_arm64_bundle.proof")
        res = ode_audit.pack_bundle(
            unit_elfs,
            orig_order,
            "b3l_hashr_arm64",
            full_spec,
            out_o,
            out_p,
            existing_proof_path=os.path.join(HERE, "proofs", "b3hashr_arm64.proof"),
        )
        self.assertEqual(res["verdict"], "shown", res)
        self.assertEqual(res["contract_b32"], "ckdrhllybtjzr7vgscyhlgz6sxqaga347kozoepvqk3b54ohbfra")
        self.assertEqual(res["coverage"]["functions"], 7)
        self.assertEqual(res["coverage"]["local_helpers"], 6)
        self.assertEqual(res["coverage"]["instructions"], 1832)
        self.assertEqual(res["coverage"]["exported_symbols"], 1)
        self.assertEqual(res["coverage"]["hooks"], 0)
        # Confirm ZERO author names in ELF .symtab!
        with open(out_o, "rb") as f:
            elf = ode_audit.parse_elf64(f.read())
        names = [s["name"] for s in elf["symbols"] if s["name"]]
        self.assertFalse(any("blake3" in n or "b3l_" in n for n in names), names)

    def test_08_flagship_full_blake3_x86_64_bundle_and_native_vectors(self):
        """Pack & audit ALL 14 functions (3,761 instructions, incl. shared-tail k32/p32 and `.rodata`)
        of single-threaded x86-64 BLAKE3 into ONE self-contained `.o` + `.proof`, and link + run
        against official BLAKE3 test vectors on Linux x86-64!"""
        bdir = os.path.join(self.tmp, "b3_x86_objs")
        os.makedirs(bdir, exist_ok=True)
        subprocess.run([sys.executable, os.path.join(ROOT, "lang", "odec.py"),
                        os.path.join(KCHECK, "hash.ode"), "--all", bdir], check=True, capture_output=True)
        subprocess.run([sys.executable, os.path.join(KCHECK, "kernels.py"), bdir],
                       check=True, capture_output=True)
        # Collect the 13 ELF object files covering all 14 functions (k32.o holds both k32 and p32!).
        obj_files = [
            "one_sse41.o",
            "one.o",
            "k32.o",
            "p16.o",
            "pad.o",
            "node_out.o",
            "chunk_node.o",
            "wide32.o",
            "wide128.o",
            "take.o",
            "part32.o",
            "subtree.o",
            "hashr.o",
        ]
        orig_order = [
            "blake3_servil_compress_in_place_sse41",
            "blake3_servil_compress_in_place_avx512",
            "blake3_servil_avx512_k32",
            "blake3_servil_avx512_p16",
            "blake3_servil_avx512_p32",
            "b3l_pad",
            "b3l_node_out",
            "b3l_chunk_node",
            "b3l_wide32",
            "b3l_wide128",
            "b3l_take",
            "b3l_part32",
            "b3l_subtree",
            "b3l_hashr",
        ]
        unit_elfs = []
        for of in obj_files:
            with open(os.path.join(bdir, of), "rb") as f:
                unit_elfs.append(f.read())
        with open(os.path.join(KCHECK, "blake3.spec"), "r", encoding="utf-8") as f:
            full_spec = f.read()
        with open(os.path.join(KCHECK, "proofs", "inner.spec"), "r", encoding="utf-8") as f:
            full_spec += "\n" + f.read()
        # Concatenate the 14 kept x86-64 BLAKE3 proof files into one temp file.
        comb_prf = os.path.join(self.tmp, "b3_x86_orig.proof")
        with open(comb_prf, "w", encoding="utf-8") as out:
            for nm in orig_order:
                with open(os.path.join(HERE, "proofs", nm + ".proof"), "r", encoding="utf-8") as pf:
                    out.write(pf.read())

        out_o = os.path.join(self.tmp, "blake3_x86_bundle.o")
        out_p = os.path.join(self.tmp, "blake3_x86_bundle.proof")
        res = ode_audit.pack_bundle(
            unit_elfs,
            orig_order,
            "b3l_hashr",
            full_spec,
            out_o,
            out_p,
            existing_proof_path=comb_prf,
        )
        self.assertEqual(res["verdict"], "shown", res)
        self.assertEqual(res["contract_b32"], "7jb2pyzuwz6tqd3qmjsra3mk36tl4547sfpy3at5scbk772lbila")
        self.assertEqual(res["coverage"]["functions"], 14)
        self.assertEqual(res["coverage"]["local_helpers"], 13)
        self.assertEqual(res["coverage"]["exported_symbols"], 1)
        self.assertEqual(res["coverage"]["hooks"], 0)
        # Confirm ZERO author names in ELF .symtab!
        with open(out_o, "rb") as f:
            elf = ode_audit.parse_elf64(f.read())
        names = [s["name"] for s in elf["symbols"] if s["name"]]
        self.assertFalse(any("blake3" in n or "b3l_" in n for n in names), names)

        # On Linux x86-64 with AVX-512 & cc, link and execute the audited `.o` directly!
        if IS_LINUX_X86 and CC:
            with open("/proc/cpuinfo", "r", encoding="utf-8") as ci:
                has_avx512 = "avx512f" in ci.read()
            sym = res["symbol"]
            c_path = os.path.join(self.tmp, "run_b3.c")
            exe_path = os.path.join(self.tmp, "run_b3")
            plat_val = 5 if has_avx512 else 0
            # Expected BLAKE3-256 digests (hex) from official BLAKE3 spec for len 0, 64, 1024, 1025, 32768.
            lens = [0, 64, 1024, 1025, 32768]
            expected_hex = [
                ode_canon.blake3_256(bytes(i % 251 for i in range(n))).hex()
                for n in lens
            ]
            checks = []
            for n, hx in zip(lens, expected_hex):
                checks.append(f'  if (!check_len({n}, "{hx}", {plat_val})) return 1;')
            with open(c_path, "w", encoding="utf-8") as cf:
                cf.write(textwrap.dedent(f"""\
                    #include <stdint.h>
                    #include <stdio.h>
                    #include <stdlib.h>
                    #include <string.h>
                    extern void {sym}(uint8_t *out, const uint8_t *in, uint64_t len, const uint8_t *key, uint8_t flags, uint64_t plat);
                    static const uint32_t IV[8] = {{
                      0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
                      0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19
                    }};
                    static int check_len(size_t n, const char *want, uint64_t plat) {{
                      uint8_t *buf = malloc(n ? n : 1);
                      for (size_t i = 0; i < n; i++) buf[i] = (uint8_t)(i % 251);
                      uint8_t out[32] = {{0}};
                      {sym}(out, buf, (uint64_t)n, (const uint8_t *)IV, 0, plat);
                      free(buf);
                      char got[65];
                      for (int i = 0; i < 32; i++) sprintf(got + 2 * i, "%02x", out[i]);
                      if (strcmp(got, want) != 0) {{
                        fprintf(stderr, "MISMATCH len=%zu got=%s want=%s\\n", n, got, want);
                        return 0;
                      }}
                      return 1;
                    }}
                    int main(void) {{
                    {chr(10).join(checks)}
                      puts("B3_BUNDLE_NATIVE_OK");
                      return 0;
                    }}
                """))
            subprocess.run([CC, c_path, out_o, "-o", exe_path], check=True)
            run = subprocess.run([exe_path], capture_output=True, text=True, check=True)
            self.assertIn("B3_BUNDLE_NATIVE_OK", run.stdout)


if __name__ == "__main__":
    unittest.main()
