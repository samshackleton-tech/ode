#!/usr/bin/env pypy3
"""Verify the fast short-input x86-64 BLAKE3 bundle (`examples/hashr_fast/hash_fast.ode` —
17 functions including custom-calling `b3l_pad_fast` with `stack 0` and zero-spill short-input
paths in `b3l_chunk_node_fast` and `b3l_hashr`) in ONE `ode audit` + `odeverify` call against
the exact canonical BLAKE3 contract (`7jb2pyzuwz6tqd3qmjsra3mk36tl4547sfpy3at5scbk772lbila`),
check negative controls on `b3l_pad_fast`'s custom `calling` contract, and run official BLAKE3
vectors natively on Linux x86-64.

    pypy3 proof-core/test_hashr_fast.py
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
FAST = os.path.join(HERE, "examples", "hashr_fast")
for d in (HERE, FAST, os.path.join(ROOT, "lang"), KCHECK, os.path.join(ROOT, "core")):
    if d not in sys.path:
        sys.path.insert(0, d)

import lean_verify
import ode_audit
import ode_canon
import odec
import prove_fast

LAKE = shutil.which("lake")
CC = shutil.which("cc") or shutil.which("gcc") or shutil.which("clang")
IS_LINUX_X86 = platform.system() == "Linux" and platform.machine() in ("x86_64", "amd64")


@unittest.skipUnless(LAKE, "Lean's lake is not installed")
class HashrFastTests(unittest.TestCase):
    def test_01_full_17fn_fast_bundle_audit_and_native_vectors(self):
        """All 17 functions (custom-calling `b3l_pad_fast` + zero-spill `b3l_chunk_node_fast`
        + zero-spill `b3l_hashr` + AVX-512 wide tree) pass `ode audit` with the exact canonical
        BLAKE3 contract hash and match official BLAKE3 vectors natively on Linux x86-64."""
        full_spec = prove_fast.load_full_spec()
        src = os.path.join(FAST, "hash_fast.ode")
        with tempfile.TemporaryDirectory(prefix="ode_hashr_fast_") as d:
            bdir = os.path.join(d, "orig")
            os.makedirs(bdir)
            subprocess.run([sys.executable, os.path.join(ROOT, "lang", "odec.py"),
                            os.path.join(KCHECK, "hash.ode"), "--all", bdir], check=True, capture_output=True)
            subprocess.run([sys.executable, os.path.join(KCHECK, "kernels.py"), bdir],
                           check=True, capture_output=True)
            with open(os.path.join(bdir, "hashr.o"), "rb") as f:
                long_elf = ode_audit.rename_elf_symbol(f.read(), "b3l_hashr", "b3l_hashr_long")
            long_o = os.path.join(bdir, "hashr_long.o")
            with open(long_o, "wb") as f:
                f.write(long_elf)

            k16_o = os.path.join(d, "k16.o"); odec.build(os.path.join(FAST, "k16.ode"), "k16", k16_o)
            pad_o = os.path.join(d, "pad_fast.o"); odec.build(src, "pad_fast", pad_o)
            chk_o = os.path.join(d, "chunk_node_fast.o"); odec.build(src, "chunk_node_fast", chk_o)
            hk16_o = os.path.join(d, "hashr_k16.o"); odec.build(src, "hashr_k16", hk16_o)
            hsh_o = os.path.join(d, "hashr_fast.o"); odec.build(src, "hashr_fast", hsh_o)

            order19 = (
                prove_fast.KEPT_INNER
                + ["blake3_servil_avx512_k16", "b3l_hashr_long", "b3l_pad_fast",
                   "b3l_chunk_node_fast", "b3l_hashr_k16", "b3l_hashr"]
            )
            unit_files = [
                os.path.join(bdir, "one_sse41.o"),
                os.path.join(bdir, "one.o"),
                os.path.join(bdir, "k32.o"),
                os.path.join(bdir, "p16.o"),
                os.path.join(bdir, "pad.o"),
                os.path.join(bdir, "node_out.o"),
                os.path.join(bdir, "chunk_node.o"),
                os.path.join(bdir, "wide32.o"),
                os.path.join(bdir, "wide128.o"),
                os.path.join(bdir, "take.o"),
                os.path.join(bdir, "part32.o"),
                os.path.join(bdir, "subtree.o"),
                k16_o,
                long_o,
                pad_o,
                chk_o,
                hk16_o,
                hsh_o,
            ]
            unit_elfs = []
            for uf in unit_files:
                with open(uf, "rb") as f:
                    unit_elfs.append(f.read())

            comb_prf = os.path.join(d, "all19.prf")
            with open(comb_prf, "w", encoding="utf-8") as out:
                for nm in prove_fast.KEPT_INNER:
                    with open(os.path.join(HERE, "proofs", nm + ".proof"), "r", encoding="utf-8") as f:
                        out.write(f.read())
                with open(os.path.join(FAST, "b3l_k16.proof"), "r", encoding="utf-8") as f:
                    out.write(f.read())
                with open(os.path.join(HERE, "proofs", "b3l_hashr.proof"), "r", encoding="utf-8") as f:
                    out.write(f.read().replace("for b3l_hashr\n", "for b3l_hashr_long\n", 1))
                for nm in ("b3l_pad_fast.proof", "b3l_chunk_node_fast.proof", "b3l_hashr_k16.proof", "b3l_hashr_fast.proof"):
                    with open(os.path.join(FAST, nm), "r", encoding="utf-8") as f:
                        out.write(f.read())

            out_o = os.path.join(d, "b3hashr_fast.o")
            out_p = os.path.join(d, "b3hashr_fast.proof")
            res = ode_audit.pack_bundle(
                unit_elfs, order19, "b3l_hashr", full_spec, out_o, out_p,
                existing_proof_path=comb_prf,
            )
            self.assertEqual(res["verdict"], "shown", res)
            self.assertEqual(res["contract_b32"], "7jb2pyzuwz6tqd3qmjsra3mk36tl4547sfpy3at5scbk772lbila")
            self.assertEqual(res["coverage"]["functions"], 19)
            self.assertEqual(res["coverage"]["local_helpers"], 18)
            self.assertEqual(res["coverage"]["exported_symbols"], 1)
            self.assertEqual(res["coverage"]["hooks"], 0)

            if IS_LINUX_X86 and CC:
                with open("/proc/cpuinfo", "r", encoding="utf-8") as ci:
                    has_avx512 = "avx512f" in ci.read()
                plat_val = 5 if has_avx512 else 3
                sym = res["symbol"]
                c_p = os.path.join(d, "run_fast.c")
                exe_p = os.path.join(d, "run_fast")
                lens = [0, 1, 3, 63, 64, 65, 128, 256, 1023, 1024, 1025, 4096, 32768]
                checks = []
                for n in lens:
                    hx = ode_canon.blake3_256(bytes(i % 251 for i in range(n))).hex()
                    checks.append(f'  if (!chk({n}, "{hx}", {plat_val})) return 1;')
                with open(c_p, "w", encoding="utf-8") as cf:
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
                        static int chk(size_t n, const char *want, uint64_t plat) {{
                          uint8_t *buf = malloc(n + 7);
                          for (size_t i = 0; i < n; i++) buf[i + 3] = (uint8_t)(i % 251);
                          uint8_t out[32] = {{0}};
                          {sym}(out, buf + 3, (uint64_t)n, (const uint8_t *)IV, 0, plat);
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
                          puts("FAST_B3_NATIVE_OK");
                          return 0;
                        }}
                    """))
                subprocess.run([CC, c_p, out_o, "-o", exe_p], check=True)
                run = subprocess.run([exe_p], capture_output=True, text=True, check=True)
                self.assertIn("FAST_B3_NATIVE_OK", run.stdout)

    def test_02_negative_control_clobber_custom_preserved_reg_refused(self):
        """Clobbering `rdi` (which `b3l_pad_fast` promises to preserve via `calling { ... }`)
        MUST be refused by Lean `odeverify`."""
        full_spec = prove_fast.load_full_spec()
        with open(os.path.join(FAST, "hash_fast.ode"), "r", encoding="utf-8") as f:
            mut = f.read().replace(
                "fn pad_fast as \"b3l_pad_fast\" {\n",
                "fn pad_fast as \"b3l_pad_fast\" {\n  mov rdi, 0\n",
                1,
            )
        with tempfile.TemporaryDirectory(prefix="ode_hashr_neg_") as d:
            m_src = os.path.join(d, "mut.ode")
            m_obj = os.path.join(d, "mut.o")
            with open(m_src, "w", encoding="utf-8") as f:
                f.write(mut)
            odec.build(m_src, "pad_fast", m_obj)
            ok, _ = lean_verify.verify(full_spec, [(m_obj, "b3l_pad_fast")], os.path.join(FAST, "b3l_pad_fast.proof"))
            self.assertFalse(ok)


if __name__ == "__main__":
    unittest.main()
