#!/usr/bin/env pypy3
"""Dual-verification (`--verifier both`) and native execution test for the portable
100% pure High-Level Ode 1-block BLAKE3 compression kernel (`compress_hl.ode`),
verifying exact contract-ID identity with hand-written assembly `compress_arm64.ode`
and exact bit-for-bit BLAKE3 output on Linux x86-64 and Apple M6 AArch64."""
import os, platform, re, shutil, struct, subprocess, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
ODE_TOOL = os.path.join(ROOT, "lang", "ode_tool.py")
STD_DIR = os.path.join(ROOT, "std")
FAST_DIR = os.path.join(HERE, "examples", "hashr_arm64_fast")
SRC_HL = os.path.join(FAST_DIR, "compress_hl.ode")
SRC_ASM = os.path.join(FAST_DIR, "compress_arm64.ode")

IS_LINUX_X86 = (platform.system() == "Linux" and platform.machine() in ("x86_64", "AMD64"))
IS_MAC_ARM64 = (platform.system() == "Darwin" and platform.machine() == "arm64")


def extract_text(elf_path):
    with open(elf_path, "rb") as f:
        b = f.read()
    e_shoff = struct.unpack_from("<Q", b, 40)[0]
    e_shentsize, e_shnum, e_shstrndx = struct.unpack_from("<HHH", b, 58)
    secs = [struct.unpack_from("<IIQQQQI", b, e_shoff + i * e_shentsize) for i in range(e_shnum)]
    shstr = secs[e_shstrndx][4]
    for sn, _, _, _, so, sz, _ in secs:
        nm = b[shstr + sn:b.index(0, shstr + sn)].decode("ascii", "replace")
        if nm == ".text":
            return b[so:so + sz]
    raise RuntimeError("no .text section")


@unittest.skipUnless(shutil.which("lake"), "Lean's `lake` is not installed here")
class TestBlake3CompressHL(unittest.TestCase):
    def test_compress_hl_dual_verify_contract_identity_and_native(self):
        with tempfile.TemporaryDirectory() as d:
            syms, objs = {}, {}
            for label, src, tgt in (
                ("hl_x86", SRC_HL, "x86_64"),
                ("hl_arm64", SRC_HL, "arm64"),
                ("asm_arm64", SRC_ASM, "arm64"),
            ):
                o = os.path.join(d, f"{label}.o")
                p = os.path.join(d, f"{label}.proof")
                res = subprocess.run(
                    [sys.executable, ODE_TOOL, "pack", src, "--fn", "compress1", "--target", tgt,
                     "--store", STD_DIR, "--store", FAST_DIR,
                     "--c-abi", "--verifier", "both", "--out", o, "--proof", p],
                    capture_output=True, text=True,
                )
                self.assertEqual(res.returncode, 0, f"pack failed ({label}):\n{res.stdout}\n{res.stderr}")
                self.assertIn("VERDICT:           shown", res.stdout)
                self.assertIn("odeverify (shown), verify2 (shown)", res.stdout)
                m = re.search(r"SYMBOL:\s+(ode_[a-z2-7]{52})", res.stdout)
                self.assertIsNotNone(m, res.stdout)
                syms[label] = m.group(1)
                objs[label] = o

            # Pure High-Level Ode `compress_hl.ode` has the exact same 52-char contract ID
            # as hand-written assembly `compress_arm64.ode` on AArch64.
            self.assertEqual(syms["hl_arm64"], syms["asm_arm64"])

            # Official BLAKE3 root vectors:
            # 1. Empty input (0 bytes, flags = CHUNK_START|CHUNK_END|ROOT = 11):
            #    af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262
            # 2. 64-byte ramp [0, 1, ..., 63] (flags = 11):
            #    4eed7141ea4a5cd4b788606bd23f46e212af9cacebacdc7d1f4c6dc7f2511b98
            c_checks = """
    static const uint32_t IV[8] = {
        0x6A09E667U, 0xBB67AE85U, 0x3C6EF372U, 0xA54FF53AU,
        0x510E527FU, 0x9B05688CU, 0x1F83D9ABU, 0x5BE0CD19U
    };
    /* Vector 1: empty input */
    static const uint8_t want_empty[32] = {
        0xaf,0x13,0x49,0xb9,0xf5,0xf9,0xa1,0xa6,0xa0,0x40,0x4d,0xea,0x36,0xdc,0xc9,0x49,
        0x9b,0xcb,0x25,0xc9,0xad,0xc1,0x12,0xb7,0xcc,0x9a,0x93,0xca,0xe4,0x1f,0x32,0x62
    };
    uint32_t h[8];
    uint8_t z[64];
    memset(z, 0, 64);
    memcpy(h, IV, 32);
    fn_compress1(h, z, 0, 0, 11);
    CHK(memcmp(h, want_empty, 32) == 0);
    /* Vector 2: 64-byte ramp 0..63 */
    static const uint8_t want_ramp64[32] = {
        0x4e,0xed,0x71,0x41,0xea,0x4a,0x5c,0xd4,0xb7,0x88,0x60,0x6b,0xd2,0x3f,0x46,0xe2,
        0x12,0xaf,0x9c,0xac,0xeb,0xac,0xdc,0x7d,0x1f,0x4c,0x6d,0xc7,0xf2,0x51,0x1b,0x98
    };
    uint8_t ramp[64];
    for (int i = 0; i < 64; i++) ramp[i] = (uint8_t)i;
    memcpy(h, IV, 32);
    fn_compress1(h, ramp, 64, 0, 11);
    CHK(memcmp(h, want_ramp64, 32) == 0);
"""

            cc = shutil.which("cc") or shutil.which("gcc") or shutil.which("clang")
            if IS_LINUX_X86 and cc:
                with open("/proc/cpuinfo", "r", encoding="utf-8") as ci:
                    has_avx = "avx" in ci.read()
                if has_avx:
                    c_src = f"""
#include <stdint.h>
#include <stdio.h>
#include <string.h>
void {syms["hl_x86"]}(uint32_t *, const uint8_t *, uint64_t, uint64_t, uint64_t);
#define fn_compress1 {syms["hl_x86"]}
#define CHK(cond) do {{ if (!(cond)) {{ fprintf(stderr, "FAIL line %d\\n", __LINE__); return 1; }} }} while (0)
int main(void) {{
{c_checks}
    puts("blake3_compress_hl_x86: OK");
    return 0;
}}
"""
                    cp, ex = os.path.join(d, "run.c"), os.path.join(d, "run")
                    with open(cp, "w", encoding="utf-8") as f:
                        f.write(c_src)
                    subprocess.run([cc, "-O1", "-o", ex, cp, objs["hl_x86"]], check=True, capture_output=True, text=True)
                    r = subprocess.run([ex], check=True, capture_output=True, text=True)
                    self.assertEqual(r.stdout.strip(), "blake3_compress_hl_x86: OK")

            elif IS_MAC_ARM64 and shutil.which("clang"):
                code = extract_text(objs["hl_arm64"])
                bp = os.path.join(d, "c1.bin")
                with open(bp, "wb") as bf:
                    bf.write(code)
                c_src = f"""
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <pthread.h>
#include <libkern/OSCacheControl.h>
typedef void (*c1_fn)(uint32_t *, const uint8_t *, uint64_t, uint64_t, uint64_t);
static void *load_jit(const char *path, size_t n) {{
    uint8_t *tmp = (uint8_t *)malloc(n);
    FILE *fp = fopen(path, "rb");
    if (!tmp || !fp || fread(tmp, 1, n, fp) != n) exit(2);
    fclose(fp);
    void *p = mmap(NULL, (n + 4095) & ~4095ULL, PROT_READ|PROT_WRITE|PROT_EXEC, MAP_PRIVATE|MAP_ANON|MAP_JIT, -1, 0);
    if (p == MAP_FAILED) exit(2);
    pthread_jit_write_protect_np(0);
    memcpy(p, tmp, n);
    pthread_jit_write_protect_np(1);
    sys_icache_invalidate(p, n);
    free(tmp);
    return p;
}}
#define CHK(cond) do {{ if (!(cond)) {{ fprintf(stderr, "FAIL line %d\\n", __LINE__); return 1; }} }} while (0)
int main(void) {{
    c1_fn fn_compress1 = (c1_fn)load_jit("{bp}", {len(code)});
{c_checks}
    puts("blake3_compress_hl_arm64: OK");
    return 0;
}}
"""
                cp, ex = os.path.join(d, "run_arm64.c"), os.path.join(d, "run_arm64")
                with open(cp, "w", encoding="utf-8") as f:
                    f.write(c_src)
                subprocess.run(["clang", "-O1", "-o", ex, cp], check=True, capture_output=True, text=True)
                r = subprocess.run([ex], check=True, capture_output=True, text=True)
                self.assertEqual(r.stdout.strip(), "blake3_compress_hl_arm64: OK")


if __name__ == "__main__":
    unittest.main()
