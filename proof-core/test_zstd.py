"""RFC 8878 Zstandard (Zstd) Core verification and native hardware tests.

Dual-verifies (`--verifier both`: Lean `odeverify` + standalone pure-Python `verify2.py`)
all 8 portable High-Level Ode kernels in `proof-core/examples/zstd/zstd_core.ode`
across both x86-64 and AArch64, confirms exact cross-architecture 52-char BLAKE3-256
contract hash identity, and executes the verified machine code natively against RFC 8878
frames and official default FSE distribution tables.
"""
import os, platform, shutil, subprocess, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for p in (os.path.join(ROOT, "lang"), HERE, os.path.join(ROOT, "kcheck"), os.path.join(ROOT, "arm64")):
    if p not in sys.path:
        sys.path.insert(0, p)

import obj as aobj, ode_audit

ZSTD_SRC = os.path.join(HERE, "examples", "zstd", "zstd_core.ode")
IS_LINUX_X86 = platform.system() == "Linux" and platform.machine() in ("x86_64", "amd64")
IS_MAC_ARM64 = platform.system() == "Darwin" and platform.machine() in ("arm64", "aarch64")

FNS = [
    "zstd_magic",
    "zstd_frame_hdr_info",
    "zstd_window_size",
    "zstd_block_hdr",
    "zstd_fse_norm_valid",
    "zstd_ll_decode",
    "zstd_ml_decode",
    "zstd_rle_block64",
]


def _c_body(call_prefix):
    p = call_prefix
    return f"""
    /* 1. RFC 8878 §3.1.1 / §3.1.2 Magic numbers */
    const uint8_t m_zstd[4] = {{0x28, 0xB5, 0x2F, 0xFD}};
    const uint8_t m_skip0[4] = {{0x50, 0x2A, 0x4D, 0x18}};
    const uint8_t m_skipF[4] = {{0x5F, 0x2A, 0x4D, 0x18}};
    const uint8_t m_bad[4] = {{0x60, 0x2A, 0x4D, 0x18}};
    CHK({p}zstd_magic(m_zstd, 4) == 1);
    CHK({p}zstd_magic(m_zstd, 3) == 0);
    CHK({p}zstd_magic(m_skip0, 4) == 2);
    CHK({p}zstd_magic(m_skipF, 4) == 2);
    CHK({p}zstd_magic(m_bad, 4) == 0);

    /* 2. RFC 8878 §3.1.1.1.1 FHD exhaustively for all 256 byte values */
    for (uint64_t fhd = 0; fhd < 256; fhd++) {{
        uint64_t want = 0;
        if (((fhd >> 3) & 1) == 0) {{
            uint64_t did_f = fhd & 3;
            uint64_t did = (did_f == 3) ? 4 : did_f;
            uint64_t cksum = (fhd >> 2) & 1;
            uint64_t ss = (fhd >> 5) & 1;
            uint64_t ff = fhd >> 6;
            uint64_t wd = 1 - ss;
            uint64_t fcs = (ff == 0) ? ss : (ff == 1) ? 2 : (ff == 2) ? 4 : 8;
            want = (1 + wd + did + fcs) + (wd << 4) + (did << 8) + (fcs << 12) + (cksum << 16);
        }}
        CHK({p}zstd_frame_hdr_info(fhd) == want);
    }}

    /* 3. RFC 8878 §3.1.1.1.2 Window_Descriptor exhaustively for all 256 values */
    for (uint64_t wd = 0; wd < 256; wd++) {{
        uint64_t exp = wd >> 3;
        uint64_t mant = wd & 7;
        uint64_t base = 1ULL << (10 + exp);
        uint64_t want = base + (base >> 3) * mant;
        CHK({p}zstd_window_size(wd) == want);
    }}
    CHK({p}zstd_window_size(0x00) == 1024ULL);
    CHK({p}zstd_window_size(0xFF) == 4123168604160ULL); /* 3.75 TiB */

    /* 4. RFC 8878 §3.1.1.2 Block headers + real Raw and RLE Zstandard frames */
    const uint8_t raw_hello[14] = {{
        0x28, 0xB5, 0x2F, 0xFD, 0x20, 0x05, 0x29, 0x00, 0x00, 'h', 'e', 'l', 'l', 'o'
    }};
    CHK({p}zstd_magic(raw_hello, 14) == 1);
    uint64_t fi = {p}zstd_frame_hdr_info(raw_hello[4]);
    CHK((fi & 0xF) == 2);              /* 1 FHD + 1 FCS */
    CHK(((fi >> 12) & 0xF) == 1);      /* FCS = 1 byte */
    CHK(raw_hello[5] == 5);
    uint64_t bh = {p}zstd_block_hdr(raw_hello + 6, 8);
    CHK((bh >> 24) == 0);              /* Raw block */
    CHK(((bh >> 20) & 1) == 1);        /* Last_Block = 1 */
    CHK((bh & 0xFFFFF) == 5);          /* Block_Size = 5 */

    const uint8_t rle_aaa[10] = {{
        0x28, 0xB5, 0x2F, 0xFD, 0x20, 0x0A, 0x53, 0x00, 0x00, 'A'
    }};
    CHK({p}zstd_magic(rle_aaa, 10) == 1);
    uint64_t bh_rle = {p}zstd_block_hdr(rle_aaa + 6, 4);
    CHK((bh_rle >> 24) == 1);          /* RLE block */
    CHK(((bh_rle >> 20) & 1) == 1);    /* Last_Block = 1 */
    CHK((bh_rle & 0xFFFFF) == 10);     /* 10 'A' bytes */
    uint8_t out64[64];
    memset(out64, 0x55, sizeof(out64));
    {p}zstd_rle_block64(out64, rle_aaa[9], bh_rle & 0xFFFFF);
    for (int k = 0; k < 10; k++) CHK(out64[k] == 'A');
    for (int k = 10; k < 64; k++) CHK(out64[k] == 0);

    const uint8_t bh_res[3] = {{0x06, 0x00, 0x00}};   /* Block_Type == 3 (Reserved) */
    const uint8_t bh_big[3] = {{0x08, 0x00, 0x10}};   /* Block_Size == 131073 > 131072 */
    const uint8_t bh_max[3] = {{0x00, 0x00, 0x10}};   /* Block_Size == 131072 (exact max) */
    CHK({p}zstd_block_hdr(bh_res, 3) == 0xFFFFFFFFULL);
    CHK({p}zstd_block_hdr(bh_big, 3) == 0xFFFFFFFFULL);
    CHK(({p}zstd_block_hdr(bh_max, 3) & 0xFFFFF) == 131072);

    /* 5. Official RFC 8878 §3.1.1.3.2.2 default FSE distribution tables (-1 encoded as 255) */
    const uint8_t ll_def[36] = {{
        4, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1,
        2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 1, 1, 1, 1, 1,
        255, 255, 255, 255
    }};
    const uint8_t ml_def[53] = {{
        1, 4, 3, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1,
        1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        255, 255, 255, 255, 255, 255, 255
    }};
    const uint8_t of_def[29] = {{
        1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1,
        1, 1, 1, 1, 1, 1, 1, 1, 255, 255, 255, 255, 255
    }};
    CHK({p}zstd_fse_norm_valid(ll_def, 36, 6) == 1);
    CHK({p}zstd_fse_norm_valid(ml_def, 53, 6) == 1);
    CHK({p}zstd_fse_norm_valid(of_def, 29, 5) == 1);
    CHK({p}zstd_fse_norm_valid(of_def, 29, 6) == 0); /* wrong acc_log */
    CHK({p}zstd_fse_norm_valid(of_def, 29, 4) == 0); /* acc_log < 5 */
    CHK({p}zstd_fse_norm_valid(of_def, 29, 10) == 0); /* acc_log > 9 */
    uint8_t bad_fse[29];
    memcpy(bad_fse, of_def, 29);
    bad_fse[0] = 2; /* sum = 33 != 32 */
    CHK({p}zstd_fse_norm_valid(bad_fse, 29, 5) == 0);

    /* 6. RFC 8878 §3.1.1.3.2.1.1 Literals & Match Length decoders */
    CHK({p}zstd_ll_decode(0, 999) == 0);
    CHK({p}zstd_ll_decode(15, 999) == 15);
    CHK({p}zstd_ll_decode(16, 1) == 17);
    CHK({p}zstd_ll_decode(25, 63) == 127);
    CHK({p}zstd_ll_decode(35, 0x1FFFFULL) == 131071);

    CHK({p}zstd_ml_decode(0, 999) == 3);
    CHK({p}zstd_ml_decode(31, 999) == 34);
    CHK({p}zstd_ml_decode(32, 1) == 36);
    CHK({p}zstd_ml_decode(43, 127) == 258);
    CHK({p}zstd_ml_decode(52, 0x1FFFFULL) == 131074);
"""


class TestZstdCore(unittest.TestCase):
    def test_01_dual_verify_all_8_kernels_both_arches_and_run_native(self):
        odeverify = os.path.join(HERE, ".lake", "build", "bin", "odeverify")
        if not os.path.isfile(odeverify):
            self.skipTest("odeverify binary not built")
        cids = {}
        objs = {}
        syms = {}
        with tempfile.TemporaryDirectory() as d:
            for fn in FNS:
                for tgt in ("x86_64", "arm64"):
                    out_o = os.path.join(d, f"{fn}_{tgt}.o")
                    out_p = os.path.join(d, f"{fn}_{tgt}.proof")
                    res = ode_audit.pack_verified(
                        ZSTD_SRC, None, out_o, out_p,
                        fn_name=fn, target=tgt, c_abi=True, verifier="both",
                    )
                    self.assertEqual(res["verdict"], "shown", (fn, tgt, res))
                    self.assertEqual(list(res["verifiers"].keys()), ["odeverify", "verify2"])
                    cids[(fn, tgt)] = res["contract_b32"]
                    objs[(fn, tgt)] = out_o
                    syms[(fn, tgt)] = res["symbol"]
            for fn in FNS:
                self.assertEqual(
                    cids[(fn, "x86_64")], cids[(fn, "arm64")],
                    f"cross-arch contract hash mismatch on {fn}",
                )

            cc = shutil.which("cc") or shutil.which("gcc") or shutil.which("clang")
            if IS_LINUX_X86 and cc:
                decls = "\n".join([
                    f'uint64_t {syms[("zstd_magic", "x86_64")]}(const uint8_t *, uint64_t);',
                    f'uint64_t {syms[("zstd_frame_hdr_info", "x86_64")]}(uint64_t);',
                    f'uint64_t {syms[("zstd_window_size", "x86_64")]}(uint64_t);',
                    f'uint64_t {syms[("zstd_block_hdr", "x86_64")]}(const uint8_t *, uint64_t);',
                    f'uint64_t {syms[("zstd_fse_norm_valid", "x86_64")]}(const uint8_t *, uint64_t, uint64_t);',
                    f'uint64_t {syms[("zstd_ll_decode", "x86_64")]}(uint64_t, uint64_t);',
                    f'uint64_t {syms[("zstd_ml_decode", "x86_64")]}(uint64_t, uint64_t);',
                    f'void {syms[("zstd_rle_block64", "x86_64")]}(uint8_t *, uint64_t, uint64_t);',
                ])
                aliases = "\n".join(
                    f'#define fn_{fn} {syms[(fn, "x86_64")]}' for fn in FNS
                )
                c_src = f"""
#include <stdint.h>
#include <stdio.h>
#include <string.h>
{decls}
{aliases}
#define CHK(cond) do {{ if (!(cond)) {{ fprintf(stderr, "FAIL line %d\\n", __LINE__); return 1; }} }} while (0)
int main(void) {{
{_c_body("fn_")}
    puts("zstd_core_x86_64: OK");
    return 0;
}}
"""
                c_p = os.path.join(d, "run_zstd.c")
                exe_p = os.path.join(d, "run_zstd")
                with open(c_p, "w", encoding="utf-8") as f:
                    f.write(c_src)
                subprocess.run(
                    [cc, "-O1", "-o", exe_p, c_p] + [objs[(fn, "x86_64")] for fn in FNS],
                    check=True, capture_output=True, text=True,
                )
                r = subprocess.run([exe_p], check=True, capture_output=True, text=True)
                self.assertEqual(r.stdout.strip(), "zstd_core_x86_64: OK")

            elif IS_MAC_ARM64 and shutil.which("clang"):
                bins = {}
                for fn in FNS:
                    words, _ = aobj.words(objs[(fn, "arm64")], syms[(fn, "arm64")])
                    code = b"".join(words)
                    bp = os.path.join(d, f"{fn}.bin")
                    with open(bp, "wb") as bf:
                        bf.write(code)
                    bins[fn] = (bp, len(code))
                types = {
                    "zstd_magic": "uint64_t (*)(const uint8_t *, uint64_t)",
                    "zstd_frame_hdr_info": "uint64_t (*)(uint64_t)",
                    "zstd_window_size": "uint64_t (*)(uint64_t)",
                    "zstd_block_hdr": "uint64_t (*)(const uint8_t *, uint64_t)",
                    "zstd_fse_norm_valid": "uint64_t (*)(const uint8_t *, uint64_t, uint64_t)",
                    "zstd_ll_decode": "uint64_t (*)(uint64_t, uint64_t)",
                    "zstd_ml_decode": "uint64_t (*)(uint64_t, uint64_t)",
                    "zstd_rle_block64": "void (*)(uint8_t *, uint64_t, uint64_t)",
                }
                loads = "\n".join(
                    f'    {types[fn].replace("(*)", "(*fn_" + fn + ")")} = ({types[fn]})load_jit("{bins[fn][0]}", {bins[fn][1]});'
                    for fn in FNS
                )
                c_src = f"""
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <pthread.h>
#include <libkern/OSCacheControl.h>
static void *load_jit(const char *path, size_t n) {{
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
    return p;
}}
#define CHK(cond) do {{ if (!(cond)) {{ fprintf(stderr, "FAIL line %d\\n", __LINE__); return 1; }} }} while (0)
int main(void) {{
{loads}
{_c_body("fn_")}
    puts("zstd_core_arm64: OK");
    return 0;
}}
"""
                c_p = os.path.join(d, "run_zstd_arm64.c")
                exe_p = os.path.join(d, "run_zstd_arm64")
                with open(c_p, "w", encoding="utf-8") as f:
                    f.write(c_src)
                subprocess.run(["clang", "-O1", "-o", exe_p, c_p], check=True, capture_output=True, text=True)
                r = subprocess.run([exe_p], check=True, capture_output=True, text=True)
                self.assertEqual(r.stdout.strip(), "zstd_core_arm64: OK")


if __name__ == "__main__":
    unittest.main()
