"""RFC 7932 Brotli Decompressor Core verification and native hardware tests.

Dual-verifies (`--verifier both`: Lean `odeverify` + standalone pure-Python `verify2.py`)
all 9 portable High-Level Ode kernels in `proof-core/examples/brotli/brotli_core.ode`
across both x86-64 and AArch64, confirms exact cross-architecture 52-char BLAKE3-256
contract hash identity, and executes the verified machine code natively against RFC 7932
test vectors (including real empty and `"hello"` Brotli streams).
"""
import os, platform, shutil, subprocess, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for p in (os.path.join(ROOT, "lang"), HERE, os.path.join(ROOT, "kcheck"), os.path.join(ROOT, "arm64")):
    if p not in sys.path:
        sys.path.insert(0, p)

import obj as aobj, ode_audit

BROTLI_SRC = os.path.join(HERE, "examples", "brotli", "brotli_core.ode")
IS_LINUX_X86 = platform.system() == "Linux" and platform.machine() in ("x86_64", "amd64")
IS_MAC_ARM64 = platform.system() == "Darwin" and platform.machine() in ("arm64", "aarch64")

FNS = [
    "brotli_wbits",
    "brotli_huffman_complete",
    "brotli_iac_split",
    "brotli_insert_len",
    "brotli_copy_len",
    "brotli_read_bits24",
    "brotli_metablock_hdr",
    "brotli_dist_short",
    "brotli_copy_block64",
]


def _c_body(call_prefix):
    """Return the C test body shared by Linux x86-64 ELF linking and macOS arm64 MAP_JIT."""
    p = call_prefix
    return f"""
    /* 1. RFC 7932 §9.1 WBITS stream header (all 256 byte values against reference formula) */
    for (uint64_t b0 = 0; b0 < 256; b0++) {{
        uint64_t want;
        if ((b0 & 1) == 0) want = 16;
        else if (((b0 >> 1) & 7) != 0) want = 17 + ((b0 >> 1) & 7);
        else {{
            uint64_t hi = (b0 >> 4) & 7;
            want = (hi == 0) ? 17 : (hi == 1) ? 0 : (8 + hi);
        }}
        CHK({p}brotli_wbits(b0) == want);
    }}
    CHK({p}brotli_wbits(0x06) == 16);  /* empty Brotli stream */
    CHK({p}brotli_wbits(0x0b) == 22);  /* "hello" Brotli stream */
    CHK({p}brotli_wbits(0x11) == 0);   /* reserved 0010001 -> invalid */
    CHK({p}brotli_wbits(0x21) == 10);  /* minimum WBITS = 10 */
    CHK({p}brotli_wbits(0x01) == 17);  /* special 0000001 -> 17 */

    /* 2. RFC 7932 §3.5 Canonical Huffman Kraft-sum validator (exact 32768) */
    uint8_t h_ok[16] = {{0}};
    h_ok[1] = 2; /* two 1-bit codes: 2 * 16384 = 32768 */
    CHK({p}brotli_huffman_complete(h_ok, 16) == 1);
    uint8_t h_mix[16] = {{0}};
    h_mix[1] = 1; h_mix[2] = 1; h_mix[3] = 2; /* 1/2 + 1/4 + 2/8 = 1 */
    CHK({p}brotli_huffman_complete(h_mix, 16) == 1);
    uint8_t h_deep[16] = {{0}};
    for (int k = 1; k <= 14; k++) h_deep[k] = 1;
    h_deep[15] = 2; /* sum 2^(15-k) for k=1..14 + 2 = 32768 */
    CHK({p}brotli_huffman_complete(h_deep, 16) == 1);
    uint8_t h_over[16] = {{0}};
    h_over[1] = 2; h_over[15] = 1; /* oversubscribed: 32769 */
    CHK({p}brotli_huffman_complete(h_over, 16) == 0);
    uint8_t h_under[16] = {{0}};
    h_under[1] = 1; h_under[2] = 1; /* incomplete: 24576 */
    CHK({p}brotli_huffman_complete(h_under, 16) == 0);

    /* 3. RFC 7932 §6 Insert-and-Copy symbol splitter (0..703 + out-of-range) */
    CHK({p}brotli_iac_split(0)   == ((1ULL << 16) | (0ULL << 8)  | 0ULL));
    CHK({p}brotli_iac_split(64)  == ((1ULL << 16) | (0ULL << 8)  | 8ULL));
    CHK({p}brotli_iac_split(128) == ((0ULL << 16) | (0ULL << 8)  | 0ULL));
    CHK({p}brotli_iac_split(320) == ((0ULL << 16) | (8ULL << 8)  | 8ULL));
    CHK({p}brotli_iac_split(703) == ((0ULL << 16) | (23ULL << 8) | 23ULL));
    CHK({p}brotli_iac_split(704) == 0xFFFFFFFFULL);

    /* 4. RFC 7932 §6 Insert length decoder (boundary and max-extra cases) */
    CHK({p}brotli_insert_len(0, 999) == 0);
    CHK({p}brotli_insert_len(5, 999) == 5);
    CHK({p}brotli_insert_len(6, 1)   == 7);
    CHK({p}brotli_insert_len(16, 63) == 193);
    CHK({p}brotli_insert_len(22, 16383) == 22593);
    CHK({p}brotli_insert_len(23, 0x1FFFFFFULL) == 22594ULL + 0xFFFFFFULL);

    /* 5. RFC 7932 §6 Copy length decoder (boundary and max-extra cases) */
    CHK({p}brotli_copy_len(0, 999) == 2);
    CHK({p}brotli_copy_len(7, 999) == 9);
    CHK({p}brotli_copy_len(8, 1)   == 11);
    CHK({p}brotli_copy_len(18, 63) == 197);
    CHK({p}brotli_copy_len(22, 1023) == 2117);
    CHK({p}brotli_copy_len(23, 0x1FFFFFFULL) == 2118ULL + 0xFFFFFFULL);

    /* 6. RFC 7932 §4 Distance ring-buffer short-code decoder (0..15 + underflow guard) */
    CHK({p}brotli_dist_short(0, 10, 20, 30, 40) == 10);
    CHK({p}brotli_dist_short(3, 10, 20, 30, 40) == 40);
    CHK({p}brotli_dist_short(4, 10, 20, 30, 40) == 9);
    CHK({p}brotli_dist_short(4, 1,  20, 30, 40) == 0);   /* d0-1 <= 0 -> invalid */
    CHK({p}brotli_dist_short(8, 3,  20, 30, 40) == 0);   /* d0-3 <= 0 -> invalid */
    CHK({p}brotli_dist_short(9, 10, 20, 30, 40) == 13);
    CHK({p}brotli_dist_short(14, 10, 2, 30, 40) == 0);   /* d1-3 <= 0 -> invalid */
    CHK({p}brotli_dist_short(15, 10, 20, 30, 40) == 23);

    /* 7. End-to-end decode of real RFC 7932 Brotli streams using verified Ode kernels */
    /* 7a. Empty Brotli stream: 0x06 (padded to 4 bytes for 24-bit window reader) */
    const uint8_t empty_stream[4] = {{0x06, 0x00, 0x00, 0x00}};
    CHK({p}brotli_wbits(empty_stream[0]) == 16);
    uint64_t b_empty = {p}brotli_read_bits24(empty_stream, 4, 1);
    uint64_t h_empty = {p}brotli_metablock_hdr(b_empty);
    CHK(((h_empty >> 32) & 7) == 3);  /* kind=3 (EOF / ISLASTEMPTY) */
    CHK(((h_empty >> 35) & 1) == 1);  /* ISLAST=1 */
    CHK(((h_empty >> 40) & 0xFF) == 2);

    /* 7b. Real uncompressed "hello" Brotli stream: 0b 02 80 68 65 6c 6c 6f 03 */
    const uint8_t hello_stream[12] = {{
        0x0b, 0x02, 0x80, 'h', 'e', 'l', 'l', 'o', 0x03, 0x00, 0x00, 0x00
    }};
    CHK({p}brotli_wbits(hello_stream[0]) == 22);       /* 4 header bits */
    uint64_t b_hdr = {p}brotli_read_bits24(hello_stream, 12, 4);
    uint64_t h_mb  = {p}brotli_metablock_hdr(b_hdr);
    uint64_t mlen  = h_mb & 0xFFFFFFFFULL;
    uint64_t tag   = (h_mb >> 32) & 7;
    uint64_t last  = (h_mb >> 35) & 1;
    uint64_t cbits = (h_mb >> 40) & 0xFF;
    CHK(mlen == 5);
    CHK(tag == 2);       /* uncompressed meta-block */
    CHK(last == 0);
    CHK(cbits == 20);    /* 4 + 20 = 24 bits = 3 bytes -> payload at offset 3 */
    uint8_t out64[64];
    memset(out64, 0xAA, sizeof(out64));
    {p}brotli_copy_block64(out64, hello_stream + 3, mlen);
    CHK(memcmp(out64, "hello", 5) == 0);
    for (int k = 5; k < 64; k++) CHK(out64[k] == 0);
    uint64_t b_eof = {p}brotli_read_bits24(hello_stream, 12, 64); /* byte 8 = 0x03 */
    uint64_t h_eof = {p}brotli_metablock_hdr(b_eof);
    CHK(((h_eof >> 32) & 7) == 3);  /* EOF */

    /* 7c. Bounds & canonical rejection checks */
    CHK({p}brotli_read_bits24(hello_stream, 3, 0) == 0xFFFFFFFFULL); /* buffer < 4 bytes */
    CHK({p}brotli_read_bits24(hello_stream, 12, 72) == 0xFFFFFFFFULL); /* byte_off 9 + 4 > 12 */
    CHK({p}brotli_metablock_hdr(0x00000002ULL) == 0); /* 5-nibble MLEN with leading zero nibble -> invalid */
"""


class TestBrotliCore(unittest.TestCase):
    def test_01_dual_verify_all_9_kernels_both_arches_and_run_native(self):
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
                        BROTLI_SRC, None, out_o, out_p,
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
                    f'uint64_t {syms[("brotli_wbits", "x86_64")]}(uint64_t);',
                    f'uint64_t {syms[("brotli_huffman_complete", "x86_64")]}(const uint8_t *, uint64_t);',
                    f'uint64_t {syms[("brotli_iac_split", "x86_64")]}(uint64_t);',
                    f'uint64_t {syms[("brotli_insert_len", "x86_64")]}(uint64_t, uint64_t);',
                    f'uint64_t {syms[("brotli_copy_len", "x86_64")]}(uint64_t, uint64_t);',
                    f'uint64_t {syms[("brotli_read_bits24", "x86_64")]}(const uint8_t *, uint64_t, uint64_t);',
                    f'uint64_t {syms[("brotli_metablock_hdr", "x86_64")]}(uint64_t);',
                    f'uint64_t {syms[("brotli_dist_short", "x86_64")]}(uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);',
                    f'void {syms[("brotli_copy_block64", "x86_64")]}(uint8_t *, const uint8_t *, uint64_t);',
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
    puts("brotli_core_x86_64: OK");
    return 0;
}}
"""
                c_p = os.path.join(d, "run_brotli.c")
                exe_p = os.path.join(d, "run_brotli")
                with open(c_p, "w", encoding="utf-8") as f:
                    f.write(c_src)
                subprocess.run(
                    [cc, "-O1", "-o", exe_p, c_p] + [objs[(fn, "x86_64")] for fn in FNS],
                    check=True, capture_output=True, text=True,
                )
                r = subprocess.run([exe_p], check=True, capture_output=True, text=True)
                self.assertEqual(r.stdout.strip(), "brotli_core_x86_64: OK")

            elif IS_MAC_ARM64 and shutil.which("clang"):
                bins = {}
                for fn in FNS:
                    words, _ = aobj.words(objs[(fn, "arm64")], syms[(fn, "arm64")])
                    code = b"".join(words)
                    bp = os.path.join(d, f"{fn}.bin")
                    with open(bp, "wb") as bf:
                        bf.write(code)
                    bins[fn] = (bp, len(code))
                load_lines = []
                types = {
                    "brotli_wbits": "uint64_t (*)(uint64_t)",
                    "brotli_huffman_complete": "uint64_t (*)(const uint8_t *, uint64_t)",
                    "brotli_iac_split": "uint64_t (*)(uint64_t)",
                    "brotli_insert_len": "uint64_t (*)(uint64_t, uint64_t)",
                    "brotli_copy_len": "uint64_t (*)(uint64_t, uint64_t)",
                    "brotli_read_bits24": "uint64_t (*)(const uint8_t *, uint64_t, uint64_t)",
                    "brotli_metablock_hdr": "uint64_t (*)(uint64_t)",
                    "brotli_dist_short": "uint64_t (*)(uint64_t, uint64_t, uint64_t, uint64_t, uint64_t)",
                    "brotli_copy_block64": "void (*)(uint8_t *, const uint8_t *, uint64_t)",
                }
                for fn in FNS:
                    bp, blen = bins[fn]
                    ty = types[fn]
                    load_lines.append(
                        f'    {ty.replace("(*)", "(*fn_" + fn + ")")} = ({ty})load_jit("{bp}", {blen});'
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
    puts("brotli_core_arm64: OK");
    return 0;
}}
"""
                c_p = os.path.join(d, "run_brotli_arm64.c")
                exe_p = os.path.join(d, "run_brotli_arm64")
                with open(c_p, "w", encoding="utf-8") as f:
                    f.write(c_src)
                subprocess.run(["clang", "-O1", "-o", exe_p, c_p], check=True, capture_output=True, text=True)
                r = subprocess.run([exe_p], check=True, capture_output=True, text=True)
                self.assertEqual(r.stdout.strip(), "brotli_core_arm64: OK")


if __name__ == "__main__":
    unittest.main()
