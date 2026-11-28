"""QOI Image, BIP 173/350 Bech32/Bech32m, and bzip2 (`mibz2`) Codec verification & native tests.

Dual-verifies (`--verifier both`: Lean `odeverify` + standalone pure-Python `verify2.py`)
all 8 portable High-Level Ode kernels in `proof-core/examples/codecs/qoi_bech32_bz2.ode`
across both x86-64 and AArch64, confirms exact cross-arch 52-char BLAKE3-256 contract
hash identity, and executes all 8 natively on Linux x86-64 ELF and Apple M6 AArch64 MAP_JIT.
"""
import os, platform, shutil, struct, subprocess, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for p in (os.path.join(ROOT, "lang"), HERE, os.path.join(ROOT, "kcheck"), os.path.join(ROOT, "arm64")):
    if p not in sys.path:
        sys.path.insert(0, p)

import ode_audit

CODECS_SRC = os.path.join(HERE, "examples", "codecs", "qoi_bech32_bz2.ode")
IS_LINUX_X86 = platform.system() == "Linux" and platform.machine() in ("x86_64", "amd64")
IS_MAC_ARM64 = platform.system() == "Darwin" and platform.machine() in ("arm64", "aarch64")

FNS = [
    "qoi_header_valid",
    "qoi_color_hash",
    "qoi_op_next",
    "bech32_hrp_valid",
    "bech32_char_val",
    "bz2_stream_hdr",
    "bz2_block_magic",
    "bz2_rle1_decoded_len",
]


def _elf_text_and_entry(elf_path, sym_name):
    with open(elf_path, "rb") as f:
        b = f.read()
    e_shoff = struct.unpack_from("<Q", b, 40)[0]
    e_shentsize, e_shnum, e_shstrndx = struct.unpack_from("<HHH", b, 58)
    secs = []
    for i in range(e_shnum):
        off = e_shoff + i * e_shentsize
        sh_name, sh_type, _, _, sh_offset, sh_size, sh_link = struct.unpack_from("<IIQQQQI", b, off)
        secs.append((sh_name, sh_type, sh_offset, sh_size, sh_link))
    shstr_off = secs[e_shstrndx][2]

    def sname(idx):
        end = b.index(0, shstr_off + idx)
        return b[shstr_off + idx:end].decode("ascii", "replace")

    text_bytes = b""
    entry_off = 0
    for sh_name, sh_type, sh_offset, sh_size, sh_link in secs:
        nm = sname(sh_name)
        if nm == ".text":
            text_bytes = b[sh_offset:sh_offset + sh_size]
        elif sh_type == 2:
            str_off = secs[sh_link][2]
            for pos in range(sh_offset, sh_offset + sh_size, 24):
                st_name, _, _, _, st_value, _ = struct.unpack_from("<IBBHQQ", b, pos)
                end = b.index(0, str_off + st_name)
                if b[str_off + st_name:end].decode("ascii", "replace") == sym_name:
                    entry_off = st_value
    return text_bytes, entry_off


def _c_body(call_prefix):
    p = call_prefix
    return f"""
    /* 1. QOI header, color hash (constant-time), and chunk op-tag stepper */
    const uint8_t qoi_hdr[14] = {{
        'q', 'o', 'i', 'f',  0, 0, 0x01, 0x40,  0, 0, 0x00, 0xF0,  4, 0
    }}; /* 320x240 RGBA sRGB */
    uint64_t qh = {p}qoi_header_valid(qoi_hdr, 14);
    CHK((qh >> 32) == 4 && (qh & 0xFFFFFFFFULL) == 320);
    CHK({p}qoi_header_valid(qoi_hdr, 13) == 0);
    uint8_t qoi_bad[14];
    memcpy(qoi_bad, qoi_hdr, 14); qoi_bad[12] = 5; /* invalid channels */
    CHK({p}qoi_header_valid(qoi_bad, 14) == 0);
    CHK({p}qoi_color_hash(0, 0, 0, 255) == (255 * 11) % 64);
    CHK({p}qoi_color_hash(12, 34, 56, 78) == (12*3 + 34*5 + 56*7 + 78*11) % 64);
    /* QOI chunk stream: RGB(4B) + LUMA(2B) + RGBA(5B) + DIFF(1B) + RUN(1B) = 13B */
    const uint8_t qops[13] = {{0xFE, 1, 2, 3,  0x80, 0x12,  0xFF, 4, 5, 6, 7,  0x40,  0xC0}};
    CHK({p}qoi_op_next(qops, 13, 0) == 4);
    CHK({p}qoi_op_next(qops, 13, 4) == 6);
    CHK({p}qoi_op_next(qops, 13, 6) == 11);
    CHK({p}qoi_op_next(qops, 13, 11) == 12);
    CHK({p}qoi_op_next(qops, 13, 12) == 13);
    CHK({p}qoi_op_next(qops, 10, 6) == 0); /* truncated RGBA */

    /* 2. BIP 173 / BIP 350 Bech32/Bech32m HRP & alphabet */
    CHK({p}bech32_hrp_valid((const uint8_t *)"bc", 2) == 1);
    CHK({p}bech32_hrp_valid((const uint8_t *)"BC", 2) == 1);
    CHK({p}bech32_hrp_valid((const uint8_t *)"tb1", 3) == 1);
    CHK({p}bech32_hrp_valid((const uint8_t *)"Bc", 2) == 0);       /* mixed case rejected */
    CHK({p}bech32_hrp_valid((const uint8_t *)"", 0) == 0);         /* empty rejected */
    CHK({p}bech32_hrp_valid((const uint8_t *)"a b", 3) == 0);      /* space (32 < 33) rejected */
    const char *charset = "qpzry9x8gf2tvdw0s3jn54khce6mua7l";
    for (uint64_t k = 0; k < 32; k++) {{
        uint8_t ch = (uint8_t)charset[k];
        CHK({p}bech32_char_val(ch) == k);
        if (ch >= 'a' && ch <= 'z') CHK({p}bech32_char_val(ch - 32) == k);
    }}
    CHK({p}bech32_char_val('1') == 32); /* excluded from Bech32 alphabet */
    CHK({p}bech32_char_val('b') == 32);
    CHK({p}bech32_char_val('i') == 32);
    CHK({p}bech32_char_val('o') == 32);

    /* 3. bzip2 (`mibz2`) stream header, pi/sqrt(pi) block magics, and RLE1 exact expanded length */
    CHK({p}bz2_stream_hdr((const uint8_t *)"BZh9", 4) == 9);
    CHK({p}bz2_stream_hdr((const uint8_t *)"BZh1", 4) == 1);
    CHK({p}bz2_stream_hdr((const uint8_t *)"BZh0", 4) == 0);
    CHK({p}bz2_stream_hdr((const uint8_t *)"BZh", 3) == 0);
    const uint8_t bz_blk[6] = {{0x31, 0x41, 0x59, 0x26, 0x53, 0x59}};
    const uint8_t bz_eos[6] = {{0x17, 0x72, 0x45, 0x38, 0x50, 0x90}};
    const uint8_t bz_bad[6] = {{0x31, 0x41, 0x59, 0x26, 0x53, 0x58}};
    CHK({p}bz2_block_magic(bz_blk, 6) == 1);
    CHK({p}bz2_block_magic(bz_eos, 6) == 2);
    CHK({p}bz2_block_magic(bz_bad, 6) == 0);
    /* RLE1: "AAAA\x05B" -> 4 + 5 + 1 = 10 bytes; "AAAA\x00AAAA\x02" -> 4 + 0 + 4 + 2 = 10 bytes */
    const uint8_t rle_ok1[6] = {{'A', 'A', 'A', 'A', 5, 'B'}};
    const uint8_t rle_ok2[10] = {{'A', 'A', 'A', 'A', 0, 'A', 'A', 'A', 'A', 2}};
    const uint8_t rle_trunc[4] = {{'A', 'A', 'A', 'A'}}; /* missing repeat count byte */
    CHK({p}bz2_rle1_decoded_len(rle_ok1, 6) == 10);
    CHK({p}bz2_rle1_decoded_len(rle_ok2, 10) == 10);
    CHK({p}bz2_rle1_decoded_len(rle_trunc, 4) == 0xFFFFFFFFULL);
"""


class TestCodecs(unittest.TestCase):
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
                        CODECS_SRC, None, out_o, out_p,
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
                    f'uint64_t {syms[("qoi_header_valid", "x86_64")]}(const uint8_t *, uint64_t);',
                    f'uint64_t {syms[("qoi_color_hash", "x86_64")]}(uint64_t, uint64_t, uint64_t, uint64_t);',
                    f'uint64_t {syms[("qoi_op_next", "x86_64")]}(const uint8_t *, uint64_t, uint64_t);',
                    f'uint64_t {syms[("bech32_hrp_valid", "x86_64")]}(const uint8_t *, uint64_t);',
                    f'uint64_t {syms[("bech32_char_val", "x86_64")]}(uint64_t);',
                    f'uint64_t {syms[("bz2_stream_hdr", "x86_64")]}(const uint8_t *, uint64_t);',
                    f'uint64_t {syms[("bz2_block_magic", "x86_64")]}(const uint8_t *, uint64_t);',
                    f'uint64_t {syms[("bz2_rle1_decoded_len", "x86_64")]}(const uint8_t *, uint64_t);',
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
    puts("codecs_x86_64: OK");
    return 0;
}}
"""
                c_p = os.path.join(d, "run_codecs.c")
                exe_p = os.path.join(d, "run_codecs")
                with open(c_p, "w", encoding="utf-8") as f:
                    f.write(c_src)
                subprocess.run(
                    [cc, "-O1", "-o", exe_p, c_p] + [objs[(fn, "x86_64")] for fn in FNS],
                    check=True, capture_output=True, text=True,
                )
                r = subprocess.run([exe_p], check=True, capture_output=True, text=True)
                self.assertEqual(r.stdout.strip(), "codecs_x86_64: OK")

            elif IS_MAC_ARM64 and shutil.which("clang"):
                bins = {}
                for fn in FNS:
                    code, entry = _elf_text_and_entry(objs[(fn, "arm64")], syms[(fn, "arm64")])
                    bp = os.path.join(d, f"{fn}.bin")
                    with open(bp, "wb") as bf:
                        bf.write(code)
                    bins[fn] = (bp, len(code), entry)
                types = {
                    "qoi_header_valid": "uint64_t (*)(const uint8_t *, uint64_t)",
                    "qoi_color_hash": "uint64_t (*)(uint64_t, uint64_t, uint64_t, uint64_t)",
                    "qoi_op_next": "uint64_t (*)(const uint8_t *, uint64_t, uint64_t)",
                    "bech32_hrp_valid": "uint64_t (*)(const uint8_t *, uint64_t)",
                    "bech32_char_val": "uint64_t (*)(uint64_t)",
                    "bz2_stream_hdr": "uint64_t (*)(const uint8_t *, uint64_t)",
                    "bz2_block_magic": "uint64_t (*)(const uint8_t *, uint64_t)",
                    "bz2_rle1_decoded_len": "uint64_t (*)(const uint8_t *, uint64_t)",
                }
                loads = "\n".join(
                    f'    {types[fn].replace("(*)", "(*fn_" + fn + ")")} = ({types[fn]})load_jit("{bins[fn][0]}", {bins[fn][1]}, {bins[fn][2]});'
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
{_c_body("fn_")}
    puts("codecs_arm64: OK");
    return 0;
}}
"""
                c_p = os.path.join(d, "run_codecs_arm64.c")
                exe_p = os.path.join(d, "run_codecs_arm64")
                with open(c_p, "w", encoding="utf-8") as f:
                    f.write(c_src)
                subprocess.run(["clang", "-O1", "-o", exe_p, c_p], check=True, capture_output=True, text=True)
                r = subprocess.run([exe_p], check=True, capture_output=True, text=True)
                self.assertEqual(r.stdout.strip(), "codecs_arm64: OK")


if __name__ == "__main__":
    unittest.main()
