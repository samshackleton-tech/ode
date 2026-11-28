"""RFC 8949 Deterministic (Canonical) CBOR verification and native hardware tests.

Dual-verifies (`--verifier both`: Lean `odeverify` + standalone pure-Python `verify2.py`)
the full 5-function call graph in `proof-core/examples/cbor/cbor_canon.ode` across both
x86-64 and AArch64, confirms exact cross-arch 52-char BLAKE3-256 contract hash identity,
and executes all 5 functions natively on Linux x86-64 ELF and Apple M6 AArch64 MAP_JIT
against RFC 8949 Appendix A vectors and non-canonical encoding / truncation attacks.
"""
import os, platform, shutil, struct, subprocess, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for p in (os.path.join(ROOT, "lang"), HERE, os.path.join(ROOT, "kcheck"), os.path.join(ROOT, "arm64")):
    if p not in sys.path:
        sys.path.insert(0, p)

import ode_audit

CBOR_SRC = os.path.join(HERE, "examples", "cbor", "cbor_canon.ode")
IS_LINUX_X86 = platform.system() == "Linux" and platform.machine() in ("x86_64", "amd64")
IS_MAC_ARM64 = platform.system() == "Darwin" and platform.machine() in ("arm64", "aarch64")

FNS = [
    "cbor_head_size",
    "cbor_arg_u32",
    "cbor_str_next",
    "cbor_item_next_fn",
    "cbor_flat_count",
]


def _elf_text_and_entry(elf_path, sym_name):
    """Return `(relocated_text_bytes, entry_offset)` from an ELF64 AArch64 `.o`."""
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
    sym_vals = {}
    for sh_name, sh_type, sh_offset, sh_size, sh_link in secs:
        nm = sname(sh_name)
        if nm == ".text":
            text_bytes = b[sh_offset:sh_offset + sh_size]
        elif sh_type == 2:
            str_off = secs[sh_link][2]
            for idx, pos in enumerate(range(sh_offset, sh_offset + sh_size, 24)):
                st_name, _, _, _, st_value, _ = struct.unpack_from("<IBBHQQ", b, pos)
                sym_vals[idx] = st_value
                end = b.index(0, str_off + st_name)
                if b[str_off + st_name:end].decode("ascii", "replace") == sym_name:
                    entry_off = st_value
    buf = bytearray(text_bytes)
    for sh_name, sh_type, sh_offset, sh_size, sh_link in secs:
        if sh_type == 4 and sname(sh_name) == ".rela.text":
            for pos in range(sh_offset, sh_offset + sh_size, 24):
                r_offset, r_info, r_addend = struct.unpack_from("<QQq", b, pos)
                r_sym, r_type = r_info >> 32, r_info & 0xFFFFFFFF
                if r_type in (282, 283):  # R_AARCH64_JUMP26 / R_AARCH64_CALL26
                    target = sym_vals[r_sym] + r_addend
                    imm26 = ((target - r_offset) >> 2) & 0x03FFFFFF
                    insn = struct.unpack_from("<I", buf, r_offset)[0]
                    struct.pack_into("<I", buf, r_offset, (insn & 0xFC000000) | imm26)
    return bytes(buf), entry_off


def _c_body(call_prefix):
    p = call_prefix
    return f"""
    const uint64_t ARG_ERR = 1ULL << 32;

    /* 1. Canonical RFC 8949 integer headers across all 5 widths (1, 2, 3, 5, 9 bytes) */
    const uint8_t v_0[1]     = {{0x00}};
    const uint8_t v_23[1]    = {{0x17}};
    const uint8_t v_24[2]    = {{0x18, 0x18}};
    const uint8_t v_256[3]   = {{0x19, 0x01, 0x00}};
    const uint8_t v_65536[5] = {{0x1A, 0x00, 0x01, 0x00, 0x00}};
    const uint8_t v_2p32[9]  = {{0x1B, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00}};
    CHK({p}cbor_head_size(v_0, 1, 0) == 1);     CHK({p}cbor_arg_u32(v_0, 1, 0) == 0);
    CHK({p}cbor_head_size(v_23, 1, 0) == 1);    CHK({p}cbor_arg_u32(v_23, 1, 0) == 23);
    CHK({p}cbor_head_size(v_24, 2, 0) == 2);    CHK({p}cbor_arg_u32(v_24, 2, 0) == 24);
    CHK({p}cbor_head_size(v_256, 3, 0) == 3);   CHK({p}cbor_arg_u32(v_256, 3, 0) == 256);
    CHK({p}cbor_head_size(v_65536, 5, 0) == 5); CHK({p}cbor_arg_u32(v_65536, 5, 0) == 65536);
    CHK({p}cbor_head_size(v_2p32, 9, 0) == 9);  CHK({p}cbor_arg_u32(v_2p32, 9, 0) == ARG_ERR);

    /* 2. Non-canonical RFC 8949 §4.2.1 encodings + indefinite/reserved + truncated — ALL REJECTED */
    const uint8_t nc_1[2] = {{0x18, 0x05}};                           /* 5 encoded in 2B */
    const uint8_t nc_2[3] = {{0x19, 0x00, 0xFF}};                     /* 255 encoded in 3B */
    const uint8_t nc_4[5] = {{0x1A, 0x00, 0x00, 0xFF, 0xFF}};         /* 65535 encoded in 5B */
    const uint8_t nc_8[9] = {{0x1B, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF}};
    const uint8_t indef[2] = {{0x5F, 0xFF}};                          /* indefinite bstr */
    const uint8_t res28[1] = {{0x1C}};                                /* reserved ai=28 */
    CHK({p}cbor_head_size(nc_1, 2, 0) == 0);   CHK({p}cbor_arg_u32(nc_1, 2, 0) == ARG_ERR);
    CHK({p}cbor_head_size(nc_2, 3, 0) == 0);   CHK({p}cbor_arg_u32(nc_2, 3, 0) == ARG_ERR);
    CHK({p}cbor_head_size(nc_4, 5, 0) == 0);   CHK({p}cbor_arg_u32(nc_4, 5, 0) == ARG_ERR);
    CHK({p}cbor_head_size(nc_8, 9, 0) == 0);
    CHK({p}cbor_head_size(indef, 2, 0) == 0);
    CHK({p}cbor_head_size(res28, 1, 0) == 0);
    CHK({p}cbor_head_size(v_256, 2, 0) == 0);  /* truncated 3B header */

    /* 3. Byte strings and text strings via verified multi-fn cbor_str_next */
    const uint8_t tstr_hi[6] = {{0x65, 'h', 'e', 'l', 'l', 'o'}};     /* major 3, len 5 */
    const uint8_t bstr_4[5]  = {{0x44, 0xDE, 0xAD, 0xBE, 0xEF}};      /* major 2, len 4 */
    CHK({p}cbor_str_next(tstr_hi, 6, 0) == 6);
    CHK({p}cbor_str_next(tstr_hi, 5, 0) == 0);                        /* truncated payload */
    CHK({p}cbor_str_next(bstr_4, 5, 0) == 5);
    CHK({p}cbor_str_next(v_23, 1, 0) == 0);                           /* wrong major type (0) */

    /* 4. End-to-end flat canonical CBOR sequence via 5-fn call graph cbor_flat_count */
    /* Sequence of 6 items:
     *   [0] uint 42 (0x18 0x2A, 2B)
     *   [1] nint -100 (0x38 0x63, 2B)
     *   [2] bstr 4B (0x44 DE AD BE EF, 5B)
     *   [3] tstr "hello" (0x65 "hello", 6B)
     *   [4] true (0xF5, 1B)
     *   [5] uint 2^32 (0x1B 00 00 00 01 00 00 00 00, 9B)
     * Total = 25 bytes, 6 items!
     */
    const uint8_t seq[25] = {{
        0x18, 0x2A,
        0x38, 0x63,
        0x44, 0xDE, 0xAD, 0xBE, 0xEF,
        0x65, 'h', 'e', 'l', 'l', 'o',
        0xF5,
        0x1B, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00
    }};
    CHK({p}cbor_flat_count(seq, 25) == 6);
    CHK({p}cbor_flat_count(seq, 0) == 0);
    CHK({p}cbor_flat_count(seq, 24) == 0xFFFFFFFFULL); /* truncated last item */

    /* Corrupt item [0] from canonical 42 (0x18 0x2A) to non-canonical 5 (0x18 0x05) -> REJECTED! */
    uint8_t bad_seq[25];
    memcpy(bad_seq, seq, 25);
    bad_seq[1] = 0x05;
    CHK({p}cbor_flat_count(bad_seq, 25) == 0xFFFFFFFFULL);
"""


class TestCborCanon(unittest.TestCase):
    def test_01_dual_verify_all_5_kernels_both_arches_and_run_native(self):
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
                        CBOR_SRC, None, out_o, out_p,
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
                    f'uint64_t {syms[("cbor_head_size", "x86_64")]}(const uint8_t *, uint64_t, uint64_t);',
                    f'uint64_t {syms[("cbor_arg_u32", "x86_64")]}(const uint8_t *, uint64_t, uint64_t);',
                    f'uint64_t {syms[("cbor_str_next", "x86_64")]}(const uint8_t *, uint64_t, uint64_t);',
                    f'uint64_t {syms[("cbor_item_next_fn", "x86_64")]}(const uint8_t *, uint64_t, uint64_t);',
                    f'uint64_t {syms[("cbor_flat_count", "x86_64")]}(const uint8_t *, uint64_t);',
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
    puts("cbor_canon_x86_64: OK");
    return 0;
}}
"""
                c_p = os.path.join(d, "run_cbor.c")
                exe_p = os.path.join(d, "run_cbor")
                with open(c_p, "w", encoding="utf-8") as f:
                    f.write(c_src)
                subprocess.run(
                    [cc, "-O1", "-o", exe_p, c_p] + [objs[(fn, "x86_64")] for fn in FNS],
                    check=True, capture_output=True, text=True,
                )
                r = subprocess.run([exe_p], check=True, capture_output=True, text=True)
                self.assertEqual(r.stdout.strip(), "cbor_canon_x86_64: OK")

            elif IS_MAC_ARM64 and shutil.which("clang"):
                bins = {}
                for fn in FNS:
                    code, entry = _elf_text_and_entry(objs[(fn, "arm64")], syms[(fn, "arm64")])
                    bp = os.path.join(d, f"{fn}.bin")
                    with open(bp, "wb") as bf:
                        bf.write(code)
                    bins[fn] = (bp, len(code), entry)
                types = {
                    "cbor_head_size": "uint64_t (*)(const uint8_t *, uint64_t, uint64_t)",
                    "cbor_arg_u32": "uint64_t (*)(const uint8_t *, uint64_t, uint64_t)",
                    "cbor_str_next": "uint64_t (*)(const uint8_t *, uint64_t, uint64_t)",
                    "cbor_item_next_fn": "uint64_t (*)(const uint8_t *, uint64_t, uint64_t)",
                    "cbor_flat_count": "uint64_t (*)(const uint8_t *, uint64_t)",
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
    puts("cbor_canon_arm64: OK");
    return 0;
}}
"""
                c_p = os.path.join(d, "run_cbor_arm64.c")
                exe_p = os.path.join(d, "run_cbor_arm64")
                with open(c_p, "w", encoding="utf-8") as f:
                    f.write(c_src)
                subprocess.run(["clang", "-O1", "-o", exe_p, c_p], check=True, capture_output=True, text=True)
                r = subprocess.run([exe_p], check=True, capture_output=True, text=True)
                self.assertEqual(r.stdout.strip(), "cbor_canon_arm64: OK")


if __name__ == "__main__":
    unittest.main()
