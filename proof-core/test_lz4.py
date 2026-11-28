#!/usr/bin/env pypy3
"""Dual-verification (`--verifier both`) and native execution tests for LZ4 Block Format
and LZ4 Frame Format v1.6.4 core (`examples/lz4/lz4_core.ode`) on x86-64 and AArch64."""
import os, platform, re, shutil, struct, subprocess, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
ODE_TOOL = os.path.join(ROOT, "lang", "ode_tool.py")
SRC = os.path.join(HERE, "examples", "lz4", "lz4_core.ode")

IS_LINUX_X86 = (platform.system() == "Linux" and platform.machine() in ("x86_64", "AMD64"))
IS_MAC_ARM64 = (platform.system() == "Darwin" and platform.machine() == "arm64")


def reloc_arm64_text(elf_path, sym_name):
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


@unittest.skipUnless(shutil.which("lake"), "Lean's `lake` is not installed here")
class TestLZ4Core(unittest.TestCase):
    def test_lz4_core_dual_verify_and_native(self):
        portable = [
            "lz4_ext_len_end",
            "lz4_ext_len_val",
            "lz4_match_step",
            "lz4_seq_step",
            "lz4_block_decoded_size",
            "lz4_frame_magic",
            "lz4_frame_hdr_len",
        ]
        all_fns = portable + ["lz4_copy_lit64"]
        root_fns = ["lz4_block_decoded_size", "lz4_frame_magic", "lz4_frame_hdr_len", "lz4_copy_lit64"]

        with tempfile.TemporaryDirectory() as d:
            cids, syms, objs = {}, {}, {}
            for fn in all_fns:
                for tgt in ("x86_64", "arm64"):
                    obj_p = os.path.join(d, f"{fn}_{tgt}.o")
                    prf_p = os.path.join(d, f"{fn}_{tgt}.proof")
                    res = subprocess.run(
                        [sys.executable, ODE_TOOL, "pack", SRC, "--fn", fn, "--target", tgt,
                         "--c-abi", "--verifier", "both", "--out", obj_p, "--proof", prf_p],
                        capture_output=True, text=True,
                    )
                    self.assertEqual(res.returncode, 0, f"LZ4 pack failed ({fn}, {tgt}):\n{res.stdout}\n{res.stderr}")
                    self.assertIn("VERDICT:           shown", res.stdout)
                    self.assertIn("odeverify (shown), verify2 (shown)", res.stdout)
                    m = re.search(r"SYMBOL:\s+(ode_[a-z2-7]{52})", res.stdout)
                    self.assertIsNotNone(m, res.stdout)
                    syms[(fn, tgt)] = m.group(1)
                    cids[(fn, tgt)] = m.group(1)[4:]
                    objs[(fn, tgt)] = obj_p
            for fn in portable:
                self.assertEqual(cids[(fn, "x86_64")], cids[(fn, "arm64")], f"cross-arch hash mismatch: {fn}")

            def c_body(p, run_simd):
                simd_block = ""
                if run_simd:
                    simd_block = f"""
    _Alignas(64) uint8_t src64[64], dst64[64];
    for (int i = 0; i < 64; i++) {{ src64[i] = (uint8_t)(i * 3 + 11); dst64[i] = 0; }}
    {p}lz4_copy_lit64(dst64, src64);
    CHK(memcmp(dst64, src64, 64) == 0);
"""
                return f"""
    const uint64_t ERR = 4294967295ULL;
    /* 1. Empty block -> 0 bytes */
    const uint8_t empty[1] = {{0}};
    CHK({p}lz4_block_decoded_size(empty, 0) == 0);
    /* 2. Literals-only block: "hello" (token=0x50, 5 literals) */
    const uint8_t lit_hello[] = {{ 0x50, 'h', 'e', 'l', 'l', 'o' }};
    CHK({p}lz4_block_decoded_size(lit_hello, sizeof(lit_hello)) == 5);
    /* 3. RLE block: 1 literal 'A' + match offset=1 len=19 (token=0x1F, 'A', off=1,0, ext=0 -> 1 + 19 = 20)
          followed by 5 final literals (token=0x50, "world") -> total 25 bytes */
    const uint8_t rle_blk[] = {{ 0x1F, 'A', 0x01, 0x00, 0x00, 0x50, 'w', 'o', 'r', 'l', 'd' }};
    CHK({p}lz4_block_decoded_size(rle_blk, sizeof(rle_blk)) == 25);
    /* 4. Multi-byte extended literal length: 270 literals (token=0xF0, 0xFF, 0x00, 270 bytes) */
    uint8_t ext_lit[273];
    ext_lit[0] = 0xF0; ext_lit[1] = 0xFF; ext_lit[2] = 0x00;
    for (int i = 0; i < 270; i++) ext_lit[3 + i] = (uint8_t)(i & 0xFF);
    CHK({p}lz4_block_decoded_size(ext_lit, sizeof(ext_lit)) == 270);
    /* 5. Adversarial zero-offset attack: offset == 0 must be refused */
    const uint8_t bad_zero_off[] = {{ 0x10, 'A', 0x00, 0x00, 0x10, 'B' }};
    CHK({p}lz4_block_decoded_size(bad_zero_off, sizeof(bad_zero_off)) == ERR);
    /* 6. Adversarial lookbehind-underflow attack: offset=2 when only 1 byte decoded */
    const uint8_t bad_underflow[] = {{ 0x10, 'A', 0x02, 0x00, 0x10, 'B' }};
    CHK({p}lz4_block_decoded_size(bad_underflow, sizeof(bad_underflow)) == ERR);
    /* 7. Truncated extended length (ends in 0xFF) must be refused */
    const uint8_t bad_trunc_ext[] = {{ 0xF0, 0xFF }};
    CHK({p}lz4_block_decoded_size(bad_trunc_ext, sizeof(bad_trunc_ext)) == ERR);
    /* 8. Truncated literals must be refused */
    const uint8_t bad_trunc_lit[] = {{ 0x50, 'h', 'e' }};
    CHK({p}lz4_block_decoded_size(bad_trunc_lit, sizeof(bad_trunc_lit)) == ERR);
    /* 9. LZ4 Frame Format v1.6.4 magic & header length */
    const uint8_t hdr_min[7] = {{ 0x04, 0x22, 0x4D, 0x18, 0x64, 0x40, 0xA7 }};
    CHK({p}lz4_frame_magic(hdr_min, sizeof(hdr_min)) == 1);
    CHK({p}lz4_frame_hdr_len(hdr_min, sizeof(hdr_min)) == 7);
    const uint8_t hdr_csize_dict[19] = {{ 0x04, 0x22, 0x4D, 0x18, 0x6D, 0x70, 0 }};
    CHK({p}lz4_frame_hdr_len(hdr_csize_dict, sizeof(hdr_csize_dict)) == 19);
    CHK({p}lz4_frame_hdr_len(hdr_csize_dict, 18) == 0);
    const uint8_t hdr_skip[4] = {{ 0x50, 0x2A, 0x4D, 0x18 }};
    CHK({p}lz4_frame_magic(hdr_skip, sizeof(hdr_skip)) == 2);
    CHK({p}lz4_frame_hdr_len(hdr_skip, sizeof(hdr_skip)) == 0);
    const uint8_t hdr_bad_ver[7] = {{ 0x04, 0x22, 0x4D, 0x18, 0x80, 0x40, 0x00 }};
    CHK({p}lz4_frame_hdr_len(hdr_bad_ver, sizeof(hdr_bad_ver)) == 0);
    {simd_block}
"""

            cc = shutil.which("cc") or shutil.which("gcc") or shutil.which("clang")
            if IS_LINUX_X86 and cc:
                with open("/proc/cpuinfo", "r", encoding="utf-8") as ci:
                    has_avx512 = "avx512f" in ci.read()
                run_roots = root_fns if has_avx512 else root_fns[:-1]
                decls = "\n".join([
                    f'uint64_t {syms[("lz4_block_decoded_size", "x86_64")]}(const uint8_t *, uint64_t);',
                    f'uint64_t {syms[("lz4_frame_magic", "x86_64")]}(const uint8_t *, uint64_t);',
                    f'uint64_t {syms[("lz4_frame_hdr_len", "x86_64")]}(const uint8_t *, uint64_t);',
                ] + ([
                    f'void {syms[("lz4_copy_lit64", "x86_64")]}(uint8_t *, const uint8_t *);',
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
{c_body("fn_", has_avx512)}
    puts("lz4_x86: OK");
    return 0;
}}
"""
                c_p, exe_p = os.path.join(d, "run_lz4.c"), os.path.join(d, "run_lz4")
                with open(c_p, "w", encoding="utf-8") as f:
                    f.write(c_src)
                subprocess.run([cc, "-O1", "-o", exe_p, c_p] + [objs[(fn, "x86_64")] for fn in run_roots],
                               check=True, capture_output=True, text=True)
                r = subprocess.run([exe_p], check=True, capture_output=True, text=True)
                self.assertEqual(r.stdout.strip(), "lz4_x86: OK")

            elif IS_MAC_ARM64 and shutil.which("clang"):
                types = {
                    "lz4_block_decoded_size": "uint64_t (*)(const uint8_t *, uint64_t)",
                    "lz4_frame_magic": "uint64_t (*)(const uint8_t *, uint64_t)",
                    "lz4_frame_hdr_len": "uint64_t (*)(const uint8_t *, uint64_t)",
                    "lz4_copy_lit64": "void (*)(uint8_t *, const uint8_t *)",
                }
                load_lines = []
                for fn in root_fns:
                    code, entry = reloc_arm64_text(objs[(fn, "arm64")], syms[(fn, "arm64")])
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
{c_body("fn_", True)}
    puts("lz4_arm64: OK");
    return 0;
}}
"""
                c_p, exe_p = os.path.join(d, "run_lz4_arm64.c"), os.path.join(d, "run_lz4_arm64")
                with open(c_p, "w", encoding="utf-8") as f:
                    f.write(c_src)
                subprocess.run(["clang", "-O1", "-o", exe_p, c_p], check=True, capture_output=True, text=True)
                r = subprocess.run([exe_p], check=True, capture_output=True, text=True)
                self.assertEqual(r.stdout.strip(), "lz4_arm64: OK")


if __name__ == "__main__":
    unittest.main()
