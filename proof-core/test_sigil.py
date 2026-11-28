#!/usr/bin/env pypy3
"""Dual-verification (`--verifier both`) and native execution tests for Sigil 0.1
byte-to-glyph codec core (`examples/sigil/sigil_core.ode`) on x86-64 and AArch64."""
import os, platform, re, shutil, struct, subprocess, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
ODE_TOOL = os.path.join(ROOT, "lang", "ode_tool.py")
SRC = os.path.join(HERE, "examples", "sigil", "sigil_core.ode")

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
class TestSigilCore(unittest.TestCase):
    def test_sigil_core_dual_verify_and_native(self):
        fns = [
            "sigil_letters",
            "sigil_check_prime",
            "sigil_marked4",
            "sigil_encode4_word",
            "sigil_digit5",
            "sigil_verify4_decode",
            "sigil_mul_k32_limb",
            "sigil_utf8_pack3",
            "sigil_utf8_decode3",
        ]

        with tempfile.TemporaryDirectory() as d:
            cids, syms, objs = {}, {}, {}
            for fn in fns:
                for tgt in ("x86_64", "arm64"):
                    obj_p = os.path.join(d, f"{fn}_{tgt}.o")
                    prf_p = os.path.join(d, f"{fn}_{tgt}.proof")
                    res = subprocess.run(
                        [sys.executable, ODE_TOOL, "pack", SRC, "--fn", fn, "--target", tgt,
                         "--c-abi", "--verifier", "both", "--out", obj_p, "--proof", prf_p],
                        capture_output=True, text=True,
                    )
                    self.assertEqual(res.returncode, 0, f"Sigil pack failed ({fn}, {tgt}):\n{res.stdout}\n{res.stderr}")
                    self.assertIn("VERDICT:           shown", res.stdout)
                    self.assertIn("odeverify (shown), verify2 (shown)", res.stdout)
                    m = re.search(r"SYMBOL:\s+(ode_[a-z2-7]{52})", res.stdout)
                    self.assertIsNotNone(m, res.stdout)
                    syms[(fn, tgt)] = m.group(1)
                    cids[(fn, tgt)] = m.group(1)[4:]
                    objs[(fn, tgt)] = obj_p
                self.assertEqual(cids[(fn, "x86_64")], cids[(fn, "arm64")], f"cross-arch hash mismatch: {fn}")

            def c_body(p):
                return f"""
    /* 1. Sigil 0.1 letter counts & check primes for L = 1..64 */
    static const uint64_t PRIMES[11] = {{
        4093, 8179, 16381, 32749, 65519, 131063, 262133, 524269, 1048433, 2096881, 4193633
    }};
    CHK({p}sigil_letters(32) == 25);
    CHK({p}sigil_check_prime(32) == 131063);
    CHK({p}sigil_letters(16) == 13);
    CHK({p}sigil_check_prime(16) == 8179);
    CHK({p}sigil_letters(4) == 5);
    CHK({p}sigil_check_prime(4) == 2096881);
    for (uint64_t L = 1; L <= 64; L++) {{
        uint64_t want_n = (8 * L + 24) / 11;
        uint64_t idx = 11 * want_n - 8 * L - 14;
        CHK({p}sigil_letters(L) == want_n);
        CHK({p}sigil_check_prime(L) == PRIMES[idx]);
    }}
    /* 2. 4-byte Sigil marker + check-prime encoding, base-2048 unpacking, and round-trip verify */
    const uint8_t b0[4] = {{ 0x00, 0x00, 0x00, 0x00 }};
    uint64_t w0 = {p}sigil_encode4_word(b0, 4);
    CHK(w0 == (1ULL << 16) * 2096881ULL);
    CHK({p}sigil_verify4_decode(w0, 0x00000000ULL) == 1);
    CHK({p}sigil_verify4_decode(w0 ^ 1ULL, 0x00000000ULL) == 0);
    const uint8_t b1[4] = {{ 0xDE, 0xAD, 0xBE, 0xEF }};
    uint64_t m1 = {p}sigil_marked4(0xDEADBEEFULL);
    CHK(m1 == (((0xDEADULL << 2) + 1ULL) << 16) + 0xBEEFULL);
    uint64_t w1 = {p}sigil_encode4_word(b1, 4);
    CHK(w1 == m1 * 2096881ULL);
    CHK({p}sigil_verify4_decode(w1, 0xDEADBEEFULL) == 1);
    CHK({p}sigil_verify4_decode(w1, 0xDEADBEEEULL) == 0);
    /* Reassemble w1 from its 5 base-2048 digits */
    uint64_t re = 0;
    for (uint64_t k = 0; k < 5; k++) {{
        uint64_t dig = {p}sigil_digit5(w1, k);
        CHK(dig < 2048);
        re = (re << 11) | dig;
    }}
    CHK(re == w1);
    /* 3. 32-byte Sigil multi-limb multiply-add step (K = 131063) */
    CHK({p}sigil_mul_k32_limb(0xFFFFFFFFULL, 131062ULL) == 0xFFFFFFFFULL * 131063ULL + 131062ULL);
    CHK({p}sigil_mul_k32_limb(0x12345678ULL, 1234ULL) == 0x12345678ULL * 131063ULL + 1234ULL);
    /* 4. 3-byte BMP UTF-8 pack & strict decode round-trip on Sigil alphabet bounds + rejections */
    const uint64_t cps[] = {{ 0x0800, 0x0904, 0x1200, 0x2D30, 0xA500, 0xAA4B, 0xD7FF, 0xE000, 0xFFFF }};
    for (size_t i = 0; i < sizeof(cps) / sizeof(cps[0]); i++) {{
        uint64_t cp = cps[i];
        uint64_t pk = {p}sigil_utf8_pack3(cp);
        uint64_t u0 = pk & 0xFF, u1 = (pk >> 8) & 0xFF, u2 = (pk >> 16) & 0xFF;
        CHK({p}sigil_utf8_decode3(u0, u1, u2) == cp);
    }}
    /* Reject overlong U+07FF (E0 9F BF) and UTF-16 surrogate U+D800 (ED A0 80) */
    CHK({p}sigil_utf8_decode3(0xE0, 0x9F, 0xBF) == 0);
    CHK({p}sigil_utf8_decode3(0xED, 0xA0, 0x80) == 0);
    CHK({p}sigil_utf8_decode3(0xED, 0xBF, 0xBF) == 0);
    CHK({p}sigil_utf8_decode3(0xE1, 0x40, 0x80) == 0);
"""

            cc = shutil.which("cc") or shutil.which("gcc") or shutil.which("clang")
            if IS_LINUX_X86 and cc:
                decls = "\n".join([
                    f'uint64_t {syms[("sigil_letters", "x86_64")]}(uint64_t);',
                    f'uint64_t {syms[("sigil_check_prime", "x86_64")]}(uint64_t);',
                    f'uint64_t {syms[("sigil_marked4", "x86_64")]}(uint64_t);',
                    f'uint64_t {syms[("sigil_encode4_word", "x86_64")]}(const uint8_t *, uint64_t);',
                    f'uint64_t {syms[("sigil_digit5", "x86_64")]}(uint64_t, uint64_t);',
                    f'uint64_t {syms[("sigil_verify4_decode", "x86_64")]}(uint64_t, uint64_t);',
                    f'uint64_t {syms[("sigil_mul_k32_limb", "x86_64")]}(uint64_t, uint64_t);',
                    f'uint64_t {syms[("sigil_utf8_pack3", "x86_64")]}(uint64_t);',
                    f'uint64_t {syms[("sigil_utf8_decode3", "x86_64")]}(uint64_t, uint64_t, uint64_t);',
                ])
                aliases = "\n".join(f'#define fn_{fn} {syms[(fn, "x86_64")]}' for fn in fns)
                c_src = f"""
#include <stdint.h>
#include <stdio.h>
{decls}
{aliases}
#define CHK(cond) do {{ if (!(cond)) {{ fprintf(stderr, "FAIL line %d\\n", __LINE__); return 1; }} }} while (0)
int main(void) {{
{c_body("fn_")}
    puts("sigil_x86: OK");
    return 0;
}}
"""
                c_p, exe_p = os.path.join(d, "run_sigil.c"), os.path.join(d, "run_sigil")
                with open(c_p, "w", encoding="utf-8") as f:
                    f.write(c_src)
                subprocess.run([cc, "-O1", "-o", exe_p, c_p] + [objs[(fn, "x86_64")] for fn in fns],
                               check=True, capture_output=True, text=True)
                r = subprocess.run([exe_p], check=True, capture_output=True, text=True)
                self.assertEqual(r.stdout.strip(), "sigil_x86: OK")

            elif IS_MAC_ARM64 and shutil.which("clang"):
                types = {
                    "sigil_letters": "uint64_t (*)(uint64_t)",
                    "sigil_check_prime": "uint64_t (*)(uint64_t)",
                    "sigil_marked4": "uint64_t (*)(uint64_t)",
                    "sigil_encode4_word": "uint64_t (*)(const uint8_t *, uint64_t)",
                    "sigil_digit5": "uint64_t (*)(uint64_t, uint64_t)",
                    "sigil_verify4_decode": "uint64_t (*)(uint64_t, uint64_t)",
                    "sigil_mul_k32_limb": "uint64_t (*)(uint64_t, uint64_t)",
                    "sigil_utf8_pack3": "uint64_t (*)(uint64_t)",
                    "sigil_utf8_decode3": "uint64_t (*)(uint64_t, uint64_t, uint64_t)",
                }
                load_lines = []
                for fn in fns:
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
{c_body("fn_")}
    puts("sigil_arm64: OK");
    return 0;
}}
"""
                c_p, exe_p = os.path.join(d, "run_sigil_arm64.c"), os.path.join(d, "run_sigil_arm64")
                with open(c_p, "w", encoding="utf-8") as f:
                    f.write(c_src)
                subprocess.run(["clang", "-O1", "-o", exe_p, c_p], check=True, capture_output=True, text=True)
                r = subprocess.run([exe_p], check=True, capture_output=True, text=True)
                self.assertEqual(r.stdout.strip(), "sigil_arm64: OK")


if __name__ == "__main__":
    unittest.main()
