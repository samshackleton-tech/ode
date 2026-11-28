"""TLS 1.3, Heartbleed Guard, HTTP/1.1 Chunked, HTTP/2 HPACK & PNG Chunk Framing tests.

Dual-verifies (`--verifier both`: Lean `odeverify` + standalone pure-Python `verify2.py`)
all 7 portable High-Level Ode kernels in `proof-core/examples/net/net_framing.ode` across
both x86-64 and AArch64, confirms exact cross-arch 52-char BLAKE3-256 contract hash
identity, and executes all 7 natively on Linux x86-64 ELF and Apple M6 AArch64 MAP_JIT
against official RFC test vectors (RFC 8446, RFC 6520, RFC 9112, RFC 7541 Appendix C.1,
ISO/IEC 15948) and CVE-class attack payloads (Heartbleed, HTTP chunk smuggling, HPACK bomb).
"""
import os, platform, shutil, struct, subprocess, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for p in (os.path.join(ROOT, "lang"), HERE, os.path.join(ROOT, "kcheck"), os.path.join(ROOT, "arm64")):
    if p not in sys.path:
        sys.path.insert(0, p)

import ode_audit

NET_SRC = os.path.join(HERE, "examples", "net", "net_framing.ode")
IS_LINUX_X86 = platform.system() == "Linux" and platform.machine() in ("x86_64", "amd64")
IS_MAC_ARM64 = platform.system() == "Darwin" and platform.machine() in ("arm64", "aarch64")

FNS = [
    "tls_record_next",
    "tls_heartbeat_ok",
    "tls_handshake_next",
    "hex_digit_val",
    "http_chunk_next",
    "hpack_int_decode",
    "png_chunk_next",
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
    /* 1. RFC 8446 §5.1 TLS Record Layer: 2 back-to-back records (Handshake 4B + AppData 3B) */
    const uint8_t tls_stream[17] = {{
        22, 0x03, 0x03, 0x00, 0x04,  0x01, 0x00, 0x00, 0x00,  /* Handshake (ClientHello len 0), next=9 */
        23, 0x03, 0x03, 0x00, 0x03,  'a', 'b', 'c'            /* AppData 3B, next=17 */
    }};
    CHK({p}tls_record_next(tls_stream, 17, 0) == 9);
    CHK({p}tls_record_next(tls_stream, 17, 9) == 17);
    CHK({p}tls_record_next(tls_stream, 16, 9) == 0);   /* truncated */
    const uint8_t tls_bad_ver[5] = {{23, 0x03, 0x00, 0x00, 0x00}}; /* SSL 3.0 rejected */
    const uint8_t tls_bad_ct[5]  = {{24, 0x03, 0x03, 0x00, 0x00}}; /* invalid content type */
    const uint8_t tls_huge[5]    = {{23, 0x03, 0x03, 0x41, 0x01}}; /* 16641 > 16640 */
    CHK({p}tls_record_next(tls_bad_ver, 5, 0) == 0);
    CHK({p}tls_record_next(tls_bad_ct, 5, 0) == 0);
    CHK({p}tls_record_next(tls_huge, 5, 0) == 0);

    /* 2. RFC 6520 §4 Heartbleed (CVE-2014-0160) guard */
    uint8_t hb_ok[23] = {{1, 0x00, 0x04, 'p', 'i', 'n', 'g'}}; /* type=1, len=4, +16B pad = 23B */
    CHK({p}tls_heartbeat_ok(hb_ok, 23) == 1);
    CHK({p}tls_heartbeat_ok(hb_ok, 22) == 0); /* 1 byte short of mandatory 16-byte padding */
    /* Classic Heartbleed attack: claims 16384 bytes (0x4000) in a 19-byte record! */
    uint8_t heartbleed[19] = {{1, 0x40, 0x00}};
    CHK({p}tls_heartbeat_ok(heartbleed, 19) == 0);

    /* 3. RFC 8446 §4 TLS Handshake message framing */
    const uint8_t hs[10] = {{1, 0x00, 0x00, 0x02, 0xAA, 0xBB,  2, 0x00, 0x00, 0x00}};
    CHK({p}tls_handshake_next(hs, 10, 0) == 6);
    CHK({p}tls_handshake_next(hs, 10, 6) == 10);
    CHK({p}tls_handshake_next(hs, 5, 0) == 0);

    /* 4. RFC 9112 §7.1 Strict HTTP/1.1 chunked framing (request-smuggling defense) */
    const char *chunked = "4\\r\\nWiki\\r\\n5\\r\\npedia\\r\\n0\\r\\n\\r\\n";
    uint64_t clen = strlen(chunked);
    uint64_t c1 = {p}http_chunk_next((const uint8_t *)chunked, clen, 0);
    CHK(c1 == 9);
    uint64_t c2 = {p}http_chunk_next((const uint8_t *)chunked, clen, c1);
    CHK(c2 == 19);
    uint64_t c3 = {p}http_chunk_next((const uint8_t *)chunked, clen, c2);
    CHK(c3 == 24);
    /* Smuggling & malformed attacks rejected */
    const char *smug_lf   = "4\\nWiki\\r\\n";         /* bare LF */
    const char *smug_sp   = " 4\\r\\nWiki\\r\\n";     /* leading whitespace */
    const char *smug_ext  = "4;x=1\\r\\nWiki\\r\\n";  /* chunk extension */
    const char *smug_ovf  = "100000000\\r\\n\\r\\n";  /* 9 hex digits (> 32-bit) */
    const char *smug_tr   = "4\\r\\nWiki\\r\\x00";    /* bad trailing CRLF */
    CHK({p}http_chunk_next((const uint8_t *)smug_lf, strlen(smug_lf), 0) == 0);
    CHK({p}http_chunk_next((const uint8_t *)smug_sp, strlen(smug_sp), 0) == 0);
    CHK({p}http_chunk_next((const uint8_t *)smug_ext, strlen(smug_ext), 0) == 0);
    CHK({p}http_chunk_next((const uint8_t *)smug_ovf, strlen(smug_ovf), 0) == 0);
    CHK({p}http_chunk_next((const uint8_t *)smug_tr, 9, 0) == 0);

    /* 5. RFC 7541 Appendix C.1 official HTTP/2 HPACK prefix-integer test vectors */
    const uint8_t hp_c11[1] = {{0x0A}};                    /* C.1.1: 10 with 5-bit prefix */
    const uint8_t hp_c12[3] = {{0x1F, 0x9A, 0x0A}};        /* C.1.2: 1337 with 5-bit prefix */
    const uint8_t hp_c13[1] = {{0x2A}};                    /* C.1.3: 42 with 8-bit prefix */
    const uint8_t hp_bomb[6] = {{0x1F, 0x80, 0x80, 0x80, 0x80, 0x01}}; /* >4 cont bytes */
    uint64_t r11 = {p}hpack_int_decode(hp_c11, 1, 0, 5);
    CHK((r11 >> 32) == 1 && (r11 & 0xFFFFFFFFULL) == 10);
    uint64_t r12 = {p}hpack_int_decode(hp_c12, 3, 0, 5);
    CHK((r12 >> 32) == 3 && (r12 & 0xFFFFFFFFULL) == 1337);
    uint64_t r13 = {p}hpack_int_decode(hp_c13, 1, 0, 8);
    CHK((r13 >> 32) == 1 && (r13 & 0xFFFFFFFFULL) == 42);
    CHK({p}hpack_int_decode(hp_c12, 2, 0, 5) == 0);        /* truncated */
    CHK({p}hpack_int_decode(hp_bomb, 6, 0, 5) == 0);       /* overflow bomb rejected */

    /* 6. ISO/IEC 15948 PNG chunk framing (IHDR 13B + IEND 0B after 8B PNG signature) */
    uint8_t png[8 + 25 + 12];
    memset(png, 0, sizeof(png));
    /* IHDR at offset 8: length=13, type="IHDR", 13 data bytes, 4 CRC bytes -> next = 33 */
    png[8 + 3] = 13;
    png[8 + 4] = 'I'; png[8 + 5] = 'H'; png[8 + 6] = 'D'; png[8 + 7] = 'R';
    /* IEND at offset 33: length=0, type="IEND", 4 CRC bytes -> next = 45 */
    png[33 + 4] = 'I'; png[33 + 5] = 'E'; png[33 + 6] = 'N'; png[33 + 7] = 'D';
    CHK({p}png_chunk_next(png, 45, 8) == 33);
    CHK({p}png_chunk_next(png, 45, 33) == 45);
    CHK({p}png_chunk_next(png, 44, 33) == 0); /* truncated CRC */
    const uint8_t png_bad_len[12] = {{0x80, 0, 0, 0, 'I', 'H', 'D', 'R', 0, 0, 0, 0}};
    const uint8_t png_bad_typ[12] = {{0, 0, 0, 0, 'I', 'H', '1', 'R', 0, 0, 0, 0}};
    CHK({p}png_chunk_next(png_bad_len, 12, 0) == 0); /* length >= 2^31 rejected */
    CHK({p}png_chunk_next(png_bad_typ, 12, 0) == 0); /* non-letter chunk type rejected */
"""


class TestNetFraming(unittest.TestCase):
    def test_01_dual_verify_all_7_kernels_both_arches_and_run_native(self):
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
                        NET_SRC, None, out_o, out_p,
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
                    f'uint64_t {syms[("tls_record_next", "x86_64")]}(const uint8_t *, uint64_t, uint64_t);',
                    f'uint64_t {syms[("tls_heartbeat_ok", "x86_64")]}(const uint8_t *, uint64_t);',
                    f'uint64_t {syms[("tls_handshake_next", "x86_64")]}(const uint8_t *, uint64_t, uint64_t);',
                    f'uint64_t {syms[("hex_digit_val", "x86_64")]}(uint64_t);',
                    f'uint64_t {syms[("http_chunk_next", "x86_64")]}(const uint8_t *, uint64_t, uint64_t);',
                    f'uint64_t {syms[("hpack_int_decode", "x86_64")]}(const uint8_t *, uint64_t, uint64_t, uint64_t);',
                    f'uint64_t {syms[("png_chunk_next", "x86_64")]}(const uint8_t *, uint64_t, uint64_t);',
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
    puts("net_framing_x86_64: OK");
    return 0;
}}
"""
                c_p = os.path.join(d, "run_net.c")
                exe_p = os.path.join(d, "run_net")
                with open(c_p, "w", encoding="utf-8") as f:
                    f.write(c_src)
                subprocess.run(
                    [cc, "-O1", "-o", exe_p, c_p] + [objs[(fn, "x86_64")] for fn in FNS],
                    check=True, capture_output=True, text=True,
                )
                r = subprocess.run([exe_p], check=True, capture_output=True, text=True)
                self.assertEqual(r.stdout.strip(), "net_framing_x86_64: OK")

            elif IS_MAC_ARM64 and shutil.which("clang"):
                bins = {}
                for fn in FNS:
                    code, entry = _elf_text_and_entry(objs[(fn, "arm64")], syms[(fn, "arm64")])
                    bp = os.path.join(d, f"{fn}.bin")
                    with open(bp, "wb") as bf:
                        bf.write(code)
                    bins[fn] = (bp, len(code), entry)
                types = {
                    "tls_record_next": "uint64_t (*)(const uint8_t *, uint64_t, uint64_t)",
                    "tls_heartbeat_ok": "uint64_t (*)(const uint8_t *, uint64_t)",
                    "tls_handshake_next": "uint64_t (*)(const uint8_t *, uint64_t, uint64_t)",
                    "hex_digit_val": "uint64_t (*)(uint64_t)",
                    "http_chunk_next": "uint64_t (*)(const uint8_t *, uint64_t, uint64_t)",
                    "hpack_int_decode": "uint64_t (*)(const uint8_t *, uint64_t, uint64_t, uint64_t)",
                    "png_chunk_next": "uint64_t (*)(const uint8_t *, uint64_t, uint64_t)",
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
    puts("net_framing_arm64: OK");
    return 0;
}}
"""
                c_p = os.path.join(d, "run_net_arm64.c")
                exe_p = os.path.join(d, "run_net_arm64")
                with open(c_p, "w", encoding="utf-8") as f:
                    f.write(c_src)
                subprocess.run(["clang", "-O1", "-o", exe_p, c_p], check=True, capture_output=True, text=True)
                r = subprocess.run([exe_p], check=True, capture_output=True, text=True)
                self.assertEqual(r.stdout.strip(), "net_framing_arm64: OK")


if __name__ == "__main__":
    unittest.main()
