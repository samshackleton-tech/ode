"""RFC 1035 DNS Wire-Format Parser verification and native hardware tests.

Dual-verifies (`--verifier both`: Lean `odeverify` + standalone pure-Python `verify2.py`)
all 5 portable High-Level Ode kernels in `proof-core/examples/dns/dns_wire.ode` across
both x86-64 and AArch64 (including multi-function `dns_rr_next -> dns_name_wire_len` and
acyclic compression-pointer expansion `dns_name_expand_len`), confirms exact cross-arch
52-char BLAKE3-256 contract hash identity, and executes the verified machine code natively
against real DNS response packets and adversarial compression-loop / truncation packets.
"""
import os, platform, shutil, struct, subprocess, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for p in (os.path.join(ROOT, "lang"), HERE, os.path.join(ROOT, "kcheck"), os.path.join(ROOT, "arm64")):
    if p not in sys.path:
        sys.path.insert(0, p)

import ode_audit

DNS_SRC = os.path.join(HERE, "examples", "dns", "dns_wire.ode")
IS_LINUX_X86 = platform.system() == "Linux" and platform.machine() in ("x86_64", "amd64")
IS_MAC_ARM64 = platform.system() == "Darwin" and platform.machine() in ("arm64", "aarch64")

FNS = [
    "dns_label_eq_ci",
    "dns_hdr_valid",
    "dns_name_wire_len",
    "dns_name_expand_len",
    "dns_rr_next",
]


def _elf_text_and_entry(elf_path, sym_name):
    """Return `(text_bytes, entry_offset)` from an ELF64 little-endian relocatable `.o`."""
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
        elif sh_type == 2:  # SHT_SYMTAB
            str_off = secs[sh_link][2]
            for idx, pos in enumerate(range(sh_offset, sh_offset + sh_size, 24)):
                st_name, _, _, _, st_value, _ = struct.unpack_from("<IBBHQQ", b, pos)
                sym_vals[idx] = st_value
                end = b.index(0, str_off + st_name)
                if b[str_off + st_name:end].decode("ascii", "replace") == sym_name:
                    entry_off = st_value
    buf = bytearray(text_bytes)
    for sh_name, sh_type, sh_offset, sh_size, sh_link in secs:
        if sh_type == 4 and sname(sh_name) == ".rela.text":  # SHT_RELA
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
    /* 1. RFC 1035 §2.3.3 case-insensitive ASCII label comparison */
    CHK({p}dns_label_eq_ci((const uint8_t *)"Example", (const uint8_t *)"eXaMpLe", 7) == 1);
    CHK({p}dns_label_eq_ci((const uint8_t *)"abc-123", (const uint8_t *)"ABC-123", 7) == 1);
    CHK({p}dns_label_eq_ci((const uint8_t *)"Example", (const uint8_t *)"Examplf", 7) == 0);
    CHK({p}dns_label_eq_ci((const uint8_t *)"", (const uint8_t *)"", 0) == 1);

    /* 2. Real RFC 1035 DNS response packet:
     *    Header (0..11): ID=0x1234, QR=1, OPCODE=0, RCODE=0, QD=1, AN=2
     *    Question (12..32): 3"www" 7"example" 3"com" 0  (len 17: off 12..28), QTYPE=1, QCLASS=1 (29..32)
     *      Note: "example.com" starts at offset 16!
     *    Answer 1 (33..48): PTR->12 (0xC0 0x0C, 2B), TYPE=A(1), CLASS=IN(1), TTL=300, RDLEN=4, IP=93.184.216.34
     *      off 33..34 name, 35..44 hdr(10B), 45..48 rdata(4B) -> next = 49
     *    Answer 2 (49..70): 4"mail" PTR->16 (0xC0 0x10, 7B), TYPE=A(1), CLASS=IN(1), TTL=60, RDLEN=4, IP=1.2.3.4
     *      off 49..55 name(7B), 56..65 hdr(10B), 66..69 rdata(4B) -> next = 70
     */
    const uint8_t pkt[70] = {{
        /* Header 0..11 */
        0x12, 0x34, 0x81, 0x80, 0x00, 0x01, 0x00, 0x02, 0x00, 0x00, 0x00, 0x00,
        /* Question name 12..28: 3 www 7 example 3 com 0 (17 bytes) */
        3, 'w', 'w', 'w',  7, 'e', 'x', 'a', 'm', 'p', 'l', 'e',  3, 'c', 'o', 'm',  0,
        /* QTYPE=1, QCLASS=1 (29..32) */
        0x00, 0x01, 0x00, 0x01,
        /* Answer 1 (33..48): ptr->12, A, IN, TTL=300, RDLEN=4, 93.184.216.34 */
        0xC0, 0x0C,  0x00, 0x01, 0x00, 0x01,  0x00, 0x00, 0x01, 0x2C,  0x00, 0x04,  93, 184, 216, 34,
        /* Answer 2 (49..69): 4 mail + ptr->16 ("example.com"), A, IN, TTL=60, RDLEN=4, 1.2.3.4 */
        4, 'm', 'a', 'i', 'l',  0xC0, 0x10,
        0x00, 0x01, 0x00, 0x01,  0x00, 0x00, 0x00, 0x3C,  0x00, 0x04,  1, 2, 3, 4
    }};
    uint64_t hdr = {p}dns_hdr_valid(pkt, 70);
    CHK(hdr != 0xFFFFFFFFULL);
    CHK((hdr >> 24) == 1);            /* QR=1 (response) */
    CHK(((hdr >> 20) & 15) == 0);     /* OPCODE=0 (standard query) */
    CHK(((hdr >> 16) & 15) == 0);     /* RCODE=0 (NOERROR) */
    CHK((hdr & 0xFFFF) == 1);         /* QDCOUNT=1 */

    /* Header rejection: truncated and Z-bit set */
    CHK({p}dns_hdr_valid(pkt, 11) == 0xFFFFFFFFULL);
    uint8_t bad_z[12];
    memcpy(bad_z, pkt, 12);
    bad_z[3] |= 0x40; /* set reserved Z bit */
    CHK({p}dns_hdr_valid(bad_z, 12) == 0xFFFFFFFFULL);

    /* Wire length and expanded length of all 3 names */
    CHK({p}dns_name_wire_len(pkt, 70, 12) == 17);     /* www.example.com */
    CHK({p}dns_name_expand_len(pkt, 70, 12) == 17);
    CHK({p}dns_name_wire_len(pkt, 70, 33) == 2);      /* ptr -> 12 */
    CHK({p}dns_name_expand_len(pkt, 70, 33) == 17);   /* expands to www.example.com (17B) */
    CHK({p}dns_name_wire_len(pkt, 70, 49) == 7);      /* 4"mail" + ptr -> 16 */
    CHK({p}dns_name_expand_len(pkt, 70, 49) == 18);   /* 5 ("mail") + 13 ("example.com.") = 18B */

    /* Walk both Resource Records end-to-end with verified multi-fn dns_rr_next */
    uint64_t next1 = {p}dns_rr_next(pkt, 70, 33);
    CHK(next1 == 49);
    uint64_t next2 = {p}dns_rr_next(pkt, 70, next1);
    CHK(next2 == 70);
    /* Truncated RDATA rejected */
    CHK({p}dns_rr_next(pkt, 69, 49) == 0);

    /* 3. Adversarial CVE-class DNS attack packets — ALL MUST BE REJECTED (return 0) */
    /* 3a. Self-looping pointer at offset 0: 0xC0 0x00 */
    const uint8_t self_loop[4] = {{0xC0, 0x00, 0x00, 0x00}};
    CHK({p}dns_name_wire_len(self_loop, 4, 0) == 0);
    CHK({p}dns_name_expand_len(self_loop, 4, 0) == 0);

    /* 3b. Mutual 2-node cycle: offset 0 -> ptr 2, offset 2 -> ptr 0 */
    const uint8_t mut_cycle[4] = {{0xC0, 0x02, 0xC0, 0x00}};
    CHK({p}dns_name_expand_len(mut_cycle, 4, 0) == 0);
    CHK({p}dns_name_expand_len(mut_cycle, 4, 2) == 0);

    /* 3c. Sub-label backward cycle: off 0 = 1 'a', off 2 = 0xC0 0x00 (jumps back to start of same segment!) */
    const uint8_t seg_cycle[4] = {{1, 'a', 0xC0, 0x00}};
    CHK({p}dns_name_expand_len(seg_cycle, 4, 0) == 0);

    /* 3d. Reserved label tag 0x40 and 0x80 */
    const uint8_t res_tag[4] = {{0x40, 'a', 'b', 0}};
    CHK({p}dns_name_wire_len(res_tag, 4, 0) == 0);
    CHK({p}dns_name_expand_len(res_tag, 4, 0) == 0);

    /* 3e. Truncated label and truncated pointer */
    const uint8_t trunc_lbl[4] = {{5, 'a', 'b', 'c'}};
    const uint8_t trunc_ptr[1] = {{0xC0}};
    CHK({p}dns_name_wire_len(trunc_lbl, 4, 0) == 0);
    CHK({p}dns_name_expand_len(trunc_lbl, 4, 0) == 0);
    CHK({p}dns_name_wire_len(trunc_ptr, 1, 0) == 0);
    CHK({p}dns_name_expand_len(trunc_ptr, 1, 0) == 0);

    /* 3f. Overlong expanded name (> 255 bytes via 5 x 63-byte labels = 320 bytes > 255) */
    uint8_t overlong[325];
    memset(overlong, 'a', sizeof(overlong));
    for (int k = 0; k < 5; k++) overlong[k * 64] = 63;
    overlong[320] = 0;
    CHK({p}dns_name_wire_len(overlong, 321, 0) == 0);
    CHK({p}dns_name_expand_len(overlong, 321, 0) == 0);
"""


class TestDnsWire(unittest.TestCase):
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
                        DNS_SRC, None, out_o, out_p,
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
                    f'uint64_t {syms[("dns_label_eq_ci", "x86_64")]}(const uint8_t *, const uint8_t *, uint64_t);',
                    f'uint64_t {syms[("dns_hdr_valid", "x86_64")]}(const uint8_t *, uint64_t);',
                    f'uint64_t {syms[("dns_name_wire_len", "x86_64")]}(const uint8_t *, uint64_t, uint64_t);',
                    f'uint64_t {syms[("dns_name_expand_len", "x86_64")]}(const uint8_t *, uint64_t, uint64_t);',
                    f'uint64_t {syms[("dns_rr_next", "x86_64")]}(const uint8_t *, uint64_t, uint64_t);',
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
    puts("dns_wire_x86_64: OK");
    return 0;
}}
"""
                c_p = os.path.join(d, "run_dns.c")
                exe_p = os.path.join(d, "run_dns")
                with open(c_p, "w", encoding="utf-8") as f:
                    f.write(c_src)
                # Note: dns_rr_next_x86_64.o already embeds local callee dns_name_wire_len as a local symbol,
                # so linking all 5 objects has zero duplicate global symbols!
                subprocess.run(
                    [cc, "-O1", "-o", exe_p, c_p] + [objs[(fn, "x86_64")] for fn in FNS],
                    check=True, capture_output=True, text=True,
                )
                r = subprocess.run([exe_p], check=True, capture_output=True, text=True)
                self.assertEqual(r.stdout.strip(), "dns_wire_x86_64: OK")

            elif IS_MAC_ARM64 and shutil.which("clang"):
                bins = {}
                for fn in FNS:
                    code, entry = _elf_text_and_entry(objs[(fn, "arm64")], syms[(fn, "arm64")])
                    bp = os.path.join(d, f"{fn}.bin")
                    with open(bp, "wb") as bf:
                        bf.write(code)
                    bins[fn] = (bp, len(code), entry)
                types = {
                    "dns_label_eq_ci": "uint64_t (*)(const uint8_t *, const uint8_t *, uint64_t)",
                    "dns_hdr_valid": "uint64_t (*)(const uint8_t *, uint64_t)",
                    "dns_name_wire_len": "uint64_t (*)(const uint8_t *, uint64_t, uint64_t)",
                    "dns_name_expand_len": "uint64_t (*)(const uint8_t *, uint64_t, uint64_t)",
                    "dns_rr_next": "uint64_t (*)(const uint8_t *, uint64_t, uint64_t)",
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
    puts("dns_wire_arm64: OK");
    return 0;
}}
"""
                c_p = os.path.join(d, "run_dns_arm64.c")
                exe_p = os.path.join(d, "run_dns_arm64")
                with open(c_p, "w", encoding="utf-8") as f:
                    f.write(c_src)
                subprocess.run(["clang", "-O1", "-o", exe_p, c_p], check=True, capture_output=True, text=True)
                r = subprocess.run([exe_p], check=True, capture_output=True, text=True)
                self.assertEqual(r.stdout.strip(), "dns_wire_arm64: OK")


if __name__ == "__main__":
    unittest.main()
