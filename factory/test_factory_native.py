#!/usr/bin/env python3
"""Independent verification + real-silicon RFC/ITU/FIPS execution suite for all 38 Factory artifacts.

Three independent checks:
1. Re-compiles every verified `.ode` file (19 x86-64 + 19 AArch64), checks its `.statement`,
   and runs Lean 4 `odeverify` against the saved `.proof` -> must say `shown` (38/38).
2. Audits every AArch64 `.ode` file to confirm zero writes to AAPCS64 callee-saved `v8..v15`.
3. Links the verified machine bytes of every routine for the host CPU (19 x86-64 on x86-64,
   19 AArch64 on Apple Silicon / ARM64) into a C test harness and executes it on real hardware
   against official RFC 4648, ITU-T X.690, RFC 8439, FIPS 180-4, RFC 1950, RFC 3629, RFC 1071,
   Protobuf/Wasm LEB128, and CVE negative vectors.
"""

import os
import platform
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path[:0] = [
    os.path.join(ROOT, "factory"),
    os.path.join(ROOT, "lang"),
    os.path.join(ROOT, "kcheck"),
    os.path.join(ROOT, "proof-core"),
    os.path.join(ROOT, "arm64"),
]

import catalog
import obj as aobj
import ode
import odec
import statement

VERIFIED_DIR = os.path.join(ROOT, "factory", "verified")
ODEVERIFY = os.path.join(ROOT, "proof-core", ".lake", "build", "bin", "odeverify")

WAVE1_VERIFIED_IDS = [
    "base64_char_val",
    "base64_encode_char",
    "base64_valid_quad",
    "der_tlv_len",
    "der_walk_seq",
    "lz4_ext_len",
    "lz4_pad_lit32",
    "chacha20_qround_4x",
    "sha256_big_sigma_4x",
    "utf8_is_ascii",
    "adler32_s1",
    "v_row_all_zero",
    "v_arm64_rd_valid",
]

WAVE2_VERIFIED_IDS = [
    "chacha20_double_round_4x",
    "varint_decode_u32",
    "utf8_decode_2byte",
    "hex_decode_byte",
    "inet_sum16",
    "chacha20_block",
]

ALL_VERIFIED_IDS = WAVE1_VERIFIED_IDS + WAVE2_VERIFIED_IDS
HOST_ARCH = platform.machine().lower()
HOST_TARGET = (
    "x86_64" if HOST_ARCH in ("x86_64", "amd64")
    else ("arm64" if HOST_ARCH in ("arm64", "aarch64") else None)
)


def emit_arm64_asm(obj_sym_pairs):
    lines = [
        "#ifdef __APPLE__",
        "#define SYM(x) _##x",
        "#else",
        "#define SYM(x) x",
        "#endif",
        ".text",
    ]
    for obj_p, sym in obj_sym_pairs:
        e = aobj.Elf(obj_p)
        symbols, symtab = e.symbols()
        shndx, value, size, at = aobj.place(e, sym)
        relocs = e.relocations(shndx, symtab)
        code = e.b[at:at + size]
        lines += [".p2align 2", f".globl SYM({sym})", f"SYM({sym}):"]
        for off in range(0, size, 4):
            rel = relocs.get(value + off)
            if rel is not None:
                target_sym = symbols[rel[1]][0]
                lines.append(f"  bl SYM({target_sym})")
            else:
                w = int.from_bytes(code[off:off + 4], "little")
                lines.append(f"  .word 0x{w:08x}")
    return "\n".join(lines) + "\n"


def compile_all_fns(ode_p, out_dir):
    """Compile every `fn` in `ode_p` into its own ELF `.o`, returning `[(obj_p, symbol), ...]`."""
    text = odec.read_source(ode_p)
    _, _, _, fns = odec.source(text, ode_p)
    pairs = []
    for name, sym, _, _ in fns:
        obj_p = os.path.join(out_dir, f"{sym}.o")
        odec.build(ode_p, name, obj_p)
        pairs.append((obj_p, sym))
    return pairs


C_TESTS = {
    "base64_char_val": r"""
#include <stdint.h>
#include <stdio.h>
extern uint64_t ode_b64_char_val(uint64_t b);
int main(void) {
  for (uint64_t b = 0; b < 256; b++) {
    uint64_t want = 255;
    if (b >= 'A' && b <= 'Z') want = b - 'A';
    else if (b >= 'a' && b <= 'z') want = b - 'a' + 26;
    else if (b >= '0' && b <= '9') want = b - '0' + 52;
    else if (b == '+') want = 62;
    else if (b == '/') want = 63;
    uint64_t got = ode_b64_char_val(b);
    if (got != want) { fprintf(stderr, "b=%llu got=%llu want=%llu\n", (unsigned long long)b, (unsigned long long)got, (unsigned long long)want); return 1; }
  }
  return 0;
}
""",
    "base64_encode_char": r"""
#include <stdint.h>
#include <stdio.h>
extern uint64_t ode_b64_encode_char(uint64_t v);
int main(void) {
  const char *alph = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
  for (uint64_t v = 0; v < 64; v++) {
    uint64_t got = ode_b64_encode_char(v);
    if (got != (uint8_t)alph[v]) { fprintf(stderr, "v=%llu got=%llu want=%u\n", (unsigned long long)v, (unsigned long long)got, (unsigned)alph[v]); return 1; }
  }
  return 0;
}
""",
    "base64_valid_quad": r"""
#include <stdint.h>
#include <stdio.h>
extern uint64_t ode_b64_valid_quad(uint64_t c0, uint64_t c1, uint64_t c2, uint64_t c3);
int main(void) {
  struct { const char *q; uint64_t want; } cases[] = {
    {"Zg==", 1}, {"Zh==", 0}, // canonical trailing zero bits (RFC 4648 Sec 3.5 CVE!)
    {"Zm8=", 1}, {"Zm9=", 0}, // 1-pad trailing zero bits (RFC 4648 Sec 3.5 CVE!)
    {"Zm9v", 1}, {"AAAA", 1}, {"////", 1}, {"+9aZ", 1},
    {"====", 0}, {"A===", 0}, {"Zg=A", 0}, {"Zg!=", 0},
    {"Zm9!", 0}, {"!m9v", 0}, {"Z\x00==", 0}, {"Zm\x80v", 0},
    {"AQ==", 1}, {"AR==", 0}, {"Aw==", 1}, {"Ax==", 0}, {"Ag==", 1}, {"Ah==", 0}, {"AA==", 1}, {"gA==", 1},
  };
  for (unsigned i = 0; i < sizeof(cases)/sizeof(cases[0]); i++) {
    const uint8_t *s = (const uint8_t *)cases[i].q;
    uint64_t got = ode_b64_valid_quad(s[0], s[1], s[2], s[3]);
    if (got != cases[i].want) { fprintf(stderr, "case %u got=%llu want=%llu\n", i, (unsigned long long)got, (unsigned long long)cases[i].want); return 1; }
  }
  return 0;
}
""",
    "der_tlv_len": r"""
#include <stdint.h>
#include <stdio.h>
extern uint64_t ode_der_tlv_len(const uint8_t *buf, uint64_t n);
int main(void) {
  uint8_t v0[] = {0x02, 0x01, 0x05};                      // valid short INT -> 3
  uint8_t v1[] = {0x05, 0x00};                            // valid NULL -> 2
  uint8_t v2[] = {0x04, 0x81, 0x80};                      // truncated 1-byte long -> 0
  uint8_t v3[131] = {0x04, 0x81, 0x80};                   // valid 1-byte long (128B) -> 131
  uint8_t v4[260] = {0x30, 0x82, 0x01, 0x00};             // valid 2-byte long (256B) -> 260
  uint8_t cve_indef[] = {0x30, 0x80, 0x00, 0x00};         // BER indefinite -> 0
  uint8_t cve_nonmin1[130] = {0x04, 0x81, 0x7f};          // non-minimal 1-byte (<128) -> 0
  uint8_t cve_nonmin2[260] = {0x04, 0x82, 0x00, 0xff};    // leading-zero 2-byte (<256) -> 0
  uint8_t cve_tag31[] = {0x1f, 0x01, 0x00};               // high-tag 0x1f -> 0
  uint8_t cve_l3[] = {0x30, 0x83, 0x01, 0x00, 0x00};      // 3-byte len -> 0
  if (ode_der_tlv_len(v0, 0) != 0) return 1;
  if (ode_der_tlv_len(v0, 1) != 0) return 2;
  if (ode_der_tlv_len(v0, 2) != 0) return 3;
  if (ode_der_tlv_len(v0, 3) != 3) return 4;
  if (ode_der_tlv_len(v1, 2) != 2) return 5;
  if (ode_der_tlv_len(v2, 3) != 0) return 6;
  if (ode_der_tlv_len(v3, 131) != 131) return 7;
  if (ode_der_tlv_len(v3, 130) != 0) return 8;
  if (ode_der_tlv_len(v4, 260) != 260) return 9;
  if (ode_der_tlv_len(v4, 259) != 0) return 10;
  if (ode_der_tlv_len(cve_indef, 4) != 0) return 11;
  if (ode_der_tlv_len(cve_nonmin1, 130) != 0) return 12;
  if (ode_der_tlv_len(cve_nonmin2, 260) != 0) return 13;
  if (ode_der_tlv_len(cve_tag31, 3) != 0) return 14;
  if (ode_der_tlv_len(cve_l3, 5) != 0) return 15;
  return 0;
}
""",
    "der_walk_seq": r"""
#include <stdint.h>
#include <stdio.h>
extern uint64_t ode_der_walk_seq(const uint8_t *buf, uint64_t n);
int main(void) {
  uint8_t empty[] = {0};
  uint8_t seq3[] = {0x02, 0x01, 0x01, 0x05, 0x00, 0x04, 0x02, 0xaa, 0xbb}; // 3 valid TLVs -> 1
  uint8_t bad_tail[] = {0x02, 0x01, 0x01, 0x05};                           // truncated -> 0
  uint8_t bad_ber[] = {0x02, 0x01, 0x01, 0x04, 0x80, 0x00, 0x00};          // indefinite -> 0
  uint8_t bad_nonmin[134] = {0x05, 0x00, 0x04, 0x81, 0x7f};                // non-minimal 1B -> 0
  uint8_t good_l1[133] = {0x05, 0x00, 0x04, 0x81, 0x80};                   // NULL + 128B OCTET -> 1
  if (ode_der_walk_seq(empty, 0) != 1) return 1;
  if (ode_der_walk_seq(seq3, sizeof(seq3)) != 1) return 2;
  if (ode_der_walk_seq(bad_tail, sizeof(bad_tail)) != 0) return 3;
  if (ode_der_walk_seq(bad_ber, sizeof(bad_ber)) != 0) return 4;
  if (ode_der_walk_seq(bad_nonmin, 132) != 0) return 5;
  if (ode_der_walk_seq(good_l1, 133) != 1) return 6;
  return 0;
}
""",
    "lz4_ext_len": r"""
#include <stdint.h>
#include <stdio.h>
extern uint64_t ode_lz4_ext_len(const uint8_t *src, uint64_t n);
int main(void) {
  uint8_t a[] = {0x00};
  uint8_t b[] = {0xfe};
  uint8_t c[] = {0xff, 0x00};
  uint8_t d[] = {0xff, 0xff, 0x10};
  uint8_t e[] = {0xff, 0xff}; // truncated (no terminator < 255) -> 0
  if (ode_lz4_ext_len(a, 0) != 0) return 1;
  if (ode_lz4_ext_len(a, 1) != 15) return 2;
  if (ode_lz4_ext_len(b, 1) != 269) return 3;
  if (ode_lz4_ext_len(c, 2) != 270) return 4;
  if (ode_lz4_ext_len(d, 3) != 541) return 5;
  if (ode_lz4_ext_len(e, 2) != 0) return 6;
  return 0;
}
""",
    "lz4_pad_lit32": r"""
#include <stdint.h>
#include <stdio.h>
extern void ode_lz4_pad_lit32(uint8_t *out, const uint8_t *src, uint64_t n);
int main(void) {
  uint8_t src[32], out[32];
  for (int i = 0; i < 32; i++) src[i] = (uint8_t)(0x30 + i);
  for (uint64_t n = 0; n <= 32; n++) {
    for (int i = 0; i < 32; i++) out[i] = 0xdd;
    ode_lz4_pad_lit32(out, src, n);
    for (uint64_t i = 0; i < 32; i++) {
      uint8_t want = (i < n) ? src[i] : 0;
      if (out[i] != want) { fprintf(stderr, "n=%llu i=%llu got=%u want=%u\n", (unsigned long long)n, (unsigned long long)i, out[i], want); return 1; }
    }
  }
  return 0;
}
""",
    "chacha20_qround_4x": r"""
#include <stdint.h>
#include <stdio.h>
extern void ode_chacha20_qround_4x(uint32_t *out, const uint32_t *state);
static uint32_t rotl32(uint32_t x, int n) { return (x << n) | (x >> (32 - n)); }
int main(void) {
  // Official RFC 8439 Section 2.1.1 test vector in lane 0 + 3 distinct lanes!
  uint32_t st[16] = {
    0x11111111u, 0x61707865u, 0x00000000u, 0xffffffffu,
    0x01020304u, 0x3320646eu, 0x12345678u, 0xdeadbeefu,
    0x9b8d6f43u, 0x79622d32u, 0x9abcdef0u, 0xcafebabeu,
    0x01234567u, 0x6b206574u, 0x0fedcba9u, 0x00000001u,
  };
  uint32_t want[16], got[16] = {0};
  for (int i = 0; i < 4; i++) {
    uint32_t A = st[i], B = st[4+i], C = st[8+i], D = st[12+i];
    A += B; D ^= A; D = rotl32(D, 16);
    C += D; B ^= C; B = rotl32(B, 12);
    A += B; D ^= A; D = rotl32(D, 8);
    C += D; B ^= C; B = rotl32(B, 7);
    want[i] = A; want[4+i] = B; want[8+i] = C; want[12+i] = D;
  }
  // Confirm lane 0 matches RFC 8439 Sec 2.1.1 exact constants:
  if (want[0] != 0xea2a92f4u || want[4] != 0xcb1cf8ceu || want[8] != 0x4581472eu || want[12] != 0x5881c4bbu) return 99;
  ode_chacha20_qround_4x(got, st);
  for (int i = 0; i < 16; i++) {
    if (got[i] != want[i]) {
      fprintf(stderr, "word %d got=0x%08x want=0x%08x\n", i, got[i], want[i]); return 1;
    }
  }
  return 0;
}
""",
    "sha256_big_sigma_4x": r"""
#include <stdint.h>
#include <stdio.h>
extern void ode_sha256_big_sigma_4x(uint32_t *out, const uint32_t *a, const uint32_t *e);
static uint32_t rotr32(uint32_t x, int n) { return (x >> n) | (x << (32 - n)); }
int main(void) {
  uint32_t a[4] = {0x6a09e667u, 0xbb67ae85u, 0x510e527fu, 0x00000001u};
  uint32_t e[4] = {0x510e527fu, 0x9b05688cu, 0x1f83d9abu, 0x5be0cd19u};
  uint32_t out[4] = {0};
  ode_sha256_big_sigma_4x(out, a, e);
  for (int i = 0; i < 4; i++) {
    uint32_t s0 = rotr32(a[i], 2) ^ rotr32(a[i], 13) ^ rotr32(a[i], 22);
    uint32_t s1 = rotr32(e[i], 6) ^ rotr32(e[i], 11) ^ rotr32(e[i], 25);
    uint32_t want = (uint32_t)(s0 + s1);
    if (out[i] != want) { fprintf(stderr, "lane %d got=0x%08x want=0x%08x\n", i, out[i], want); return 1; }
  }
  return 0;
}
""",
    "utf8_is_ascii": r"""
#include <stdint.h>
#include <stdio.h>
extern uint64_t ode_utf8_is_ascii(const uint8_t *buf, uint64_t n);
int main(void) {
  uint8_t ok[] = "Hello, Ode 2026! \x00\x7f";
  uint8_t bad0[] = {0x80};
  uint8_t bad_end[] = {'a', 'b', 'c', 0xff};
  if (ode_utf8_is_ascii(ok, 0) != 1) return 1;
  if (ode_utf8_is_ascii(ok, sizeof(ok)) != 1) return 2;
  if (ode_utf8_is_ascii(bad0, 1) != 0) return 3;
  if (ode_utf8_is_ascii(bad_end, 4) != 0) return 4;
  if (ode_utf8_is_ascii(bad_end, 3) != 1) return 5;
  return 0;
}
""",
    "adler32_s1": r"""
#include <stdint.h>
#include <stdio.h>
extern uint64_t ode_adler32_s1(const uint8_t *buf, uint64_t n);
int main(void) {
  const uint8_t w[] = "Wikipedia"; // RFC 1950: 1 + sum("Wikipedia") = 920
  if (ode_adler32_s1(w, 0) != 1) return 1;
  if (ode_adler32_s1(w, 9) != 920) return 2;
  uint8_t big[300];
  for (int i = 0; i < 300; i++) big[i] = 255;
  uint64_t want = (1ULL + 300ULL * 255ULL) % 65521ULL;
  if (ode_adler32_s1(big, 300) != want) return 3;
  return 0;
}
""",
    "v_row_all_zero": r"""
#include <stdint.h>
#include <stdio.h>
extern uint64_t ode_v_row_all_zero(const uint8_t *row, uint64_t n);
int main(void) {
  uint8_t z[32] = {0};
  if (ode_v_row_all_zero(z, 0) != 1) return 1;
  if (ode_v_row_all_zero(z, 32) != 1) return 2;
  z[31] = 1;
  if (ode_v_row_all_zero(z, 32) != 0) return 3;
  if (ode_v_row_all_zero(z, 31) != 1) return 4;
  return 0;
}
""",
    "v_arm64_rd_valid": r"""
#include <stdint.h>
#include <stdio.h>
extern uint64_t ode_v_arm64_rd_valid(uint64_t w);
int main(void) {
  for (uint64_t w = 0; w < 128; w++) {
    uint64_t want = ((w % 32) < 31) ? 1 : 0;
    if (ode_v_arm64_rd_valid(w) != want) return 1;
  }
  if (ode_v_arm64_rd_valid(0x8b01001fULL) != 0) return 2; // add xzr, x0, x1 -> rd=31
  if (ode_v_arm64_rd_valid(0x8b010000ULL) != 1) return 3; // add x0, x0, x1 -> rd=0
  return 0;
}
""",
    "chacha20_double_round_4x": r"""
#include <stdint.h>
#include <stdio.h>
extern void ode_chacha20_double_round_4x(uint32_t state[16]);
int main(void) {
  // Exact RFC 8439 Section 2.3.2 ChaCha20 block test vector (10 double rounds = 20 rounds)
  uint32_t s[16] = {
    0x61707865u, 0x3320646eu, 0x79622d32u, 0x6b206574u,
    0x03020100u, 0x07060504u, 0x0b0a0908u, 0x0f0e0d0cu,
    0x13121110u, 0x17161514u, 0x1b1a1918u, 0x1f1e1d1cu,
    0x00000001u, 0x09000000u, 0x4a000000u, 0x00000000u
  };
  static const uint32_t want[16] = {
    0x837778abu, 0xe238d763u, 0xa67ae21eu, 0x5950bb2fu,
    0xc4f2d0c7u, 0xfc62bb2fu, 0x8fa018fcu, 0x3f5ec7b7u,
    0x335271c2u, 0xf29489f3u, 0xeabda8fcu, 0x82e46ebdu,
    0xd19c12b4u, 0xb04e16deu, 0x9e83d0cbu, 0x4e3c50a2u
  };
  for (int r = 0; r < 10; r++) ode_chacha20_double_round_4x(s);
  for (int i = 0; i < 16; i++) {
    if (s[i] != want[i]) {
      fprintf(stderr, "word %d got=0x%08x want=0x%08x\n", i, s[i], want[i]);
      return 1;
    }
  }
  return 0;
}
""",
    "varint_decode_u32": r"""
#include <stdint.h>
#include <stdio.h>
extern uint64_t ode_varint_decode_u32(const uint8_t *buf, uint64_t n);
int main(void) {
  const uint64_t BAD = 4294967296ULL;
  uint8_t dummy[1] = {0};
  if (ode_varint_decode_u32(dummy, 0) != BAD) return 1;            // empty
  uint8_t v0[] = {0x00};
  if (ode_varint_decode_u32(v0, 1) != 0) return 2;
  uint8_t v127[] = {0x7f};
  if (ode_varint_decode_u32(v127, 1) != 127) return 3;
  uint8_t v300[] = {0xac, 0x02};                                   // Protobuf spec example = 300
  if (ode_varint_decode_u32(v300, 2) != 300) return 4;
  uint8_t over2[] = {0x80, 0x00};                                  // non-canonical overlong!
  if (ode_varint_decode_u32(over2, 2) != BAD) return 5;
  uint8_t trunc1[] = {0x80};                                       // truncated!
  if (ode_varint_decode_u32(trunc1, 1) != BAD) return 6;
  uint8_t max32[] = {0xff, 0xff, 0xff, 0xff, 0x0f};                // 0xFFFFFFFF
  if (ode_varint_decode_u32(max32, 5) != 0xffffffffULL) return 7;
  uint8_t ovf32[] = {0xff, 0xff, 0xff, 0xff, 0x10};                // >32-bit overflow!
  if (ode_varint_decode_u32(ovf32, 5) != BAD) return 8;
  uint8_t over5[] = {0x81, 0x80, 0x80, 0x80, 0x00};                // 5-byte overlong!
  if (ode_varint_decode_u32(over5, 5) != BAD) return 9;
  return 0;
}
""",
    "utf8_decode_2byte": r"""
#include <stdint.h>
#include <stdio.h>
extern uint64_t ode_utf8_decode_2byte(const uint8_t *buf, uint64_t n);
int main(void) {
  const uint64_t BAD = 4294967295ULL;
  uint8_t z[1] = {0};
  if (ode_utf8_decode_2byte(z, 0) != BAD) return 1;
  uint8_t a[] = {'A'};
  if (ode_utf8_decode_2byte(a, 1) != 'A') return 2;
  uint8_t cent[] = {0xc2, 0xa2};                                   // U+00A2 CENT SIGN
  if (ode_utf8_decode_2byte(cent, 2) != 0xa2) return 3;
  uint8_t max2[] = {0xdf, 0xbf};                                   // U+07FF
  if (ode_utf8_decode_2byte(max2, 2) != 0x7ff) return 4;
  uint8_t cve_slash[] = {0xc0, 0xaf};                              // CVE-2008-2938 overlong '/'!
  if (ode_utf8_decode_2byte(cve_slash, 2) != BAD) return 5;
  uint8_t over_c1[] = {0xc1, 0xbf};                                // overlong 0xC1!
  if (ode_utf8_decode_2byte(over_c1, 2) != BAD) return 6;
  uint8_t bad_cont[] = {0xc2, 0xc0};                               // invalid continuation!
  if (ode_utf8_decode_2byte(bad_cont, 2) != BAD) return 7;
  uint8_t trunc2[] = {0xc2};                                       // truncated 2-byte!
  if (ode_utf8_decode_2byte(trunc2, 1) != BAD) return 8;
  uint8_t lead3[] = {0xe2, 0x82, 0xac};                            // 3-byte lead rejected here
  if (ode_utf8_decode_2byte(lead3, 3) != BAD) return 9;
  return 0;
}
""",
    "hex_decode_byte": r"""
#include <stdint.h>
#include <stdio.h>
extern uint64_t ode_hex_decode_byte(uint64_t hi, uint64_t lo);
static int nib(int c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return -1;
}
int main(void) {
  // Exhaustive over all 65,536 byte pairs (hi, lo)!
  for (int hi = 0; hi < 256; hi++) {
    int nh = nib(hi);
    for (int lo = 0; lo < 256; lo++) {
      int nl = nib(lo);
      uint64_t want = (nh < 0 || nl < 0) ? 256ULL : (uint64_t)((nh << 4) | nl);
      uint64_t got = ode_hex_decode_byte((uint64_t)hi, (uint64_t)lo);
      if (got != want) {
        fprintf(stderr, "hi=%d lo=%d got=%llu want=%llu\n", hi, lo, (unsigned long long)got, (unsigned long long)want);
        return 1;
      }
    }
  }
  return 0;
}
""",
    "inet_sum16": r"""
#include <stdint.h>
#include <stdio.h>
extern uint64_t ode_inet_sum16(const uint8_t *buf, uint64_t len, uint64_t pairs);
int main(void) {
  uint8_t z[2] = {0, 0};
  if (ode_inet_sum16(z, 0, 0) != 0) return 1;
  // Exact RFC 1071 Section 3 example: 0001 + f203 + f4f5 + f6f7 = 0xddf2
  uint8_t rfc1071[8] = {0x00, 0x01, 0xf2, 0x03, 0xf4, 0xf5, 0xf6, 0xf7};
  uint64_t got = ode_inet_sum16(rfc1071, 8, 4);
  if (got != 0xddf2ULL) { fprintf(stderr, "rfc1071 got=0x%llx\n", (unsigned long long)got); return 2; }
  // Carry-wrap stress: 0xffff + 0xffff = 0x1fffe -> folds to 0xffff; + 0x0001 -> folds to 0x0001
  uint8_t wrap[6] = {0xff, 0xff, 0xff, 0xff, 0x00, 0x01};
  if (ode_inet_sum16(wrap, 6, 3) != 0x0001ULL) return 3;
  // RFC 791 IPv4 header checksum check (20 bytes = 10 pairs -> 1's complement sum == 0xffff)
  uint8_t ipv4[20] = {
    0x45, 0x00, 0x00, 0x73, 0x00, 0x00, 0x40, 0x00, 0x40, 0x11,
    0xb8, 0x61, 0xc0, 0xa8, 0x00, 0x01, 0xc0, 0xa8, 0x00, 0xc7
  };
  if (ode_inet_sum16(ipv4, 20, 10) != 0xffffULL) return 4;
  return 0;
}
""",
    "chacha20_block": r"""
#include <stdint.h>
#include <stdio.h>
#include <string.h>
extern void ode_chacha20_block(uint8_t out[64], const uint32_t state[16]);
int main(void) {
  const uint32_t s[16] = {
    0x61707865u, 0x3320646eu, 0x79622d32u, 0x6b206574u,
    0x03020100u, 0x07060504u, 0x0b0a0908u, 0x0f0e0d0cu,
    0x13121110u, 0x17161514u, 0x1b1a1918u, 0x1f1e1d1cu,
    0x00000001u, 0x09000000u, 0x4a000000u, 0x00000000u
  };
  static const uint8_t want[64] = {
    0x10, 0xf1, 0xe7, 0xe4, 0xd1, 0x3b, 0x59, 0x15,
    0x50, 0x0f, 0xdd, 0x1f, 0xa3, 0x20, 0x71, 0xc4,
    0xc7, 0xd1, 0xf4, 0xc7, 0x33, 0xc0, 0x68, 0x03,
    0x04, 0x22, 0xaa, 0x9a, 0xc3, 0xd4, 0x6c, 0x4e,
    0xd2, 0x82, 0x64, 0x46, 0x07, 0x9f, 0xaa, 0x09,
    0x14, 0xc2, 0xd7, 0x05, 0xd9, 0x8b, 0x02, 0xa2,
    0xb5, 0x12, 0x9c, 0xd1, 0xde, 0x16, 0x4e, 0xb9,
    0xcb, 0xd0, 0x83, 0xe8, 0xa2, 0x50, 0x3c, 0x4e
  };
  uint8_t got[64];
  ode_chacha20_block(got, s);
  return memcmp(got, want, 64) == 0 ? 0 : 1;
}
""",
}


class TestFactoryWave1(unittest.TestCase):
    def test_all_38_odeverify_shown(self):
        self.assertTrue(os.path.exists(ODEVERIFY), f"missing {ODEVERIFY}")
        routines = {r["id"]: r for r in catalog.ALL_ROUTINES}
        for rid in ALL_VERIFIED_IDS:
            r = routines[rid]
            for target in ("x86_64", "arm64"):
                tid = f"{rid}_{target}"
                ode_p = os.path.join(VERIFIED_DIR, f"{tid}.ode")
                spec_p = os.path.join(VERIFIED_DIR, f"{tid}.spec")
                stmt_p = os.path.join(VERIFIED_DIR, f"{tid}.statement")
                proof_p = os.path.join(VERIFIED_DIR, f"{tid}.proof")
                for p in (ode_p, spec_p, stmt_p, proof_p):
                    self.assertTrue(os.path.exists(p), f"missing artifact {p}")
                with tempfile.TemporaryDirectory() as d:
                    pairs = compile_all_fns(ode_p, d)
                    with open(spec_p) as f:
                        spec_txt = f.read()
                    fresh_stmt = os.path.join(d, f"{tid}.statement")
                    txt = statement.statement(spec_txt, pairs)
                    with open(fresh_stmt, "w") as f:
                        f.write("\n".join(txt) + "\n")
                    tab = statement.table_for(fresh_stmt)
                    res = subprocess.run(
                        [ODEVERIFY, tab, fresh_stmt, proof_p],
                        capture_output=True, text=True, check=False,
                    )
                    self.assertEqual(
                        res.returncode, 0,
                        f"{tid} odeverify failed: {res.stdout} {res.stderr}",
                    )
                    self.assertTrue(res.stdout.startswith("shown"), f"{tid}: {res.stdout}")

    def test_arm64_no_callee_saved_vector_clobber(self):
        import re
        pat = re.compile(r"\b[vq](8|9|1[0-5])\b")
        for rid in ALL_VERIFIED_IDS:
            ode_p = os.path.join(VERIFIED_DIR, f"{rid}_arm64.ode")
            with open(ode_p) as f:
                for ln, raw in enumerate(f, 1):
                    code = raw.split("//")[0]
                    self.assertIsNone(
                        pat.search(code),
                        f"{ode_p}:{ln} touches AAPCS64 callee-saved vector register: {code.strip()}",
                    )

    @unittest.skipUnless(HOST_TARGET and shutil.which("cc"),
                         "native compiler and x86_64/arm64 host required")
    def test_all_19_native_vectors_on_real_silicon(self):
        cc = shutil.which("clang") or shutil.which("cc")
        for rid in ALL_VERIFIED_IDS:
            tid = f"{rid}_{HOST_TARGET}"
            ode_p = os.path.join(VERIFIED_DIR, f"{tid}.ode")
            with tempfile.TemporaryDirectory() as d:
                pairs = compile_all_fns(ode_p, d)
                c_p = os.path.join(d, f"{rid}.c")
                exe_p = os.path.join(d, rid)
                with open(c_p, "w") as f:
                    f.write(C_TESTS[rid])
                if HOST_TARGET == "arm64":
                    s_p = os.path.join(d, f"{tid}.S")
                    with open(s_p, "w") as f:
                        f.write(emit_arm64_asm(pairs))
                    subprocess.run([cc, "-O1", c_p, s_p, "-o", exe_p], check=True)
                else:
                    objs = [p for p, _ in pairs]
                    subprocess.run([cc, "-O1", c_p, *objs, "-o", exe_p], check=True)
                run = subprocess.run([exe_p], capture_output=True, text=True)
                self.assertEqual(
                    run.returncode, 0,
                    f"{tid} native silicon test failed (rc={run.returncode}): {run.stderr}",
                )


if __name__ == "__main__":
    unittest.main()
