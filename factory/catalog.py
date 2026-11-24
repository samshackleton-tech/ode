#!/usr/bin/env python3
"""Spec-First AI Factory — Wave 1 Data-Processor & Verifier-in-Ode Catalog.

Thirteen real-world routines across four priority data-processor pillars (strict RFC 4648 Base64,
canonical ASN.1 / DER TLV parsing, LZ4 block decompression, FIPS 180-4 SHA-256) plus UTF-8,
Adler-32, and Stage 1 Verifier-in-Ode building blocks — each targeted at both x86-64 and AArch64
(26 verified machine-code artifacts total).

Every specification here is pure declarative Ode spec syntax checked directly by Lean 4 `odeverify`.
"""

WAVE1_ROUTINES = [
    # ------------------------------------------------------------------
    # Pillar 1: Strict RFC 4648 Base64 (Encoder + Canonical Decoder)
    # ------------------------------------------------------------------
    {
        "id": "base64_char_val",
        "pillar": "base64",
        "title": "RFC 4648 single-character Base64 alphabet decoder (returns 0..63 or 255)",
        "symbol": "ode_b64_char_val",
        "spec": """// RFC 4648 Section 4 Base64 alphabet decoder: A-Z -> 0..25, a-z -> 26..51,
// 0-9 -> 52..61, '+' (43) -> 62, '/' (47) -> 63; any other byte -> 255.
def b64_val(b) {
    if b >= 65 && b <= 90 then b - 65
    else if b >= 97 && b <= 122 then b - 71
    else if b >= 48 && b <= 57 then b + 4
    else if b == 43 then 62
    else if b == 47 then 63
    else 255
}

contract ode_b64_char_val(b: number) {
    requires b < 256
    returns b64_val(b)
    trace depends on b
    stack 0
}
""",
        "prompt_notes": (
            "Decode one ASCII byte `b` (0..255) into its RFC 4648 Base64 6-bit value (0..63), "
            "or return 255 if `b` is not in the Base64 alphabet (`A-Z`, `a-z`, `0-9`, `+`, `/`)."
        ),
    },
    {
        "id": "base64_valid_quad",
        "pillar": "base64",
        "title": "Strict canonical RFC 4648 4-byte Base64 quad & padding validator (rejects non-zero trailing padding bits)",
        "symbol": "ode_b64_valid_quad",
        "spec": """// Strict canonical RFC 4648 Section 3.5 & 4 Base64 4-byte quad validator.
// Enforces alphabet membership, valid '=' / '==' placement, and canonical zero
// trailing padding bits (rejects e.g. "Zh==" and "Zm9="). Returns 1 if valid, 0 otherwise.
def b64_val(b) {
    if b >= 65 && b <= 90 then b - 65
    else if b >= 97 && b <= 122 then b - 71
    else if b >= 48 && b <= 57 then b + 4
    else if b == 43 then 62
    else if b == 47 then 63
    else 255
}

def b64_quad_ok(v0, v1, c2, v2, c3, v3) {
    if v0 == 255 || v1 == 255 then 0
    else if c2 == 61 then
        if c3 == 61 && v1 % 16 == 0 then 1 else 0
    else if c3 == 61 then
        if v2 != 255 && v2 % 4 == 0 then 1 else 0
    else if v2 != 255 && v3 != 255 then 1
    else 0
}

def b64_valid_quad(c0, c1, c2, c3) {
    b64_quad_ok(b64_val(c0), b64_val(c1), c2, b64_val(c2), c3, b64_val(c3))
}

contract ode_b64_char_val(b: number) {
    requires b < 256
    returns b64_val(b)
    trace depends on b
    stack 0
}

contract ode_b64_valid_quad(c0: number, c1: number, c2: number, c3: number) {
    requires c0 < 256
    requires c1 < 256
    requires c2 < 256
    requires c3 < 256
    returns b64_valid_quad(c0, c1, c2, c3)
    trace depends on c0, c1, c2, c3
    stack 64
}
""",
        "prompt_notes": (
            "Write TWO functions in one `.ode` file (helper FIRST, then main function): "
            "(1) `fn b64_char_val as \"ode_b64_char_val\"` (0 stack), "
            "(2) `fn b64_valid_quad as \"ode_b64_valid_quad\"` calling `ode_b64_char_val` on c0, c1, c2, c3, "
            "then checking the exact canonical padding rules (`v1 % 16 == 0` for `==`, `v2 % 4 == 0` for `=`). "
            "Funnel all returns through ONE epilogue restoring callee-saved registers and stack (and x30 on arm64)."
        ),
    },
    {
        "id": "base64_validate",
        "pillar": "base64",
        "title": "Strict canonical RFC 4648 Base64 validator (rejects non-zero trailing padding bits)",
        "symbol": "ode_b64_validate",
        "spec": """// Strict canonical RFC 4648 Section 3.5 & 4 Base64 validator.
// Rejects: length not a multiple of 4, non-alphabet bytes, '=' outside final 2 bytes,
// single '=' at position n-2 without '=' at n-1, and non-canonical non-zero trailing
// padding bits (the bug class behind real-world Base64 decoder vulnerabilities).
// Returns 1 if valid canonical Base64, 0 otherwise.
def b64_val(b) {
    if b >= 65 && b <= 90 then b - 65
    else if b >= 97 && b <= 122 then b - 71
    else if b >= 48 && b <= 57 then b + 4
    else if b == 43 then 62
    else if b == 47 then 63
    else 255
}

def b64_valid_tail(a, at) {
    if b64_val(a[at]) == 255 || b64_val(a[at + 1]) == 255 then 0
    else if a[at + 2] == 61 then
        if a[at + 3] == 61 && b64_val(a[at + 1]) % 16 == 0 then 1 else 0
    else if a[at + 3] == 61 then
        if b64_val(a[at + 2]) != 255 && b64_val(a[at + 2]) % 4 == 0 then 1 else 0
    else if b64_val(a[at + 2]) != 255 && b64_val(a[at + 3]) != 255 then 1
    else 0
}

def b64_valid_from(a, at) {
    if at == len(a) then 1
    else if at + 4 > len(a) then 0
    else if at + 4 == len(a) then b64_valid_tail(a, at)
    else if b64_val(a[at]) == 255 || b64_val(a[at + 1]) == 255 || b64_val(a[at + 2]) == 255 || b64_val(a[at + 3]) == 255 then 0
    else b64_valid_from(a, at + 4)
}

def b64_valid(a) {
    b64_valid_from(a, 0)
}

contract ode_b64_char_val(b: number) {
    requires b < 256
    returns b64_val(b)
    trace depends on b
    stack 0
}

contract ode_b64_validate(input: n bytes, n: number) {
    returns b64_valid(input)
    trace depends on input, n
    stack 64
}
""",
        "prompt_notes": (
            "Write TWO functions in one `.ode` file (helper FIRST, then main function): "
            "(1) `fn b64_char_val as \"ode_b64_char_val\"` (0 stack, decodes one byte 0..255 to 0..63 or 255), "
            "(2) `fn b64_validate as \"ode_b64_validate\"` calling `ode_b64_char_val` on each byte (this keeps symbolic path count tiny!). "
            "Save callee-saved registers in a `frame` (aligned 16 bytes; remember `sub rsp, frame.size` on x86-64 / `sub sp, sp, frame.size` on arm64). "
            "On arm64, keep `x30` (return address) in a callee-saved register like `x28` across the loop (`saved[0] := x28; mov x28, x30` before loop, `mov x30, x28; x28 := saved[0]` before `ret`) so `x30` stays trace-clean across the loop `place`! "
            "IMPORTANT: funnel ALL returns (0 and 1) through ONE single `@done:` epilogue label that restores every callee-saved register, x30/lr, and `sp`/`rsp` before `ret`! "
            "Loop `at` from 0 in steps of 4 with `place { name at = ...; fact at <= n; fact b64_valid_from(input, 0) == b64_valid_from(input, at); decreases n - at }`. "
            "Inside loop: if `at == n` return 1; compute `rem = n - at`; if `rem < 4` return 0; if `rem == 4` check the tail (padding `=` rules + canonical zero trailing bits!) and return 1 or 0; else validate 4 chars via `ode_b64_char_val` and add 4 to `at`."
        ),
    },
    {
        "id": "base64_encode_char",
        "pillar": "base64",
        "title": "RFC 4648 single-6-bit Base64 alphabet encoder (maps 0..63 -> ASCII Base64 byte)",
        "symbol": "ode_b64_encode_char",
        "spec": """// RFC 4648 Section 4 Base64 alphabet encoder: 0..25 -> A-Z, 26..51 -> a-z,
// 52..61 -> 0-9, 62 -> '+' (43), 63 -> '/' (47).
def b64_letter(v) {
    if v < 26 then 65 + v
    else if v < 52 then 71 + v
    else if v < 62 then v - 4
    else if v == 62 then 43
    else 47
}

contract ode_b64_encode_char(v: number) {
    requires v < 64
    returns b64_letter(v)
    trace depends on v
    stack 0
}
""",
        "prompt_notes": (
            "Map 6-bit value `v` (0..63) to its RFC 4648 ASCII Base64 byte (`A-Z`, `a-z`, `0-9`, `+`, `/`). Zero stack."
        ),
    },

    # ------------------------------------------------------------------
    # Pillar 2: Canonical ASN.1 / DER TLV Parser (X.509 / TLS / ECDSA)
    # ------------------------------------------------------------------
    {
        "id": "der_tlv_len",
        "pillar": "asn1_der",
        "title": "Canonical ASN.1 / DER single TLV header & bounds validator (ITU-T X.690)",
        "symbol": "ode_der_tlv_len",
        "spec": """// Canonical ASN.1 / DER TLV parser (ITU-T X.690 Section 10.1).
// Enforces single-byte tag (tag % 32 != 31), rejects indefinite length (0x80),
// rejects non-minimal long forms (0x81 with len < 128; 0x82 with high byte 0),
// rejects lengths > 65535 (0x83+), and enforces header + length <= len(buf).
// Returns total TLV byte size (header + content) if valid, or 0 if malformed/truncated.
def der_tlv_l1(buf, at) {
    if at + 3 > len(buf) then 0
    else if buf[at + 2] >= 128 && at + 3 + buf[at + 2] <= len(buf) then 3 + buf[at + 2]
    else 0
}

def der_tlv_l2(buf, at) {
    if at + 4 > len(buf) then 0
    else if buf[at + 2] >= 1 && at + 4 + 256 * buf[at + 2] + buf[at + 3] <= len(buf) then 4 + 256 * buf[at + 2] + buf[at + 3]
    else 0
}

def der_tlv_size(buf, at) {
    if at + 2 > len(buf) then 0
    else if buf[at] % 32 == 31 then 0
    else if buf[at + 1] < 128 then
        if at + 2 + buf[at + 1] <= len(buf) then 2 + buf[at + 1] else 0
    else if buf[at + 1] == 129 then der_tlv_l1(buf, at)
    else if buf[at + 1] == 130 then der_tlv_l2(buf, at)
    else 0
}

contract ode_der_tlv_len(buf: n bytes, n: number) {
    returns der_tlv_size(buf, 0)
    trace depends on buf, n
    stack 0
}
""",
        "prompt_notes": (
            "Parse one canonical ASN.1 DER TLV starting at offset 0 of `buf[0..n]`. "
            "Check `n >= 2`, `(buf[0] & 31) != 31` (on AArch64 use `lsl 59; lsr 59` since `and` is not in arm64.tab), "
            "then short form (`l0 < 128`), 1-byte long form (`l0 == 129` with `buf[2] >= 128`), "
            "2-byte long form (`l0 == 130` with `buf[2] >= 1` and `l = (buf[2] << 8) + buf[3]`), else return 0. "
            "Carefully avoid integer overflow when checking `header + l <= n` (compare `l <= n - header`)."
        ),
    },
    {
        "id": "der_walk_seq",
        "pillar": "asn1_der",
        "title": "Canonical ASN.1 / DER SEQUENCE element walker (arbitrary length, zero trailing bytes)",
        "symbol": "ode_der_walk_seq",
        "spec": """// Canonical ASN.1 / DER SEQUENCE element walker: walks consecutive canonical DER TLVs
// spanning buf[0..n] with zero trailing garbage bytes.
// Returns 1 if buf[0..n] is a valid concatenation of canonical DER TLVs, 0 otherwise.
def der_seq_l1(buf, at) {
    if at + 3 > len(buf) then 0
    else if buf[at + 2] >= 128 && at + 3 + buf[at + 2] <= len(buf) then der_seq_from(buf, at + 3 + buf[at + 2])
    else 0
}

def der_seq_l2(buf, at) {
    if at + 4 > len(buf) then 0
    else if buf[at + 2] >= 1 && at + 4 + 256 * buf[at + 2] + buf[at + 3] <= len(buf) then der_seq_from(buf, at + 4 + 256 * buf[at + 2] + buf[at + 3])
    else 0
}

def der_seq_from(buf, at) {
    if at == len(buf) then 1
    else if at + 2 > len(buf) then 0
    else if buf[at] % 32 == 31 then 0
    else if buf[at + 1] < 128 then
        if at + 2 + buf[at + 1] <= len(buf) then der_seq_from(buf, at + 2 + buf[at + 1]) else 0
    else if buf[at + 1] == 129 then der_seq_l1(buf, at)
    else if buf[at + 1] == 130 then der_seq_l2(buf, at)
    else 0
}

contract ode_der_walk_seq(buf: n bytes, n: number) {
    returns der_seq_from(buf, 0)
    trace depends on buf, n
    stack 32
}
""",
        "prompt_notes": (
            "Loop with cursor `at` from `0` to `n`: "
            "`place { name at = ...; fact at <= n; fact der_seq_from(buf, 0) == der_seq_from(buf, at); decreases n - at }`. "
            "At each step parse the canonical DER TLV at `buf + at`; if malformed/truncated return 0; otherwise advance `at += sz` (guaranteed >= 2, strictly decreasing `n - at`)."
        ),
    },

    # ------------------------------------------------------------------
    # Pillar 3: LZ4 Block Decompression (Bounds & Extended Length)
    # ------------------------------------------------------------------
    {
        "id": "lz4_ext_len",
        "pillar": "lz4",
        "title": "LZ4 extended length run decoder (arbitrary length, strict bounds & overflow guard)",
        "symbol": "ode_lz4_ext_len",
        "spec": """// LZ4 block format extended length reader (from kcheck/programs/lz4/lz4.spec):
// While buf[at] == 255, add 255 to `acc`; when buf[at] < 255, add buf[at] and return total (>= 15).
// Returns 0 if the buffer ends before a byte < 255 (valid lengths are always >= 15).
def lz4_len_from(buf, at, acc) {
    if at >= len(buf) then 0
    else if buf[at] == 255 then lz4_len_from(buf, at + 1, acc + 255)
    else acc + buf[at]
}

contract ode_lz4_ext_len(buf: n bytes, n: number) {
    requires n <= 65536
    returns lz4_len_from(buf, 0, 15)
    trace depends on buf, n
    stack 0
}
""",
        "prompt_notes": (
            "Start with `at := 0`, `acc := 15`. Use loop invariant: "
            "`place { name at = ...; name acc = ...; fact at <= n; fact acc == 15 + 255 * at; "
            "fact lz4_len_from(buf, 0, 15) == lz4_len_from(buf, at, acc); decreases n - at }`. "
            "If `at == n`, return 0; if `buf[at] == 255`, add 255 to `acc` and increment `at`; else add `buf[at]` to `acc` and return `acc`."
        ),
    },
    {
        "id": "lz4_pad_lit32",
        "pillar": "lz4",
        "title": "Constant-time 32-byte literal copy & zero-pad (`trace depends on n` only)",
        "symbol": "ode_lz4_pad_lit32",
        "spec": """// Copy n bytes (n <= 32) from src into a 32-byte block out, zero-padding the tail.
// Constant-time in the data bytes: trace depends on n only.
def pad32(src) { [if i < len(src) then src[i] else 0 for i in 0..32] }

contract ode_lz4_pad_lit32(out: 32 bytes, src: n bytes, n: number) {
    requires no_overlap(out, src)
    requires n <= 32
    ensures out = pad32(src)
    trace depends on n
    stack 0
}
""",
        "prompt_notes": (
            "Forward loop `i := 0` up to `32` with `wrote out[.. i] = pad32(src)` and `decreases 32 - i`."
        ),
    },

    # ------------------------------------------------------------------
    # Pillar 4: FIPS 180-4 SHA-256 Core Primitives (Constant-Time SIMD)
    # ------------------------------------------------------------------
    {
        "id": "chacha20_qround_4x",
        "pillar": "crypto_simd",
        "title": "RFC 8439 ChaCha20 4-lane SIMD full quarter-round (constant-time, 64-byte state)",
        "symbol": "ode_chacha20_qround_4x",
        "spec": """// RFC 8439 Section 2.1 ChaCha20 quarter-round executed across 4 parallel 32-bit lanes
// (a 64-byte block arranged as four 16-byte rows a, b, c, d).
// Note: ROTL(x, k) == ROTR(x, 32 - k), so rotations 16, 12, 8, 7 are >>> 16, >>> 20, >>> 24, >>> 25.
// Zero branches, zero stack, constant-time in all data.
def qr_a1(a, b) { a + b }
def qr_d1(a1, d) { (d ^ a1) >>> 16 }
def qr_c1(c, d1) { c + d1 }
def qr_b1(b, c1) { (b ^ c1) >>> 20 }
def qr_a2(a1, b1) { a1 + b1 }
def qr_d2(a2, d1) { (d1 ^ a2) >>> 24 }
def qr_c2(c1, d2) { c1 + d2 }
def qr_b2(b1, c2) { (b1 ^ c2) >>> 25 }

def chacha_qr(s) {
    let a = [s[0], s[1], s[2], s[3]]
    let b = [s[4], s[5], s[6], s[7]]
    let c = [s[8], s[9], s[10], s[11]]
    let d = [s[12], s[13], s[14], s[15]]
    let a1 = [qr_a1(a[i], b[i]) for i in 0..4]
    let d1 = [qr_d1(a1[i], d[i]) for i in 0..4]
    let c1 = [qr_c1(c[i], d1[i]) for i in 0..4]
    let b1 = [qr_b1(b[i], c1[i]) for i in 0..4]
    let a2 = [qr_a2(a1[i], b1[i]) for i in 0..4]
    let d2 = [qr_d2(a2[i], d1[i]) for i in 0..4]
    let c2 = [qr_c2(c1[i], d2[i]) for i in 0..4]
    let b2 = [qr_b2(b1[i], c2[i]) for i in 0..4]
    a2 ++ b2 ++ c2 ++ d2
}

contract ode_chacha20_qround_4x(out: block, state: block) {
    requires no_overlap(out, state)
    ensures out = chacha_qr(state)
    stack 0
}
""",
        "needs_x86": "    needs avx\n",
        "prompt_notes": (
            "Load the four 16-byte rows a=[state+0], b=[state+16], c=[state+32], d=[state+48] into four 128-bit vector registers. "
            "Apply RFC 8439 ChaCha20 quarter-round: a+=b; d=(d^a)>>>16; c+=d; b=(b^c)>>>20; a+=b; d=(d^a)>>>24; c+=d; b=(b^c)>>>25. "
            "On x86-64, use VEX 128-bit instructions `vmovdqu`, `vpaddd`, `vpxor`, `vpsrld xmmD, xmmS, k`, `vpslld xmmD, xmmS, 32-k`, `vpor` (no AVX-512 needed!). "
            "On AArch64, use `rev32 .8h` for >>>16 and `ushr`/`shl`/`orr` for >>>20, >>>24, >>>25, `add .4s`, `eor .16b`."
        ),
    },
    {
        "id": "sha256_big_sigma_4x",
        "pillar": "sha256",
        "title": "FIPS 180-4 SHA-256 4-lane SIMD round Sigma0(a) + Sigma1(e) (constant-time)",
        "symbol": "ode_sha256_big_sigma_4x",
        "spec": """// FIPS 180-4 SHA-256 round functions:
//   Sigma0(a) = (a >>> 2) ^ (a >>> 13) ^ (a >>> 22)
//   Sigma1(e) = (e >>> 6) ^ (e >>> 11) ^ (e >>> 25)
// Computed across 4x32-bit lanes and added modulo 2^32, branch-free.
def big_sigma0(a) { (a >>> 2) ^ (a >>> 13) ^ (a >>> 22) }
def big_sigma1(e) { (e >>> 6) ^ (e >>> 11) ^ (e >>> 25) }
def big_sigma_sum4(a, e) { [big_sigma0(a[i]) + big_sigma1(e[i]) for i in 0..4] }

contract ode_sha256_big_sigma_4x(out: 16 bytes, a: 16 bytes, e: 16 bytes) {
    requires no_overlap(out, a, e)
    ensures out = bytes_of(big_sigma_sum4(words(a), words(e)))
    stack 0
}
""",
        "needs_x86": "    needs avx\n",
        "prompt_notes": (
            "Compute `Sigma0(a) + Sigma1(e)` across 4×u32 words in 128-bit vector registers. "
            "On x86-64, use VEX 128-bit instructions `vmovdqu`, `vpaddd`, `vpxor`, `vpsrld xmmD, xmmS, k`, `vpslld xmmD, xmmS, 32-k`, `vpor` (no AVX-512 needed!). "
            "On AArch64, do rotations with `ushr`/`shl`/`orr`, XOR with `eor`, add with `add vD.4s, vA.4s, vB.4s`."
        ),
    },

    # ------------------------------------------------------------------
    # Supporting Data Processors: UTF-8 Fast Path, Adler-32, Block XOR
    # ------------------------------------------------------------------
    {
        "id": "utf8_is_ascii",
        "pillar": "utf8",
        "title": "UTF-8 ASCII fast-path validator (returns 1 iff every byte < 128)",
        "symbol": "ode_utf8_is_ascii",
        "spec": """// UTF-8 fast-path ASCII validator: returns 1 iff every byte in input[0..n] is < 128.
def ascii_from(a, at) {
    if at == len(a) then 1
    else if a[at] >= 128 then 0
    else ascii_from(a, at + 1)
}

contract ode_utf8_is_ascii(input: n bytes, n: number) {
    returns ascii_from(input, 0)
    trace depends on input, n
    stack 0
}
""",
        "prompt_notes": (
            "Loop `i := 0` to `n` checking `input[i] < 128`; return 0 immediately if `>= 128`, else 1."
        ),
    },
    {
        "id": "adler32_s1",
        "pillar": "checksum",
        "title": "RFC 1950 Adler-32 s1 byte-sum accumulator modulo 65521",
        "symbol": "ode_adler32_s1",
        "spec": """// RFC 1950 Adler-32 s1 sequence: s[0] = 1, s[i+1] = (s[i] + input[i]) % 65521.
sequence s1(bytes) { s[0] = 1   s[i + 1] = (s[i] + bytes[i]) % 65521 }

contract ode_adler32_s1(input: n bytes, n: number) {
    returns s1(input)[n]
    trace depends on input, n
    stack 0
}
""",
        "prompt_notes": (
            "Loop `i := 0` to `n` with `s := 1`. Each byte adds `input[i]` to `s`; if `s >= 65521`, subtract `65521`. "
            "Loop invariant: `place { name i = ...; name cur = ...; fact i <= n; fact cur == s1(input)[i]; fact cur < 65521; decreases n - i }`."
        ),
    },

    # ------------------------------------------------------------------
    # Stage 1 Verifier-in-Ode Building Blocks (Self-Hosting Track)
    # ------------------------------------------------------------------
    {
        "id": "v_row_all_zero",
        "pillar": "verifier",
        "title": "Verifier-in-Ode: check all n linear-inequality row coefficients are zero",
        "symbol": "ode_v_row_all_zero",
        "spec": """// Stage 1 Verifier-in-Ode (`Arithmetic.refutes`): returns 1 iff every coefficient
// byte in row[0..n] is zero.
def row_zero_from(a, at) {
    if at == len(a) then 1
    else if a[at] != 0 then 0
    else row_zero_from(a, at + 1)
}

contract ode_v_row_all_zero(row: n bytes, n: number) {
    returns row_zero_from(row, 0)
    trace depends on row, n
    stack 0
}
""",
        "prompt_notes": "Loop `i := 0` to `n`; if `row[i] != 0` return 0; at end return 1.",
    },
    {
        "id": "v_arm64_rd_valid",
        "pillar": "verifier",
        "title": "Verifier-in-Ode: decode AArch64 Rd = word % 32 and verify Rd < 31 (sp/xzr guard)",
        "symbol": "ode_v_arm64_rd_valid",
        "spec": """// Stage 1 Verifier-in-Ode (`arm64/word.py`): given an encoded 32-bit AArch64 instruction
// word (low 32 bits of `w`), extract Rd = w % 32 and return 1 iff Rd < 31 (general register x0..x30).
def rd_valid(w) {
    if w % 32 < 31 then 1 else 0
}

contract ode_v_arm64_rd_valid(w: number) {
    returns rd_valid(w)
    trace depends on w
    stack 0
}
""",
        "prompt_notes": (
            "Extract low 5 bits `w % 32`: on x86-64 use `and rdi, 31`; on AArch64 use `lsl x0, x0, 59; lsr x0, x0, 59` "
            "(since `and` is not in arm64.tab). Compare against 31 and return 1 if `< 31` else 0."
        ),
    },
]
