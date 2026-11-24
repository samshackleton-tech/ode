# Ode Implementation Catalog (Living Document)

This catalog tracks the data processors, cryptographic primitives, and self-hosting verifier modules
targeted for proof-carrying native machine code in Ode (x86-64 and AArch64), filtered first by
components that already have complete declarative specifications in this repository or in open-source
Lean 4 projects.

Every table below uses the same status words:
- **`shown`**: verified by the Lean 4 verifier `odeverify` from the compiled object bytes.
- **`legacy-kcheck`**: verified by the older Python verifier in `kcheck/programs/`, not yet migrated to `odeverify`.
- **`spec-ready`**: complete declarative specification exists; implementation pending in the Spec-First AI Factory.
- **`planned`**: target queued for specification and implementation.

---

## Wave 1 — Complete Existing Specs (Start Here)

Each row below lists one data processor or primitive that already has a complete declarative
specification (either inside this repository, in an open-source Lean 4 repository, or both). Columns
show the existing Ode specification path, any verified open-source Lean 4 specification repository,
and current verification status on x86-64 and AArch64.

| Target | Category | Existing Ode Spec | Open-Source Lean 4 Spec | x86-64 | AArch64 |
|---|---|---|---|---|---|
| **BLAKE3 (full single-threaded hash)** | Crypto | `kcheck/blake3.spec` + `proof-core/examples/arm64/hash_arm64.spec` | `c2sp/BLAKE3` (in-repo) | **`shown`** (14/14 fns, 3,761 insns) | **`shown`** (6/6 fns, 368 insns) |
| **Base64 (RFC 4648 strict encode + decode)** | Encoding | `kcheck/programs/base64/base64.spec`, `factory/verified/base64_*` | `predictable-machines/lean4-base64` (MIT: `Encode.lean`, `Decode.lean`) | **`shown`** (`char_val`, `encode_char`, `valid_quad`) | **`shown`** (`char_val`, `encode_char`, `valid_quad`) |
| **UTF-8 (RFC 3629 strict validator + decoder)** | Encoding | `kcheck/programs/utf8/utf8.spec` (61 lines), `factory/verified/utf8_is_ascii_*` | `Proven-Commons/utf` (Apache-2.0: `Utf/Proofs/{Decode,Encode}.lean`) | **`shown`** (`utf8_is_ascii`) / `legacy-kcheck` (full) | **`shown`** (`utf8_is_ascii`) |
| **Varint / LEB128 (encode + strict decode)** | Wire codec | `kcheck/programs/varint/varint.spec` (13 lines) | `Lean-zh/protobuf` (MIT) | **`shown`** (encode) / `spec-ready` (decode) | `spec-ready` |
| **ASCII Decimal integer parser** | Parser | `kcheck/programs/decimal/decimal.spec` (34 lines) | — | `legacy-kcheck` | `spec-ready` |
| **Adler-32 (RFC 1950)** | Checksum | `kcheck/programs/adler32/adler32.spec` (34 lines), `factory/verified/adler32_s1_*` | — | **`shown`** (full + `adler32_s1`) | **`shown`** (`adler32_s1`) |
| **Internet checksum (RFC 1071)** | Checksum | `kcheck/programs/inet/inet.spec` (43 lines) | — | `legacy-kcheck` | `spec-ready` |
| **Common byte prefix / byte equality** | Utility | `kcheck/programs/common/common.spec`, `proof-core/examples/equal/equal.spec` | — | **`shown`** | **`shown`** (`v_bytes_eq`) |
| **LZ4 block decompressor + LZ4/Adler frame** | Compression | `kcheck/programs/lz4/lz4.spec` (109 lines), `factory/verified/lz4_*` | — | **`shown`** (`ext_len`, `pad_lit32`) / `legacy-kcheck` (full) | **`shown`** (`ext_len`, `pad_lit32`) |
| **Sigil (byte-to-glyph codec)** | Encoding | `kcheck/programs/sigil/sigil.spec` (175 lines) | `johnservil/sigil` (Apache-2.0: `lean/Sigil/Spec.lean`) | `spec-ready` | `spec-ready` |
| **Verifier-in-Ode Stage 1 (`Arithmetic.refutes` + `Reader` + `decode`)** | Self-hosting | `proof-core/examples/verifier/arith.spec`, `factory/verified/v_*` | `proof-core/Arithmetic.lean`, `Reader.lean`, `Core.lean` | **`shown`** (5 fns) | **`shown`** (5 fns) |

---

## Wave 2 — External Lean 4 Specs Available (Translate to Ode Specs + Factory)

Each row below lists a real-world data processor or cryptographic primitive with an existing
open-source Lean 4 specification we confirmed on GitHub. Columns show the attack surface addressed,
the Lean 4 reference repository and license, and current Ode status.

| Target | Category | Security / Practical Value | Open-Source Lean 4 Reference (License) | Status |
|---|---|---|---|---|
| **PNG chunk parser + CRC-32** | Image / framing | Classic `libpng` bounds and checksum verification | `Proven-Commons/png` (Apache-2.0: `Parse.lean`, `Header.lean`, `Crc32.lean`) | `planned` |
| **CRC32C (hardware + software)** | Checksum | Storage and networking integrity | `ryancbuckley/lean-verified-crc32c` (Apache-2.0: `MemcpyCrc32c/`) | `planned` |
| **ASN.1 / DER TLV + X.509 parser** | Binary wire | Prevents DER length malleability and certificate over-reads | `keithadler/lean-x509` (MIT: `X509/Der.lean`, `Cert.lean`) | **`shown`** (`der_tlv_len`, `der_walk_seq` on x86-64 & AArch64) |
| **ChaCha20 & Poly1305 (RFC 8439)** | Crypto | Constant-time SIMD AEAD cipher | `Egly443/chacha20-poly1305-aarch64-lean` (Apache-2.0) | **`shown`** (`chacha20_qround_4x` AVX & NEON) |
| **SipHash-2-4 / SipHash-1-3** | Crypto / DoS | Hash-table flooding defense | `8vasu/SipHash` (Apache-2.0: `SipHash.lean` + vectors) | `planned` |
| **QOI (Quite OK Image) decoder** | Image codec | Fast one-page lossless image codec | `zyansheep/qoi-zig-lean` (Lean 4 spec + Zig comparison) | `planned` |
| **Zstandard (RFC 8878) decompressor** | Compression | Major production compression format (FSE, Huffman, sequences) | `kim-em/lean-zstd` (Apache-2.0: `Zstd/Spec/{Base,BlockLoop,Complete}.lean`) | `planned` |
| **CBOR framing & canonical ints** | Binary wire | Strict binary serialization for WebAuthn / COSE | `paulbutcher/lean-cbor` (Apache-2.0) | `planned` |
| **DNS wire-name decoder (RFC 1035)** | Network parser | Compression-pointer loop and bounds safety | `BasisResearch/VeriDNS` | `planned` |

---

## Wave 3 — Additional High-Value Data Processors & Primitives

Each row below lists a high-value data processor or constant-time utility queued for declarative
Ode specification once Wave 1 and Wave 2 patterns are proven in the Spec-First AI Factory.

| Target | Category | Why It Matters | Status |
|---|---|---|---|
| **Strict Hex encoder & decoder (constant-time)** | Encoding | Zero data-dependent branches or table lookups (`trace depends on len`) | `planned` |
| **Constant-time byte equality & conditional select** | Crypto utility | Core building blocks (`trace depends on len` / nothing) | `planned` |
| **URL percent-decoder & JSON string unescaper** | Text parser | Frequent parser-differential and smuggling vulnerabilities | `planned` |
| **HTTP/1.1 chunk-size & header-line parser** | Network parser | Request-smuggling defense | `planned` |
| **TLS record header & bounds validator** | Network parser | Heartbleed-class bounds guarantee | `planned` |
| **SHA-256 / SHA-512 compression** | Crypto | Primitives left hooked in prior whole-library verifications | **`shown`** (`sha256_big_sigma_4x` AVX & NEON) |

---

## Factory Scoreboard (Updated as Verified Artifacts Land)

Each row records a verified artifact produced by the Spec-First AI Factory (or by hand), listing the
target architecture, producing model (and winning turn) or author, winning-run API spend, instruction
count, code size in bytes, proof size in bytes, and Lean 4 `odeverify` check time. Every Wave 1
artifact below is stored in `factory/verified/`, re-verified standalone from its `.ode` source by
`odeverify`, and executed on real x86-64 and AArch64 silicon in `factory/test_factory_native.py`.

| Artifact | Target | Producer | API Cost | Instructions | Code Bytes | Proof Size | `odeverify` |
|---|---|---|---:|---:|---:|---:|---:|
| `b3hashr.o` (14/14 fns, full BLAKE3) | x86-64 | Hand / Ode | — | 3,761 | 23,820 | 1.07 MB | 26.1 s |
| `b3hashr_arm64.o` (6/6 fns, full BLAKE3) | AArch64 | Hand / Ode | — | 368 | 1,472 | 12.0 KB | 0.41 s |
| `v_row_contradicts`, `v_row_sum16`, `v_bytes_eq` (6 fns) | x86-64 & AArch64 | Hand / Ode | — | 110 | 440 | 4.8 KB | < 0.2 s |
| `base64_char_val_x86_64` | x86-64 | `deepseek-v3.2` (t4) | $0.0055 | 45 | 130 | 1,357 B | 0.004 s |
| `base64_char_val_arm64` | AArch64 | `claude-sonnet-5.5` (t2) | $0.0586 | 28 | 112 | 1,164 B | 0.004 s |
| `base64_encode_char_x86_64` | x86-64 | `deepseek-v3.2` (t1) | $0.0009 | 21 | 70 | 225 B | 0.004 s |
| `base64_encode_char_arm64` | AArch64 | `deepseek-v3.2` (t1) | $0.0009 | 18 | 72 | 225 B | 0.004 s |
| `base64_valid_quad_x86_64` | x86-64 | `claude-sonnet-5.5` (t2) | $0.1116 | 53 | 170 | 11,052 B | 0.018 s |
| `base64_valid_quad_arm64` | AArch64 | `claude-sonnet-5.5` (t2) | $0.0936 | 57 | 228 | 12,998 B | 0.030 s |
| `der_tlv_len_x86_64` | x86-64 | `deepseek-v3.2` (t4) | $0.0054 | 74 | 262 | 1,039 B | 0.004 s |
| `der_tlv_len_arm64` | AArch64 | `claude-sonnet-5.5` (t1) | $0.0397 | 62 | 248 | 2,184 B | 0.004 s |
| `der_walk_seq_x86_64` | x86-64 | `claude-sonnet-5.5` (t2) | $0.0875 | 52 | 194 | 1,918 B | 0.005 s |
| `der_walk_seq_arm64` | AArch64 | `claude-sonnet-5.5` (t2) | $0.0860 | 69 | 276 | 3,118 B | 0.006 s |
| `lz4_ext_len_x86_64` | x86-64 | `deepseek-v3.2` (t3) | $0.0029 | 18 | 67 | 781 B | 0.004 s |
| `lz4_ext_len_arm64` | AArch64 | `deepseek-v3.2` (t1) | $0.0009 | 16 | 64 | 815 B | 0.003 s |
| `lz4_pad_lit32_x86_64` | x86-64 | `deepseek-v3.2` (t2) | $0.0018 | 14 | 46 | 565 B | 0.004 s |
| `lz4_pad_lit32_arm64` | AArch64 | `deepseek-v3.2` (t2) | $0.0021 | 15 | 60 | 522 B | 0.004 s |
| `chacha20_qround_4x_x86_64` | x86-64 | `deepseek-v3.2` (t1) | $0.0011 | 29 | 127 | 27 B | 0.005 s |
| `chacha20_qround_4x_arm64` | AArch64 | `deepseek-v3.2` (t1) | $0.0012 | 33 | 132 | 27 B | 0.004 s |
| `sha256_big_sigma_4x_x86_64` | x86-64 | `deepseek-v3.2` (t2) | $0.0029 | 27 | 117 | 28 B | 0.003 s |
| `sha256_big_sigma_4x_arm64` | AArch64 | `deepseek-v3.2` (t2) | $0.0027 | 27 | 108 | 28 B | 0.005 s |
| `utf8_is_ascii_x86_64` | x86-64 | `deepseek-v3.2` (t1) | $0.0009 | 14 | 52 | 477 B | 0.004 s |
| `utf8_is_ascii_arm64` | AArch64 | `deepseek-v3.2` (t1) | $0.0009 | 13 | 52 | 530 B | 0.004 s |
| `adler32_s1_x86_64` | x86-64 | `deepseek-v3.2` (t4) | $0.0046 | 13 | 51 | 1,087 B | 0.005 s |
| `adler32_s1_arm64` | AArch64 | `deepseek-v3.2` (t1) | $0.0017 | 15 | 60 | 1,102 B | 0.004 s |
| `v_row_all_zero_x86_64` | x86-64 | `deepseek-v3.2` (t3) | $0.0026 | 15 | 50 | 506 B | 0.004 s |
| `v_row_all_zero_arm64` | AArch64 | `deepseek-v3.2` (t1) | $0.0010 | 13 | 52 | 563 B | 0.004 s |
| `v_arm64_rd_valid_x86_64` | x86-64 | `deepseek-v3.2` (t1) | $0.0008 | 8 | 30 | 67 B | 0.003 s |
| `v_arm64_rd_valid_arm64` | AArch64 | `deepseek-v3.2` (t1) | $0.0009 | 8 | 32 | 238 B | 0.003 s |

**Wave 1 totals (26 verified artifacts, 13 routines x 2 targets):** 757 machine instructions,
2,862 code bytes, 42,643 proof bytes total, 0.146 s sum of `odeverify` checks, **$0.5185** total
winning-run API spend (20/26 verified by `deepseek-v3.2` at $0.0008-$0.0055 each; 6/26 escalated to
`claude-sonnet-5.5` at $0.0397-$0.1116 each).

### Wave 1 Findings Queued for Wave 2
Running Wave 1 surfaced four concrete engineering improvements (two fixed immediately during Wave 1;
two logged for Wave 2):
1. **Fixed in Wave 1:** `core/x86.tab` generalized `pslld128`/`psrld128` to support both 2-operand SSE
   and 3-operand VEX (`vpslld`/`vpsrld`) encodings; `arm64/arm64.tab` gained Row 50 `and_rrr`
   (`and D64, S64, P64`) cross-checked on Apple Silicon (8,600 instances, 0 differences) and proved
   in `arm64/agree/Agree.lean` (50/50 rows); `arm64/asm.py` fixed `written()` to ignore condition flags
   inside `inline fn`; `proof-core/statement.py` added `requires A == B` for linear expressions.
2. **Logged for Wave 2 (`base64_validate` whole-stream & `base64_encode12`):** (a) preserving
   clean-frame marks (`s.q.fq`) across a loop `place` so AArch64 callers that make calls inside loops
   do not have to stash `x30` in a callee-saved register; (b) letting a contract state an upper bound
   on a returned value (such as `r < 256` for `ode_b64_letter`) or letting a callee write a non-word
   slice of its caller's output buffer; (c) speeding up `prove.py`'s `specGoal` when a recursive
   definition calls a multi-branch helper several times per step.

*Ode stands for Obsessively Double-checking Everything.*
