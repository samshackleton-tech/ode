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
| **Base64 (RFC 4648 strict encode + decode)** | Encoding | `kcheck/programs/base64/base64.spec` (encode; add strict decode) | `predictable-machines/lean4-base64` (MIT: `Encode.lean`, `Decode.lean`) | `legacy-kcheck` (encode) / `spec-ready` (decode) | `spec-ready` |
| **UTF-8 (RFC 3629 strict validator + decoder)** | Encoding | `kcheck/programs/utf8/utf8.spec` (61 lines) | `Proven-Commons/utf` (Apache-2.0: `Utf/Proofs/{Decode,Encode}.lean`) | `legacy-kcheck` | `spec-ready` |
| **Varint / LEB128 (encode + strict decode)** | Wire codec | `kcheck/programs/varint/varint.spec` (13 lines) | `Lean-zh/protobuf` (MIT) | **`shown`** (encode) / `spec-ready` (decode) | `spec-ready` |
| **ASCII Decimal integer parser** | Parser | `kcheck/programs/decimal/decimal.spec` (34 lines) | — | `legacy-kcheck` | `spec-ready` |
| **Adler-32 (RFC 1950)** | Checksum | `kcheck/programs/adler32/adler32.spec` (34 lines) | — | **`shown`** (scalar + 4-byte unrolled) | `spec-ready` |
| **Internet checksum (RFC 1071)** | Checksum | `kcheck/programs/inet/inet.spec` (43 lines) | — | `legacy-kcheck` | `spec-ready` |
| **Common byte prefix / byte equality** | Utility | `kcheck/programs/common/common.spec`, `proof-core/examples/equal/equal.spec` | — | **`shown`** | **`shown`** (`v_bytes_eq`) |
| **LZ4 block decompressor + LZ4/Adler frame** | Compression | `kcheck/programs/lz4/lz4.spec` (109 lines), `frame/frame.spec` (90 lines) | — | `legacy-kcheck` | `spec-ready` |
| **Sigil (byte-to-glyph codec)** | Encoding | `kcheck/programs/sigil/sigil.spec` (175 lines) | `johnservil/sigil` (Apache-2.0: `lean/Sigil/Spec.lean`) | `spec-ready` | `spec-ready` |
| **Verifier-in-Ode Stage 1 (`Arithmetic.refutes` + `Reader` + `decode`)** | Self-hosting | `proof-core/examples/verifier/arith.spec` + `proof-core/Arithmetic.lean` | `proof-core/Arithmetic.lean`, `Reader.lean`, `Core.lean` | **`shown`** (3 fns; expanding) | **`shown`** (3 fns; expanding) |

---

## Wave 2 — External Lean 4 Specs Available (Translate to Ode Specs + Factory)

Each row below lists a real-world data processor or cryptographic primitive with an existing
open-source Lean 4 specification we confirmed on GitHub. Columns show the attack surface addressed,
the Lean 4 reference repository and license, and current Ode status.

| Target | Category | Security / Practical Value | Open-Source Lean 4 Reference (License) | Status |
|---|---|---|---|---|
| **PNG chunk parser + CRC-32** | Image / framing | Classic `libpng` bounds and checksum verification | `Proven-Commons/png` (Apache-2.0: `Parse.lean`, `Header.lean`, `Crc32.lean`) | `planned` |
| **CRC32C (hardware + software)** | Checksum | Storage and networking integrity | `ryancbuckley/lean-verified-crc32c` (Apache-2.0: `MemcpyCrc32c/`) | `planned` |
| **ASN.1 / DER TLV + X.509 parser** | Binary wire | Prevents DER length malleability and certificate over-reads | `keithadler/lean-x509` (MIT: `X509/Der.lean`, `Cert.lean`) | `planned` |
| **ChaCha20 & Poly1305 (RFC 8439)** | Crypto | Constant-time SIMD AEAD cipher | `Egly443/chacha20-poly1305-aarch64-lean` (Apache-2.0) | `planned` |
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
| **SHA-256 / SHA-512 compression** | Crypto | Primitives left hooked in prior whole-library verifications | `planned` |

---

## Factory Scoreboard (Updated as Verified Artifacts Land)

Each row records a verified artifact produced by the Spec-First AI Factory (or by hand), listing the
target architecture, producing model or author, API spend, instruction count, code size in bytes, and
Lean 4 `odeverify` check time.

| Artifact | Target | Producer | API Cost | Instructions | Code Bytes | `odeverify` |
|---|---|---|---:|---:|---:|---:|
| `b3hashr.o` (14/14 fns, full BLAKE3) | x86-64 | Hand / Ode | — | 3,761 | 23,820 | 26.1 s |
| `b3hashr_arm64.o` (6/6 fns, full BLAKE3) | AArch64 | Hand / Ode | — | 368 | 1,472 | 0.41 s |
| `v_row_contradicts`, `v_row_sum16`, `v_bytes_eq` (6 fns) | x86-64 & AArch64 | Hand / Ode | — | 110 | 440 | < 0.2 s |

*(Wave 1 AI Factory artifacts will be appended here as they verify `shown`.)*

*Ode stands for Obsessively Double-checking Everything.*
