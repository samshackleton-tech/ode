#!/usr/bin/env pypy3
"""Verify the complete single-threaded AArch64 BLAKE3 hash (all 6 functions, 368 machine
instructions = 1,472 bytes) in ONE `odeverify` call under the Lean 4 soundness theorem,
check false-contract and mutated-code controls, and (on an AArch64 processor with `clang`)
run the verified machine code on real hardware against official BLAKE3 test vectors up to
102,400 bytes plus 150 boundary lengths in both plain and keyed modes.

    pypy3 test_hashr_arm64.py        (Lean tests skipped without `lake`; hardware run on AArch64)

The six AArch64 functions verified together in topological order:
  1. blake3_servil_compress_in_place_arm64   (116 insns, NEON one-block kernel)
  2. b3l_pad_arm64                           ( 15 insns, chunk-tail padding)
  3. b3l_node_out_arm64                      ( 17 insns, node compression)
  4. b3l_chunk_node_arm64                    ( 45 insns, chunk block loop + pad)
  5. b3l_subtree_arm64                       ( 84 insns, recursive Merkle subtree)
  6. b3l_hashr_arm64                         ( 91 insns, top-level hash + keyed hash)
Total: 6 of 6 functions, 368 instructions (1,472 bytes), `trace depends on len` only.
"""
import os, platform, shutil, subprocess, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
ARM = os.path.join(HERE, "examples", "arm64")
KCHECK = os.path.join(ROOT, "kcheck")
sys.path[:0] = [HERE, os.path.join(ROOT, "lang"), os.path.join(ROOT, "arm64"),
                os.path.join(ROOT, "core"), KCHECK]
import built, lean_verify, obj as aobj, odec, session, statement

ARM_MACHINE = platform.machine() in ("arm64", "aarch64")

FUNCTIONS = [
    ("compress_arm64.ode", "compress1_arm64", "blake3_servil_compress_in_place_arm64", 116),
    ("pad_arm64.ode",      "pad",             "b3l_pad_arm64",                          15),
    ("hash_arm64.ode",     "node_out_arm64",  "b3l_node_out_arm64",                     17),
    ("hash_arm64.ode",     "chunk_node_arm64","b3l_chunk_node_arm64",                   45),
    ("hash_arm64.ode",     "subtree_arm64",   "b3l_subtree_arm64",                      84),
    ("hash_arm64.ode",     "hashr_arm64",     "b3l_hashr_arm64",                        91),
]
KEPT_PROOF = os.path.join(HERE, "proofs", "b3hashr_arm64.proof")


def full_spec_text(change=lambda t: t):
    with open(os.path.join(KCHECK, "blake3.spec")) as f:
        text = f.read()
    for name in ("compress_arm64.spec", "pad_arm64.spec", "hash_arm64.spec"):
        with open(os.path.join(ARM, name)) as f:
            text += "\n" + f.read()
    return change(text)


def once(old, new):
    def edit(text):
        assert text.count(old) == 1, f"expected 1 occurrence of {old!r}, got {text.count(old)}"
        return text.replace(old, new, 1)
    return edit


def build_all(out_dir, hash_override=None):
    """Compile all six AArch64 Ode functions into ELF objects in `out_dir`."""
    hash_path = os.path.join(ARM, "hash_arm64.ode")
    if hash_override is not None:
        hash_path = os.path.join(out_dir, "hash_mut.ode")
        with open(os.path.join(ARM, "hash_arm64.ode")) as f:
            mut = hash_override(f.read())
        with open(hash_path, "w") as f:
            f.write(mut)
    out = []
    for src, ode_fn, sym, _ in FUNCTIONS:
        src_p = hash_path if src == "hash_arm64.ode" else os.path.join(ARM, src)
        obj_p = os.path.join(out_dir, sym + ".o")
        odec.build(src_p, ode_fn, obj_p)
        out.append((obj_p, sym))
    return out


def verify_all(spec, fns, proof_path=KEPT_PROOF):
    with tempfile.TemporaryDirectory() as d:
        st_p = os.path.join(d, "s")
        lines = statement.statement(spec, fns)
        with open(st_p, "w") as f:
            f.write("\n".join(lines) + "\n")
        r = subprocess.run(
            [os.path.join(HERE, ".lake", "build", "bin", "odeverify"),
             statement.TABLES["arm64"], st_p, proof_path],
            capture_output=True, text=True,
        )
        return r.returncode == 0, (r.stdout + r.stderr).strip()


def verify_only(spec, target, fns):
    """Check one function using its section of the kept proof via `odeprove --only`."""
    idx = [s for _, s in fns].index(target)
    sub = fns[:idx + 1]
    with open(KEPT_PROOF) as f:
        full_pf = f.read()
    # Extract the `for <target>` section from the combined kept proof.
    marker = f"for {target}\n"
    start = full_pf.index(marker)
    next_for = full_pf.find("\nfor ", start + len(marker))
    section = full_pf[start:] if next_for == -1 else full_pf[start:next_for + 1]
    pftext = section.splitlines()
    with tempfile.TemporaryDirectory() as d:
        st_p = os.path.join(d, "s")
        try:
            st_lines = statement.statement(spec, sub)
        except SystemExit as e:
            return False, str(e)
        with open(st_p, "w") as f:
            f.write("\n".join(st_lines) + "\n")
        sess = session.Session(st_p, [pftext[0]], target, only=True)
        try:
            out = sess.ask(pftext[1:]).strip()
        finally:
            sess.close()
    return out == "shown", out


def emit_asm(fns):
    """Turn the six verified ELF objects into one `.S` file preserving every instruction word
    and every `bl` relocation for native linking on macOS or Linux AArch64."""
    lines = [
        "#ifdef __APPLE__",
        "#define SYM(x) _##x",
        "#else",
        "#define SYM(x) x",
        "#endif",
        ".text",
    ]
    for obj_p, sym in fns:
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


NATIVE_HARNESS = r"""
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void b3l_hashr_arm64(uint8_t *out, const uint8_t *input, uint64_t len, const uint8_t *key, uint64_t flags);

enum { CHUNK_START = 1, CHUNK_END = 2, PARENT = 4, ROOT = 8 };
static const uint32_t IV[8] = {
    0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
    0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19
};
static const uint8_t PERM[16] = {2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8};
static uint32_t ror32(uint32_t x, int n) { return (x >> n) | (x << (32 - n)); }
static void g(uint32_t *s, int a, int b, int c, int d, uint32_t x, uint32_t y) {
    s[a] += s[b] + x; s[d] = ror32(s[d] ^ s[a], 16); s[c] += s[d]; s[b] = ror32(s[b] ^ s[c], 12);
    s[a] += s[b] + y; s[d] = ror32(s[d] ^ s[a], 8);  s[c] += s[d]; s[b] = ror32(s[b] ^ s[c], 7);
}
static uint32_t rd32(const uint8_t *p) {
    return (uint32_t)p[0] | ((uint32_t)p[1] << 8) | ((uint32_t)p[2] << 16) | ((uint32_t)p[3] << 24);
}
static void compress_ref(uint32_t h[8], const uint32_t block[16], uint64_t t, uint32_t len, uint32_t flags) {
    uint32_t s[16], m[16], n[16];
    memcpy(m, block, 64);
    for (int i = 0; i < 8; i++) s[i] = h[i];
    for (int i = 0; i < 4; i++) s[8 + i] = IV[i];
    s[12] = (uint32_t)t; s[13] = (uint32_t)(t >> 32); s[14] = len; s[15] = flags;
    for (int r = 0; r < 7; r++) {
        g(s, 0, 4, 8, 12, m[0], m[1]); g(s, 1, 5, 9, 13, m[2], m[3]);
        g(s, 2, 6, 10, 14, m[4], m[5]); g(s, 3, 7, 11, 15, m[6], m[7]);
        g(s, 0, 5, 10, 15, m[8], m[9]); g(s, 1, 6, 11, 12, m[10], m[11]);
        g(s, 2, 7, 8, 13, m[12], m[13]); g(s, 3, 4, 9, 14, m[14], m[15]);
        for (int i = 0; i < 16; i++) n[i] = m[PERM[i]];
        memcpy(m, n, 64);
    }
    for (int i = 0; i < 8; i++) h[i] = s[i] ^ s[i + 8];
}
typedef struct { uint32_t h[8], m[16]; uint64_t t; uint32_t len, flags; } node_t;
static void node_val(uint32_t out[8], const node_t *n, uint32_t root) {
    memcpy(out, n->h, 32); compress_ref(out, n->m, n->t, n->len, n->flags | root);
}
static void chunk_ref(node_t *n, const uint32_t key[8], const uint8_t *p, size_t len, uint64_t t, uint32_t flags) {
    uint32_t m[16], first = CHUNK_START;
    uint8_t last[64] = {0};
    memcpy(n->h, key, 32);
    while (len > 64) {
        for (int i = 0; i < 16; i++) m[i] = rd32(p + 4 * i);
        compress_ref(n->h, m, t, 64, flags | first);
        first = 0; p += 64; len -= 64;
    }
    if (len) memcpy(last, p, len);
    for (int i = 0; i < 16; i++) n->m[i] = rd32(last + 4 * i);
    n->t = t; n->len = (uint32_t)len; n->flags = flags | first | CHUNK_END;
}
static void blake3_ref(uint8_t out[32], const uint8_t *input, size_t len, const uint8_t key_bytes[32], uint32_t flags) {
    uint32_t key[8], stack[64][8], cv[8], h[8];
    int depth = 0;
    uint64_t chunks = 0;
    node_t n;
    for (int i = 0; i < 8; i++) key[i] = rd32(key_bytes + 4 * i);
    while (len > 1024) {
        chunk_ref(&n, key, input, 1024, chunks, flags); node_val(cv, &n, 0);
        chunks++; input += 1024; len -= 1024;
        for (uint64_t total = chunks; (total & 1) == 0; total >>= 1) {
            depth--;
            memcpy(n.h, key, 32); memcpy(n.m, stack[depth], 32); memcpy(n.m + 8, cv, 32);
            n.t = 0; n.len = 64; n.flags = flags | PARENT;
            node_val(cv, &n, 0);
        }
        memcpy(stack[depth++], cv, 32);
    }
    chunk_ref(&n, key, input, len, chunks, flags);
    while (depth > 0) {
        node_val(cv, &n, 0); depth--;
        memcpy(n.h, key, 32); memcpy(n.m, stack[depth], 32); memcpy(n.m + 8, cv, 32);
        n.t = 0; n.len = 64; n.flags = flags | PARENT;
    }
    node_val(h, &n, ROOT);
    for (int i = 0; i < 8; i++) {
        out[4 * i]     = (uint8_t)h[i];
        out[4 * i + 1] = (uint8_t)(h[i] >> 8);
        out[4 * i + 2] = (uint8_t)(h[i] >> 16);
        out[4 * i + 3] = (uint8_t)(h[i] >> 24);
    }
}

static const struct { size_t len; const char *hash, *keyed; } OFFICIAL[] = {
    {0,      "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262", "92b2b75604ed3c761f9d6f62392c8a9227ad0ea3f09573e783f1498a4ed60d26"},
    {1,      "2d3adedff11b61f14c886e35afa036736dcd87a74d27b5c1510225d0f592e213", "6d7878dfff2f485635d39013278ae14f1454b8c0a3a2d34bc1ab38228a80c95b"},
    {63,     "e9bc37a594daad83be9470df7f7b3798297c3d834ce80ba85d6e207627b7db7b", NULL},
    {64,     "4eed7141ea4a5cd4b788606bd23f46e212af9cacebacdc7d1f4c6dc7f2511b98", NULL},
    {65,     "de1e5fa0be70df6d2be8fffd0e99ceaa8eb6e8c93a63f2d8d1c30ecb6b263dee", NULL},
    {1024,   "42214739f095a406f3fc83deb889744ac00df831c10daa55189b5d121c855af7", "75c46f6f3d9eb4f55ecaaee480db732e6c2105546f1e675003687c31719c7ba4"},
    {1025,   "d00278ae47eb27b34faecf67b4fe263f82d5412916c1ffd97c8cb7fb814b8444", "357dc55de0c7e382c900fd6e320acc04146be01db6a8ce7210b7189bd664ea69"},
    {2048,   "e776b6028c7cd22a4d0ba182a8bf62205d2ef576467e838ed6f2529b85fba24a", NULL},
    {31744,  "62b6960e1a44bcc1eb1a611a8d6235b6b4b78f32e7abc4fb4c6cdcce94895c47", "efa53b389ab67c593dba624d898d0f7353ab99e4ac9d42302ee64cbf9939a419"},
    {102400, "bc3e3d41a1146b069abffad3c0d44860cf664390afce4d9661f7902e7943e085", "1c35d1a5811083fd7119f5d5d1ba027b4d01c0c6c49fb6ff2cf75393ea5db4a7"},
};

static int check_one(const uint8_t *input, size_t len, const uint8_t *key, uint64_t flags, const char *expect_hex) {
    uint8_t guard[64], ref[32];
    char hex[65];
    memset(guard, 0xA5, sizeof guard);
    b3l_hashr_arm64(guard + 16, input, (uint64_t)len, key, flags);
    blake3_ref(ref, input, len, key, (uint32_t)flags);
    for (int i = 0; i < 16; i++) {
        if (guard[i] != 0xA5 || guard[48 + i] != 0xA5) {
            printf("guard clobbered at len=%zu flags=%llu\n", len, (unsigned long long)flags);
            return 1;
        }
    }
    if (memcmp(guard + 16, ref, 32) != 0) {
        printf("mismatch vs ref at len=%zu flags=%llu\n", len, (unsigned long long)flags);
        return 1;
    }
    if (expect_hex) {
        for (int i = 0; i < 32; i++) sprintf(hex + 2 * i, "%02x", guard[16 + i]);
        if (strcmp(hex, expect_hex) != 0) {
            printf("mismatch vs official at len=%zu flags=%llu got=%s want=%s\n",
                   len, (unsigned long long)flags, hex, expect_hex);
            return 1;
        }
    }
    return 0;
}

int main(void) {
    static uint8_t input[102400], iv[32];
    static const char KEY[] = "whats the Elvish word for friend";
    for (size_t i = 0; i < sizeof input; i++) input[i] = (uint8_t)(i % 251);
    for (int i = 0; i < 8; i++) {
        iv[4 * i]     = (uint8_t)IV[i];
        iv[4 * i + 1] = (uint8_t)(IV[i] >> 8);
        iv[4 * i + 2] = (uint8_t)(IV[i] >> 16);
        iv[4 * i + 3] = (uint8_t)(IV[i] >> 24);
    }
    int count = 0;
    for (unsigned c = 0; c < sizeof OFFICIAL / sizeof *OFFICIAL; c++) {
        if (check_one(input, OFFICIAL[c].len, iv, 0, OFFICIAL[c].hash)) return 1;
        count++;
        if (OFFICIAL[c].keyed) {
            if (check_one(input, OFFICIAL[c].len, (const uint8_t *)KEY, 16, OFFICIAL[c].keyed)) return 1;
            count++;
        }
    }
    // Sweep every length 0..66 and key chunk/subtree boundaries up to 65537 in both modes.
    for (size_t len = 0; len <= 66; len++) {
        if (check_one(input, len, iv, 0, NULL)) return 1;
        if (check_one(input, len, (const uint8_t *)KEY, 16, NULL)) return 1;
        count += 2;
    }
    static const size_t BOUNDS[] = {
        127, 128, 129, 255, 256, 257, 511, 512, 513, 1022, 1023, 1024, 1025, 1026,
        2047, 2048, 2049, 3071, 3072, 3073, 4095, 4096, 4097, 7167, 7168, 7169,
        8191, 8192, 8193, 16383, 16384, 16385, 32767, 32768, 32769, 65535, 65536, 65537
    };
    for (unsigned i = 0; i < sizeof BOUNDS / sizeof *BOUNDS; i++) {
        if (check_one(input, BOUNDS[i], iv, 0, NULL)) return 1;
        if (check_one(input, BOUNDS[i], (const uint8_t *)KEY, 16, NULL)) return 1;
        count += 2;
    }
    printf("b3l_hashr_arm64: %d vectors + boundaries same (up to 102400 bytes, plain + keyed)\n", count);
    return 0;
}
"""


@unittest.skipUnless(shutil.which("lake"), "Lean's `lake` is not installed here")
class FullAArch64Hash(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        built.built("odeprove")
        cls.tmp = tempfile.TemporaryDirectory()
        cls.fns = build_all(cls.tmp.name)
        cls.spec = full_spec_text()

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def test_all_6_functions_368_instructions_shown_in_one_call(self):
        lines = statement.statement(self.spec, self.fns)
        self.assertEqual(lines.count("machine arm64"), 6)
        cur, counts = None, {}
        for line in lines:
            if line.startswith("fn "):
                cur = line.split()[1]
                counts[cur] = 0
            elif line.startswith("i "):
                counts[cur] += 1
        expected = {sym: n for _, _, sym, n in FUNCTIONS}
        self.assertEqual(counts, expected)
        self.assertEqual(sum(counts.values()), 368)
        ok, said = verify_all(self.spec, self.fns)
        self.assertTrue(ok, said)
        self.assertEqual(said, "shown")

    def test_false_contracts_are_refused(self):
        cases = [
            ("b3l_hashr_arm64", "drop trace depends on len",
             once("    trace depends on len\n    stack 656 + 272 * bits(len / 1024)",
                  "    stack 656 + 272 * bits(len / 1024)")),
            ("b3l_hashr_arm64", "too-small stack base",
             once("stack 656 + 272 * bits(len / 1024)",
                  "stack 640 + 272 * bits(len / 1024)")),
            ("b3l_hashr_arm64", "drop no_overlap",
             once("contract b3l_hashr_arm64(out: 32 bytes, input: len bytes, len: number, key: 32 bytes, flags: byte) {\n    requires no_overlap(out, input, key)\n",
                  "contract b3l_hashr_arm64(out: 32 bytes, input: len bytes, len: number, key: 32 bytes, flags: byte) {\n")),
            ("b3l_subtree_arm64", "drop decreases len",
             once("    decreases len\n", "")),
            ("b3l_subtree_arm64", "too-small recursive stack step",
             once("stack 352 + 272 * bits((len - 1) / 1024)",
                  "stack 352 + 256 * bits((len - 1) / 1024)")),
            ("b3l_node_out_arm64", "drop no_overlap",
             once("    requires no_overlap(out, nd)\n", "")),
        ]
        for target, what, change in cases:
            with self.subTest(target=target, what=what):
                ok, said = verify_only(full_spec_text(change), target, self.fns)
                self.assertFalse(ok, f"false contract accepted ({what}): {said}")

    def test_mutated_machine_code_is_refused(self):
        mutations = [
            ("b3l_hashr_arm64", "root flag 8 -> 0 in single-chunk path",
             once("    x2 := 8\n    bl b3l_node_out_arm64",
                  "    x2 := 0\n    bl b3l_node_out_arm64")),
            ("b3l_subtree_arm64", "parent flag 4 -> 0",
             once("    x9 := 4\n    orr x4, flags, x9\n    bl blake3_servil_compress_in_place_arm64",
                  "    x9 := 0\n    orr x4, flags, x9\n    bl blake3_servil_compress_in_place_arm64")),
            ("b3l_chunk_node_arm64", "CHUNK_END flag 2 -> 0",
             once("  x10 := 2\n  orr x9, x9, x10",
                  "  x10 := 0\n  orr x9, x9, x10")),
            ("b3l_hashr_arm64", "forget restoring callee-saved x19",
             once("    bl b3l_node_out_arm64\n  }\n\n  x25 := saved[7]\n  x24 := saved[6]\n  x23 := saved[5]\n  x22 := saved[4]\n  x21 := saved[3]\n  x20 := saved[2]\n  x19 := saved[1]\n",
                  "    bl b3l_node_out_arm64\n  }\n\n  x25 := saved[7]\n  x24 := saved[6]\n  x23 := saved[5]\n  x22 := saved[4]\n  x21 := saved[3]\n  x20 := saved[2]\n  nop\n")),
        ]
        for target, what, mutate in mutations:
            with self.subTest(target=target, what=what):
                with tempfile.TemporaryDirectory() as d:
                    mut_fns = build_all(d, hash_override=mutate)
                    ok, said = verify_only(self.spec, target, mut_fns)
                    self.assertFalse(ok, f"mutated code accepted ({what}): {said}")

    @unittest.skipUnless(ARM_MACHINE and shutil.which("clang"),
                         "an AArch64 processor and clang are needed")
    def test_runs_official_vectors_up_to_102400_bytes_on_hardware(self):
        with tempfile.TemporaryDirectory() as d:
            asm_p = os.path.join(d, "b3hashr_arm64.S")
            c_p = os.path.join(d, "harness.c")
            exe_p = os.path.join(d, "run")
            with open(asm_p, "w") as f:
                f.write(emit_asm(self.fns))
            with open(c_p, "w") as f:
                f.write(NATIVE_HARNESS)
            subprocess.run(["clang", "-O1", "-o", exe_p, c_p, asm_p],
                           check=True, capture_output=True)
            r = subprocess.run([exe_p], check=True, capture_output=True, text=True)
            self.assertIn("b3l_hashr_arm64: 226 vectors + boundaries same", r.stdout.strip())


if __name__ == "__main__":
    unittest.main()
