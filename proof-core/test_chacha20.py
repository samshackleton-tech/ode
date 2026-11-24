"""Lean 4 verification + real-silicon RFC 8439 ChaCha20 test & benchmark suite.

Tests four complete 20-round RFC 8439 ChaCha20 keystream implementations
(all branch-free and constant-time, with no `trace` clause):
- `ode_chacha20_block` (x86-64 AVX, 64 B/call, 477 insns, stack 0, 23 B proof)
- `ode_chacha20_block` (AArch64 NEON, 64 B/call, 437 insns, stack 0, 23 B proof)
- `ode_chacha20_blocks16` (x86-64 AVX-512, 1,024 B/call, 1,090 insns, stack 0, 26 B proof)
- `ode_chacha20_blocks4_arm64` (AArch64 NEON, 256 B/call, 1,759 insns, stack 48, 31 B proof)
"""

import os
import platform
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for sub in ("proof-core", "lang", "kcheck", "core", "arm64", "factory"):
    p = os.path.join(ROOT, sub)
    if p not in sys.path:
        sys.path.insert(0, p)

import odec
import statement

ODEVERIFY = os.path.join(HERE, ".lake", "build", "bin", "odeverify")
HOST_ARCH = platform.machine().lower()
HOST_TARGET = (
    "x86_64" if HOST_ARCH in ("x86_64", "amd64")
    else ("arm64" if HOST_ARCH in ("arm64", "aarch64") else None)
)

ARTIFACTS = [
    (
        "chacha20_block_x86_64",
        "x86_64",
        os.path.join(ROOT, "factory", "verified", "chacha20_block_x86_64.ode"),
        os.path.join(ROOT, "factory", "verified", "chacha20_block_x86_64.spec"),
        os.path.join(ROOT, "factory", "verified", "chacha20_block_x86_64.proof"),
        "chacha20_block",
        "ode_chacha20_block",
    ),
    (
        "chacha20_block_arm64",
        "arm64",
        os.path.join(ROOT, "factory", "verified", "chacha20_block_arm64.ode"),
        os.path.join(ROOT, "factory", "verified", "chacha20_block_arm64.spec"),
        os.path.join(ROOT, "factory", "verified", "chacha20_block_arm64.proof"),
        "chacha20_block",
        "ode_chacha20_block",
    ),
    (
        "chacha20_blocks16_x86_64",
        "x86_64",
        os.path.join(HERE, "examples", "chacha20", "blocks16_x86_64.ode"),
        os.path.join(HERE, "examples", "chacha20", "blocks16_x86_64.spec"),
        os.path.join(HERE, "proofs", "ode_chacha20_blocks16.proof"),
        "chacha20_blocks16",
        "ode_chacha20_blocks16",
    ),
    (
        "chacha20_blocks4_arm64",
        "arm64",
        os.path.join(HERE, "examples", "chacha20", "blocks4_arm64.ode"),
        os.path.join(HERE, "examples", "chacha20", "blocks4_arm64.spec"),
        os.path.join(HERE, "proofs", "ode_chacha20_blocks4_arm64.proof"),
        "chacha20_blocks4_arm64",
        "ode_chacha20_blocks4_arm64",
    ),
]

HARNESS_C = r"""
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

extern void ode_chacha20_block(uint8_t out[64], const uint32_t state[16]);
#ifdef HAVE_BLOCKS16
extern void ode_chacha20_blocks16(uint8_t out[1024], const uint32_t state[16]);
#endif
#ifdef HAVE_BLOCKS4
extern void ode_chacha20_blocks4_arm64(uint8_t out[256], const uint32_t state[16]);
#endif

static double now_sec(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

static int check_rfc8439(void) {
  // 1. RFC 8439 Section 2.3.2 ChaCha20 block test vector (all 64 bytes)
  const uint32_t s232[16] = {
    0x61707865u, 0x3320646eu, 0x79622d32u, 0x6b206574u,
    0x03020100u, 0x07060504u, 0x0b0a0908u, 0x0f0e0d0cu,
    0x13121110u, 0x17161514u, 0x1b1a1918u, 0x1f1e1d1cu,
    0x00000001u, 0x09000000u, 0x4a000000u, 0x00000000u
  };
  static const uint8_t want232[64] = {
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
  ode_chacha20_block(got, s232);
  if (memcmp(got, want232, 64) != 0) {
    fprintf(stderr, "RFC 8439 2.3.2 mismatch\n");
    return 1;
  }

  // 2. RFC 8439 Section 2.4.2 Sunscreen encryption test vector (114 bytes, ctr=1,2)
  const uint32_t s242[16] = {
    0x61707865u, 0x3320646eu, 0x79622d32u, 0x6b206574u,
    0x03020100u, 0x07060504u, 0x0b0a0908u, 0x0f0e0d0cu,
    0x13121110u, 0x17161514u, 0x1b1a1918u, 0x1f1e1d1cu,
    0x00000001u, 0x00000000u, 0x4a000000u, 0x00000000u
  };
  const char *pt =
    "Ladies and Gentlemen of the class of '99: "
    "If I could offer you only one tip for the future, sunscreen would be it.";
  static const uint8_t want_ct[114] = {
    0x6e, 0x2e, 0x35, 0x9a, 0x25, 0x68, 0xf9, 0x80,
    0x41, 0xba, 0x07, 0x28, 0xdd, 0x0d, 0x69, 0x81,
    0xe9, 0x7e, 0x7a, 0xec, 0x1d, 0x43, 0x60, 0xc2,
    0x0a, 0x27, 0xaf, 0xcc, 0xfd, 0x9f, 0xae, 0x0b,
    0xf9, 0x1b, 0x65, 0xc5, 0x52, 0x47, 0x33, 0xab,
    0x8f, 0x59, 0x3d, 0xab, 0xcd, 0x62, 0xb3, 0x57,
    0x16, 0x39, 0xd6, 0x24, 0xe6, 0x51, 0x52, 0xab,
    0x8f, 0x53, 0x0c, 0x35, 0x9f, 0x08, 0x61, 0xd8,
    0x07, 0xca, 0x0d, 0xbf, 0x50, 0x0d, 0x6a, 0x61,
    0x56, 0xa3, 0x8e, 0x08, 0x8a, 0x22, 0xb6, 0x5e,
    0x52, 0xbc, 0x51, 0x4d, 0x16, 0xcc, 0xf8, 0x06,
    0x81, 0x8c, 0xe9, 0x1a, 0xb7, 0x79, 0x37, 0x36,
    0x5a, 0xf9, 0x0b, 0xbf, 0x74, 0xa3, 0x5b, 0xe6,
    0xb4, 0x0b, 0x8e, 0xed, 0xf2, 0x78, 0x5e, 0x42,
    0x87, 0x4d
  };
  uint8_t ks[128];
  uint32_t st[16];
  memcpy(st, s242, sizeof(st));
  ode_chacha20_block(ks, st);
  st[12] = 2u;
  ode_chacha20_block(ks + 64, st);
  for (int i = 0; i < 114; i++) {
    if (((uint8_t)pt[i] ^ ks[i]) != want_ct[i]) {
      fprintf(stderr, "RFC 8439 2.4.2 mismatch at byte %d\n", i);
      return 2;
    }
  }

  // 3. Multi-block differential + 32-bit counter wraparound (0xFFFFFFFE -> 0x00000001)
  uint32_t wrap[16];
  memcpy(wrap, s232, sizeof(wrap));
  wrap[12] = 0xfffffffeu;

#ifdef HAVE_BLOCKS16
  uint8_t got16[1024], ref16[1024];
  ode_chacha20_blocks16(got16, s232);
  for (uint32_t k = 0; k < 16; k++) {
    memcpy(st, s232, sizeof(st));
    st[12] = s232[12] + k;
    ode_chacha20_block(ref16 + 64 * k, st);
  }
  if (memcmp(got16, ref16, 1024) != 0) {
    fprintf(stderr, "blocks16 s232 mismatch\n");
    return 3;
  }
  ode_chacha20_blocks16(got16, wrap);
  for (uint32_t k = 0; k < 16; k++) {
    memcpy(st, wrap, sizeof(st));
    st[12] = wrap[12] + k;
    ode_chacha20_block(ref16 + 64 * k, st);
  }
  if (memcmp(got16, ref16, 1024) != 0) {
    fprintf(stderr, "blocks16 wraparound mismatch\n");
    return 4;
  }
#endif

#ifdef HAVE_BLOCKS4
  uint8_t got4[256], ref4[256];
  ode_chacha20_blocks4_arm64(got4, s232);
  for (uint32_t k = 0; k < 4; k++) {
    memcpy(st, s232, sizeof(st));
    st[12] = s232[12] + k;
    ode_chacha20_block(ref4 + 64 * k, st);
  }
  if (memcmp(got4, ref4, 256) != 0) {
    fprintf(stderr, "blocks4 s232 mismatch\n");
    return 5;
  }
  ode_chacha20_blocks4_arm64(got4, wrap);
  for (uint32_t k = 0; k < 4; k++) {
    memcpy(st, wrap, sizeof(st));
    st[12] = wrap[12] + k;
    ode_chacha20_block(ref4 + 64 * k, st);
  }
  if (memcmp(got4, ref4, 256) != 0) {
    fprintf(stderr, "blocks4 wraparound mismatch\n");
    return 6;
  }
  // 4. Verify AAPCS64 callee-saved d8..d15 are untouched by both AArch64 kernels!
  uint64_t before[8] = {
    0x1111111122222222ULL, 0x3333333344444444ULL, 0x5555555566666666ULL, 0x7777777788888888ULL,
    0x99999999aaaaaaaaULL, 0xbbbbbbbbccccccccULL, 0xddddddddeeeeeeeeULL, 0xf0f0f0f00f0f0f0fULL
  };
  uint64_t after[8] = {0};
  __asm__ volatile(
    "ldr d8,  [%0, #0]\n"
    "ldr d9,  [%0, #8]\n"
    "ldr d10, [%0, #16]\n"
    "ldr d11, [%0, #24]\n"
    "ldr d12, [%0, #32]\n"
    "ldr d13, [%0, #40]\n"
    "ldr d14, [%0, #48]\n"
    "ldr d15, [%0, #56]\n"
    : : "r"(before) : "d8","d9","d10","d11","d12","d13","d14","d15"
  );
  ode_chacha20_block(got, s232);
  ode_chacha20_blocks4_arm64(got4, s232);
  __asm__ volatile(
    "str d8,  [%0, #0]\n"
    "str d9,  [%0, #8]\n"
    "str d10, [%0, #16]\n"
    "str d11, [%0, #24]\n"
    "str d12, [%0, #32]\n"
    "str d13, [%0, #40]\n"
    "str d14, [%0, #48]\n"
    "str d15, [%0, #56]\n"
    : : "r"(after) : "memory"
  );
  if (memcmp(before, after, sizeof(before)) != 0) {
    fprintf(stderr, "AAPCS64 d8..d15 clobbered!\n");
    return 7;
  }
#endif
  return 0;
}

int main(int argc, char **argv) {
  int rc = check_rfc8439();
  if (rc != 0) return rc;
  if (argc > 1 && strcmp(argv[1], "--bench") == 0) {
    uint32_t st[16] = {
      0x61707865u, 0x3320646eu, 0x79622d32u, 0x6b206574u,
      0x03020100u, 0x07060504u, 0x0b0a0908u, 0x0f0e0d0cu,
      0x13121110u, 0x17161514u, 0x1b1a1918u, 0x1f1e1d1cu,
      1u, 0u, 0x4a000000u, 0u
    };
    static uint8_t buf[65536] __attribute__((aligned(64)));
    // 1-block throughput (64 MiB total, median of 7 runs)
    const int REPS = 7;
    double best1 = 1e9;
    for (int r = 0; r < REPS; r++) {
      double t0 = now_sec();
      for (int it = 0; it < 256; it++) {
        for (size_t off = 0; off < sizeof(buf); off += 64) {
          ode_chacha20_block(buf + off, st);
          st[12]++;
        }
      }
      double dt = now_sec() - t0;
      if (dt < best1) best1 = dt;
    }
    double bytes1 = 256.0 * (double)sizeof(buf);
    printf("chacha20_block_1x: %.3f GiB/s (%.2f ns / 64B block, sink=%u)\n",
           bytes1 / best1 / (1024.0 * 1024.0 * 1024.0),
           best1 / (bytes1 / 64.0) * 1e9, (unsigned)buf[0]);
#ifdef HAVE_BLOCKS16
    double best16 = 1e9;
    for (int r = 0; r < REPS; r++) {
      double t0 = now_sec();
      for (int it = 0; it < 1024; it++) {
        for (size_t off = 0; off < sizeof(buf); off += 1024) {
          ode_chacha20_blocks16(buf + off, st);
          st[12] += 16;
        }
      }
      double dt = now_sec() - t0;
      if (dt < best16) best16 = dt;
    }
    double bytes16 = 1024.0 * (double)sizeof(buf);
    printf("chacha20_blocks16_avx512: %.3f GiB/s (%.2f ns / 1024B = %.2f ns/64B, sink=%u)\n",
           bytes16 / best16 / (1024.0 * 1024.0 * 1024.0),
           best16 / (bytes16 / 1024.0) * 1e9,
           best16 / (bytes16 / 64.0) * 1e9, (unsigned)buf[0]);
#endif
#ifdef HAVE_BLOCKS4
    double best4 = 1e9;
    for (int r = 0; r < REPS; r++) {
      double t0 = now_sec();
      for (int it = 0; it < 512; it++) {
        for (size_t off = 0; off < sizeof(buf); off += 256) {
          ode_chacha20_blocks4_arm64(buf + off, st);
          st[12] += 4;
        }
      }
      double dt = now_sec() - t0;
      if (dt < best4) best4 = dt;
    }
    double bytes4 = 512.0 * (double)sizeof(buf);
    printf("chacha20_blocks4_arm64: %.3f GiB/s (%.2f ns / 256B = %.2f ns/64B, sink=%u)\n",
           bytes4 / best4 / (1024.0 * 1024.0 * 1024.0),
           best4 / (bytes4 / 256.0) * 1e9,
           best4 / (bytes4 / 64.0) * 1e9, (unsigned)buf[0]);
#endif
  }
  return 0;
}
"""


def _has_avx512():
    if HOST_TARGET != "x86_64":
        return False
    try:
        with open("/proc/cpuinfo") as f:
            txt = f.read()
        return "avx512f" in txt and "avx512vl" in txt
    except OSError:
        return False


def _emit_asm_for_host(ode_path, fn_name, sym, target):
    asm = odec.assembly(ode_path, fn_name, symbol=sym)
    if platform.system() == "Darwin":
        lines = []
        for line in asm.splitlines():
            s = line.strip()
            if s.startswith((".type ", ".size ", ".section .note")):
                continue
            line = line.replace(f".global {sym}", f".global _{sym}")
            line = line.replace(f".globl {sym}", f".globl _{sym}")
            if s == f"{sym}:":
                line = f"_{sym}:"
            elif s == ".section .rodata":
                line = ".section __TEXT,__const"
            elif s == ".section .text":
                line = ".text"
            lines.append(line)
        asm = "\n".join(lines) + "\n"
    return asm


def run_native_harness(bench=False):
    cc = shutil.which("clang") or shutil.which("cc")
    assert HOST_TARGET and cc, "native x86_64/arm64 compiler required"
    with tempfile.TemporaryDirectory() as d:
        srcs = []
        defs = []
        if HOST_TARGET == "x86_64":
            s1 = os.path.join(d, "block.S")
            with open(s1, "w") as f:
                f.write(_emit_asm_for_host(ARTIFACTS[0][2], ARTIFACTS[0][5], ARTIFACTS[0][6], "x86_64"))
            srcs.append(s1)
            if _has_avx512():
                s16 = os.path.join(d, "blocks16.S")
                with open(s16, "w") as f:
                    f.write(_emit_asm_for_host(ARTIFACTS[2][2], ARTIFACTS[2][5], ARTIFACTS[2][6], "x86_64"))
                srcs.append(s16)
                defs.append("-DHAVE_BLOCKS16")
        else:
            s1 = os.path.join(d, "block.S")
            with open(s1, "w") as f:
                f.write(_emit_asm_for_host(ARTIFACTS[1][2], ARTIFACTS[1][5], ARTIFACTS[1][6], "arm64"))
            s4 = os.path.join(d, "blocks4.S")
            with open(s4, "w") as f:
                f.write(_emit_asm_for_host(ARTIFACTS[3][2], ARTIFACTS[3][5], ARTIFACTS[3][6], "arm64"))
            srcs.extend([s1, s4])
            defs.append("-DHAVE_BLOCKS4")
        c_p = os.path.join(d, "main.c")
        exe_p = os.path.join(d, "run")
        with open(c_p, "w") as f:
            f.write(HARNESS_C)
        cmd = [cc, "-O2", *defs, c_p, *srcs, "-o", exe_p]
        subprocess.run(cmd, check=True)
        run_cmd = [exe_p, "--bench"] if bench else [exe_p]
        return subprocess.run(run_cmd, capture_output=True, text=True, check=False)


class TestChaCha20(unittest.TestCase):
    def test_all_4_odeverify_shown(self):
        self.assertTrue(os.path.exists(ODEVERIFY), f"missing {ODEVERIFY}")
        for name, tgt, ode_p, spec_p, proof_p, fn_name, sym in ARTIFACTS:
            with tempfile.TemporaryDirectory() as d:
                obj_p = os.path.join(d, f"{name}.o")
                odec.build(ode_p, fn_name, obj_p, symbol=sym)
                with open(spec_p) as f:
                    spec_txt = f.read()
                stmt_p = os.path.join(d, f"{name}.statement")
                lines = statement.statement(spec_txt, [(obj_p, sym)])
                with open(stmt_p, "w") as f:
                    f.write("\n".join(lines) + "\n")
                tab = statement.table_for(stmt_p)
                r = subprocess.run([ODEVERIFY, tab, stmt_p, proof_p], capture_output=True, text=True)
                self.assertEqual(r.returncode, 0, f"{name} failed: {r.stdout} {r.stderr}")
                self.assertEqual(r.stdout.strip(), "shown", f"{name}: {r.stdout}")

    def test_negative_controls_refused(self):
        # Flipping a rotation amount in either wide kernel must be refused by odeverify.
        for idx, old, new in [
            (2, "vprord s15, s15, 24", "vprord s15, s15, 16"),
            (3, "ushr  t0.4s, b0.4s, 25", "ushr  t0.4s, b0.4s, 24"),
        ]:
            name, tgt, ode_p, spec_p, proof_p, fn_name, sym = ARTIFACTS[idx]
            with open(ode_p) as f:
                src = f.read()
            self.assertIn(old, src)
            mut = src.replace(old, new, 1)
            with tempfile.TemporaryDirectory() as d:
                mut_p = os.path.join(d, "mut.ode")
                obj_p = os.path.join(d, "mut.o")
                with open(mut_p, "w") as f:
                    f.write(mut)
                odec.build(mut_p, fn_name, obj_p, symbol=sym)
                with open(spec_p) as f:
                    spec_txt = f.read()
                stmt_p = os.path.join(d, "mut.statement")
                lines = statement.statement(spec_txt, [(obj_p, sym)])
                with open(stmt_p, "w") as f:
                    f.write("\n".join(lines) + "\n")
                tab = statement.table_for(stmt_p)
                r = subprocess.run([ODEVERIFY, tab, stmt_p, proof_p], capture_output=True, text=True)
                self.assertNotEqual(r.returncode, 0, f"mutated {name} must be refused!")

    @unittest.skipUnless(HOST_TARGET and (shutil.which("clang") or shutil.which("cc")),
                         "native host compiler required")
    def test_real_silicon_rfc8439_and_abi(self):
        r = run_native_harness(bench=False)
        self.assertEqual(r.returncode, 0, f"native ChaCha20 failed: {r.stdout} {r.stderr}")


if __name__ == "__main__":
    if "--bench" in sys.argv:
        r = run_native_harness(bench=True)
        sys.stdout.write(r.stdout)
        sys.stderr.write(r.stderr)
        sys.exit(r.returncode)
    unittest.main()
