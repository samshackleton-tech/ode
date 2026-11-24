#!/usr/bin/env python3
"""Real-silicon interleaved paired benchmark for the Performance-Modeling A/B Experiment.

Runs on x86-64 Linux (Zen 5 via pinned-run) or AArch64 macOS/Linux (Apple M6).
For every unique selected verified candidate from `perf-results-20261124.jsonl`,
compiles BOTH the Wave 1 baseline (`base_fn`) and the candidate (`cand_fn`) into one
native C executable, verifies 100% identical outputs across the benchmark corpus,
then runs 15 alternating paired trials (base vs cand) and writes exact median
nanoseconds/call and speedup (`base_ns / cand_ns`) to JSON.
"""

import argparse
import glob
import json
import os
import platform
import re
import shutil
import statistics
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path[:0] = [
    os.path.join(ROOT, "lang"),
    os.path.join(ROOT, "arm64"),
    os.path.join(ROOT, "kcheck"),
    os.path.join(ROOT, "proof-core"),
]

import obj as aobj
import odec

VERIFIED_DIR = os.path.join(ROOT, "factory", "verified")
RESULTS_JSONL = os.path.join(ROOT, "paper", "coder-exp", "perf-results-20261124.jsonl")
CAND_DIR = os.path.join(ROOT, "paper", "coder-exp", "perf-candidates")

HOST_ARCH = platform.machine().lower()
HOST_TARGET = (
    "x86_64" if HOST_ARCH in ("x86_64", "amd64")
    else ("arm64" if HOST_ARCH in ("arm64", "aarch64") else None)
)

C_BENCH = {
    "base64_char_val": r"""
#include <stdint.h>
#include <stdio.h>
#include <time.h>
extern uint64_t base_fn(uint64_t b);
extern uint64_t cand_fn(uint64_t b);
static double now_ns(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec * 1e9 + (double)ts.tv_nsec;
}
int main(void) {
  // Correctness check on all 256 byte values
  for (uint64_t b = 0; b < 256; b++) {
    if (base_fn(b) != cand_fn(b)) { fprintf(stderr, "mismatch at %llu\n", (unsigned long long)b); return 1; }
  }
  // Pseudo-random shuffled byte order (mix of A-Z, a-z, 0-9, +, /, invalid)
  uint8_t inputs[256];
  for (int i = 0; i < 256; i++) inputs[i] = (uint8_t)((i * 73 + 19) & 255);
  const int sweeps = 20000;
  const int trials = 15;
  volatile uint64_t sink = 0;
  // Warmup
  for (int w = 0; w < 1000; w++) { sink ^= base_fn(inputs[w & 255]); sink ^= cand_fn(inputs[w & 255]); }
  for (int t = 0; t < trials; t++) {
    double t0, t1, t2, t3;
    uint64_t a = 0, c = 0;
    if ((t & 1) == 0) {
      t0 = now_ns();
      for (int s = 0; s < sweeps; s++) for (int i = 0; i < 256; i++) a += base_fn(inputs[i]);
      t1 = now_ns();
      t2 = now_ns();
      for (int s = 0; s < sweeps; s++) for (int i = 0; i < 256; i++) c += cand_fn(inputs[i]);
      t3 = now_ns();
    } else {
      t2 = now_ns();
      for (int s = 0; s < sweeps; s++) for (int i = 0; i < 256; i++) c += cand_fn(inputs[i]);
      t3 = now_ns();
      t0 = now_ns();
      for (int s = 0; s < sweeps; s++) for (int i = 0; i < 256; i++) a += base_fn(inputs[i]);
      t1 = now_ns();
    }
    if (a != c) return 2;
    sink ^= a;
    printf("%.6f %.6f\n", (t1 - t0) / ((double)sweeps * 256.0), (t3 - t2) / ((double)sweeps * 256.0));
  }
  return 0;
}
""",
    "der_tlv_len": r"""
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
extern uint64_t base_fn(const uint8_t *buf, uint64_t n);
extern uint64_t cand_fn(const uint8_t *buf, uint64_t n);
static double now_ns(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec * 1e9 + (double)ts.tv_nsec;
}
int main(void) {
  static uint8_t bufs[16][300];
  static uint64_t lens[16];
  // 16 realistic DER TLV inputs (short valid, 1-byte long, 2-byte long, malformed)
  memset(bufs, 0, sizeof(bufs));
  uint8_t c0[] = {0x02, 0x01, 0x05}; memcpy(bufs[0], c0, 3); lens[0] = 3;
  uint8_t c1[] = {0x05, 0x00}; memcpy(bufs[1], c1, 2); lens[1] = 2;
  uint8_t c2[] = {0x04, 0x10}; memcpy(bufs[2], c2, 2); lens[2] = 18;
  uint8_t c3[] = {0x30, 0x20}; memcpy(bufs[3], c3, 2); lens[3] = 34;
  uint8_t c4[] = {0x06, 0x09}; memcpy(bufs[4], c4, 2); lens[4] = 11;
  uint8_t c5[] = {0x04, 0x81, 0x80}; memcpy(bufs[5], c5, 3); lens[5] = 131;
  uint8_t c6[] = {0x30, 0x81, 0xc8}; memcpy(bufs[6], c6, 3); lens[6] = 203;
  uint8_t c7[] = {0x30, 0x82, 0x01, 0x00}; memcpy(bufs[7], c7, 4); lens[7] = 260;
  uint8_t c8[] = {0x30, 0x80, 0x00, 0x00}; memcpy(bufs[8], c8, 4); lens[8] = 4;      // indefinite
  uint8_t c9[] = {0x04, 0x81, 0x7f}; memcpy(bufs[9], c9, 3); lens[9] = 130;          // non-minimal
  uint8_t c10[] = {0x04, 0x82, 0x00, 0xff}; memcpy(bufs[10], c10, 4); lens[10] = 260;// leading-zero
  uint8_t c11[] = {0x1f, 0x01, 0x00}; memcpy(bufs[11], c11, 3); lens[11] = 3;        // tag31
  uint8_t c12[] = {0x02, 0x05, 0x01}; memcpy(bufs[12], c12, 3); lens[12] = 3;        // truncated
  uint8_t c13[] = {0x30, 0x7f}; memcpy(bufs[13], c13, 2); lens[13] = 129;            // max short
  uint8_t c14[] = {0x02, 0x00}; memcpy(bufs[14], c14, 2); lens[14] = 1;              // too short
  uint8_t c15[] = {0x30, 0x83, 0x01, 0x00, 0x00}; memcpy(bufs[15], c15, 5); lens[15] = 5; // 3B len
  for (int i = 0; i < 16; i++) {
    if (base_fn(bufs[i], lens[i]) != cand_fn(bufs[i], lens[i])) return 1;
  }
  const int sweeps = 200000;
  const int trials = 15;
  volatile uint64_t sink = 0;
  for (int w = 0; w < 2000; w++) { sink ^= base_fn(bufs[w & 15], lens[w & 15]); sink ^= cand_fn(bufs[w & 15], lens[w & 15]); }
  for (int t = 0; t < trials; t++) {
    double t0, t1, t2, t3;
    uint64_t a = 0, c = 0;
    if ((t & 1) == 0) {
      t0 = now_ns();
      for (int s = 0; s < sweeps; s++) for (int i = 0; i < 16; i++) a += base_fn(bufs[i], lens[i]);
      t1 = now_ns();
      t2 = now_ns();
      for (int s = 0; s < sweeps; s++) for (int i = 0; i < 16; i++) c += cand_fn(bufs[i], lens[i]);
      t3 = now_ns();
    } else {
      t2 = now_ns();
      for (int s = 0; s < sweeps; s++) for (int i = 0; i < 16; i++) c += cand_fn(bufs[i], lens[i]);
      t3 = now_ns();
      t0 = now_ns();
      for (int s = 0; s < sweeps; s++) for (int i = 0; i < 16; i++) a += base_fn(bufs[i], lens[i]);
      t1 = now_ns();
    }
    if (a != c) return 2;
    sink ^= a;
    printf("%.6f %.6f\n", (t1 - t0) / ((double)sweeps * 16.0), (t3 - t2) / ((double)sweeps * 16.0));
  }
  return 0;
}
""",
    "sha256_big_sigma_4x": r"""
#include <stdint.h>
#include <stdio.h>
#include <time.h>
extern void base_fn(uint32_t *out, const uint32_t *a, const uint32_t *e);
extern void cand_fn(uint32_t *out, const uint32_t *a, const uint32_t *e);
static double now_ns(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec * 1e9 + (double)ts.tv_nsec;
}
int main(void) {
  uint32_t a[4] = {0x6a09e667u, 0xbb67ae85u, 0x510e527fu, 0x00000001u};
  uint32_t e[4] = {0x510e527fu, 0x9b05688cu, 0x1f83d9abu, 0x5be0cd19u};
  uint32_t o1[4] = {0}, o2[4] = {0};
  base_fn(o1, a, e); cand_fn(o2, a, e);
  for (int i = 0; i < 4; i++) if (o1[i] != o2[i]) return 1;
  const int iters = 500000;
  const int trials = 15;
  volatile uint32_t sink = 0;
  // Dependent chain (measures real latency / critical path)
  for (int t = 0; t < trials; t++) {
    double t0, t1, t2, t3;
    uint32_t x1[4] = {a[0], a[1], a[2], a[3]};
    uint32_t x2[4] = {a[0], a[1], a[2], a[3]};
    uint32_t tmp[4];
    if ((t & 1) == 0) {
      t0 = now_ns();
      for (int s = 0; s < iters; s++) { base_fn(tmp, x1, e); x1[0] = tmp[0]; x1[1] = tmp[1]; x1[2] = tmp[2]; x1[3] = tmp[3]; }
      t1 = now_ns();
      t2 = now_ns();
      for (int s = 0; s < iters; s++) { cand_fn(tmp, x2, e); x2[0] = tmp[0]; x2[1] = tmp[1]; x2[2] = tmp[2]; x2[3] = tmp[3]; }
      t3 = now_ns();
    } else {
      t2 = now_ns();
      for (int s = 0; s < iters; s++) { cand_fn(tmp, x2, e); x2[0] = tmp[0]; x2[1] = tmp[1]; x2[2] = tmp[2]; x2[3] = tmp[3]; }
      t3 = now_ns();
      t0 = now_ns();
      for (int s = 0; s < iters; s++) { base_fn(tmp, x1, e); x1[0] = tmp[0]; x1[1] = tmp[1]; x1[2] = tmp[2]; x1[3] = tmp[3]; }
      t1 = now_ns();
    }
    if (x1[0] != x2[0] || x1[3] != x2[3]) return 2;
    sink ^= x1[0];
    printf("%.6f %.6f\n", (t1 - t0) / (double)iters, (t3 - t2) / (double)iters);
  }
  return 0;
}
""",
    "adler32_s1": r"""
#include <stdint.h>
#include <stdio.h>
#include <time.h>
extern uint64_t base_fn(const uint8_t *buf, uint64_t n);
extern uint64_t cand_fn(const uint8_t *buf, uint64_t n);
static double now_ns(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec * 1e9 + (double)ts.tv_nsec;
}
int main(void) {
  static uint8_t buf[4096];
  for (int i = 0; i < 4096; i++) buf[i] = (uint8_t)((i * 131 + 17) & 255);
  if (base_fn(buf, 4096) != cand_fn(buf, 4096)) return 1;
  if (base_fn(buf, 0) != cand_fn(buf, 0)) return 1;
  if (base_fn(buf, 777) != cand_fn(buf, 777)) return 1;
  const int iters = 10000;
  const int trials = 15;
  volatile uint64_t sink = 0;
  for (int w = 0; w < 200; w++) { sink ^= base_fn(buf, 4096); sink ^= cand_fn(buf, 4096); }
  for (int t = 0; t < trials; t++) {
    double t0, t1, t2, t3;
    uint64_t a = 0, c = 0;
    if ((t & 1) == 0) {
      t0 = now_ns();
      for (int s = 0; s < iters; s++) a += base_fn(buf, 4096);
      t1 = now_ns();
      t2 = now_ns();
      for (int s = 0; s < iters; s++) c += cand_fn(buf, 4096);
      t3 = now_ns();
    } else {
      t2 = now_ns();
      for (int s = 0; s < iters; s++) c += cand_fn(buf, 4096);
      t3 = now_ns();
      t0 = now_ns();
      for (int s = 0; s < iters; s++) a += base_fn(buf, 4096);
      t1 = now_ns();
    }
    if (a != c) return 2;
    sink ^= a;
    printf("%.6f %.6f\n", (t1 - t0) / (double)iters, (t3 - t2) / (double)iters);
  }
  return 0;
}
""",
}


def compile_renamed(ode_p, new_sym, out_dir, target):
    """Compile an `.ode` single-function file, renaming its exported symbol to `new_sym`."""
    with open(ode_p) as f:
        src = f.read()
    # Replace `as "ode_..."` with `as "<new_sym>"`
    src2 = re.sub(r'as\s+"[^"]+"', f'as "{new_sym}"', src, count=1)
    assert src2 != src, f"could not rename symbol in {ode_p}"
    tmp_ode = os.path.join(out_dir, f"{new_sym}.ode")
    with open(tmp_ode, "w") as f:
        f.write(src2)
    _, _, _, fns = odec.source(src2, tmp_ode)
    assert len(fns) == 1, f"expected 1 fn in {ode_p}, got {len(fns)}"
    fn_name = fns[0][0]
    obj_p = os.path.join(out_dir, f"{new_sym}.o")
    odec.build(tmp_ode, fn_name, obj_p)
    if target == "arm64":
        e = aobj.Elf(obj_p)
        shndx, value, size, at = aobj.place(e, new_sym)
        code = e.b[at:at + size]
        s_p = os.path.join(out_dir, f"{new_sym}.S")
        lines = [
            "#ifdef __APPLE__",
            f".globl _{new_sym}",
            ".p2align 6",
            f"_{new_sym}:",
            "#else",
            f".globl {new_sym}",
            ".p2align 6",
            f"{new_sym}:",
            "#endif",
        ]
        for off in range(0, size, 4):
            w = int.from_bytes(code[off:off + 4], "little")
            lines.append(f"  .word 0x{w:08x}")
        with open(s_p, "w") as f:
            f.write("\n".join(lines) + "\n")
        return s_p
    return obj_p


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--out", required=True)
    p.add_argument("--target", default=HOST_TARGET)
    args = p.parse_args()
    target = args.target
    assert target in ("x86_64", "arm64"), f"unsupported host target {target}"
    cc = shutil.which("clang") or shutil.which("cc")
    assert cc, "no C compiler found"

    with open(RESULTS_JSONL) as f:
        recs = [json.loads(l) for l in f if l.strip()]

    cand_map = {}
    for cp in sorted(glob.glob(os.path.join(CAND_DIR, "*.ode"))):
        parts = os.path.basename(cp)[:-4].split("__")
        cand_map.setdefault((parts[0], parts[-1]), cp)

    unique = {}
    for r in recs:
        if r["target"] != target:
            continue
        s = r.get("selected")
        if s and s["changed"]:
            tid = f"{r['rid']}_{target}"
            key = (r["rid"], s["hash"])
            if key not in unique:
                unique[key] = {
                    "rid": r["rid"], "target": target, "hash": s["hash"],
                    "cand_path": cand_map[(tid, s["hash"])],
                    "base_whole": r["base_whole"], "cand_whole": s["whole"],
                }

    print(f"Benchmarking {len(unique)} unique verified {target} candidates on {platform.machine()}...", flush=True)
    results = []
    for (rid, h), info in sorted(unique.items()):
        base_ode = os.path.join(VERIFIED_DIR, f"{rid}_{target}.ode")
        with tempfile.TemporaryDirectory(prefix=f"perf_b_{rid}_") as td:
            bf = compile_renamed(base_ode, "base_fn", td, target)
            cf = compile_renamed(info["cand_path"], "cand_fn", td, target)
            c_p = os.path.join(td, "bench.c")
            exe_p = os.path.join(td, "bench")
            with open(c_p, "w") as f:
                f.write(C_BENCH[rid])
            subprocess.run([cc, "-O2", c_p, bf, cf, "-o", exe_p], check=True)
            run = subprocess.run([exe_p], capture_output=True, text=True, check=True)
            bs, cs = [], []
            for line in run.stdout.strip().splitlines():
                b_ns, c_ns = map(float, line.split())
                bs.append(b_ns); cs.append(c_ns)
            b_med = statistics.median(bs)
            c_med = statistics.median(cs)
            sp = b_med / c_med
            pred_sp = info["base_whole"]["compute_lower_bound"] / info["cand_whole"]["compute_lower_bound"]
            row = {
                "rid": rid, "target": target, "hash": h,
                "base_ns": round(b_med, 4), "cand_ns": round(c_med, 4),
                "speedup": round(sp, 4), "pred_speedup": round(pred_sp, 4),
                "base_lb": info["base_whole"]["compute_lower_bound"],
                "cand_lb": info["cand_whole"]["compute_lower_bound"],
                "base_ins": info["base_whole"]["instructions"],
                "cand_ins": info["cand_whole"]["instructions"],
            }
            results.append(row)
            print(
                f"  {rid:20s} {h} | base={b_med:8.3f}ns cand={c_med:8.3f}ns | "
                f"speedup={sp:5.3f}x (pred {pred_sp:5.3f}x, lb {row['base_lb']}->{row['cand_lb']}, ins {row['base_ins']}->{row['cand_ins']})",
                flush=True,
            )

    with open(args.out, "w") as f:
        json.dump({"target": target, "machine": platform.machine(), "results": results}, f, indent=2)
    print(f"Saved {len(results)} timing results to {args.out}", flush=True)


if __name__ == "__main__":
    main()
