#!/usr/bin/env python3
"""advice/pmu_validate_arm64.py: bare-metal AArch64 + NEON hardware pipeline validation
suite for `advice/uica_sim.py` vs. `advice/estimate.py` vs. `llvm-mca`.

Assembles 30 AArch64 loop kernels (7 exact latency probes + 9 targeted pipeline probes +
4 real Ode kernels + 10 reproducible randomized instruction-mix loops) directly through
`lang/odec.py` and `arm64/arm64.tab`, extracts their exact 32-bit machine-code words, and
with `--run` measures hardware cycles per iteration on either:
  - Linux AArch64 (`perf_event_open` PERF_COUNT_HW_CPU_CYCLES when available, else
    self-calibrated interleaved `add`-chain reference via `CLOCK_MONOTONIC_RAW`), or
  - macOS Apple Silicon (`QOS_CLASS_USER_INTERACTIVE` + interleaved `add`-chain reference
    via `CLOCK_UPTIME_RAW`, verified against an independent `orr`-chain cross-check).

Strictly advisory — never imported or relied on by `proof-core/odeverify`.
"""
import argparse, json, os, platform, random, re, statistics, struct, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for d in (HERE, os.path.join(ROOT, "lang"), os.path.join(ROOT, "core"), os.path.join(ROOT, "arm64"), os.path.join(ROOT, "kcheck")):
    if d not in sys.path:
        sys.path.insert(0, d)
import estimate, obj as arm_obj, odec, table, uica_sim

# All kernels follow AArch64 C ABI: `uint64_t fn(uint64_t iters, uint8_t *buf)`
# where x0 = iters, x1 = buf (4096 B, 64B aligned).
# Strictly caller-saved registers only: GPRs x2..x15, NEON v0..v7 and v16..v23 (never callee-saved v8..v15!).

LATENCY_PROBES = [
    ("lat_add_gpr", 16.0, """target arm64
fn lat_add_gpr as "k_lat_add_gpr" {
  mov x3, 1
  mov x4, 3
  mov x2, 0
@lp:
  add x3, x3, x4
  add x3, x3, x4
  add x3, x3, x4
  add x3, x3, x4
  add x3, x3, x4
  add x3, x3, x4
  add x3, x3, x4
  add x3, x3, x4
  add x3, x3, x4
  add x3, x3, x4
  add x3, x3, x4
  add x3, x3, x4
  add x3, x3, x4
  add x3, x3, x4
  add x3, x3, x4
  add x3, x3, x4
  add x2, x2, 1
  cmp x2, x0
  b.lo @lp
  mov x0, x3
  ret
}
"""),
    ("lat_orr_gpr", 16.0, """target arm64
fn lat_orr_gpr as "k_lat_orr_gpr" {
  mov x3, 1
  mov x4, 3
  mov x2, 0
@lp:
  orr x3, x3, x4
  orr x3, x3, x4
  orr x3, x3, x4
  orr x3, x3, x4
  orr x3, x3, x4
  orr x3, x3, x4
  orr x3, x3, x4
  orr x3, x3, x4
  orr x3, x3, x4
  orr x3, x3, x4
  orr x3, x3, x4
  orr x3, x3, x4
  orr x3, x3, x4
  orr x3, x3, x4
  orr x3, x3, x4
  orr x3, x3, x4
  add x2, x2, 1
  cmp x2, x0
  b.lo @lp
  mov x0, x3
  ret
}
"""),
    ("lat_vec_add4s", 16.0, """target arm64
fn lat_vec_add4s as "k_lat_vec_add4s" {
  ldr q0, [x1, 0]
  ldr q1, [x1, 16]
  mov x2, 0
@lp:
  add v0.4s, v0.4s, v1.4s
  add v0.4s, v0.4s, v1.4s
  add v0.4s, v0.4s, v1.4s
  add v0.4s, v0.4s, v1.4s
  add v0.4s, v0.4s, v1.4s
  add v0.4s, v0.4s, v1.4s
  add v0.4s, v0.4s, v1.4s
  add v0.4s, v0.4s, v1.4s
  add v0.4s, v0.4s, v1.4s
  add v0.4s, v0.4s, v1.4s
  add v0.4s, v0.4s, v1.4s
  add v0.4s, v0.4s, v1.4s
  add v0.4s, v0.4s, v1.4s
  add v0.4s, v0.4s, v1.4s
  add v0.4s, v0.4s, v1.4s
  add v0.4s, v0.4s, v1.4s
  add x2, x2, 1
  cmp x2, x0
  b.lo @lp
  str q0, [x1, 1024]
  mov x0, x2
  ret
}
"""),
    ("lat_vec_eor", 16.0, """target arm64
fn lat_vec_eor as "k_lat_vec_eor" {
  ldr q0, [x1, 0]
  ldr q1, [x1, 16]
  mov x2, 0
@lp:
  eor v0.16b, v0.16b, v1.16b
  eor v0.16b, v0.16b, v1.16b
  eor v0.16b, v0.16b, v1.16b
  eor v0.16b, v0.16b, v1.16b
  eor v0.16b, v0.16b, v1.16b
  eor v0.16b, v0.16b, v1.16b
  eor v0.16b, v0.16b, v1.16b
  eor v0.16b, v0.16b, v1.16b
  eor v0.16b, v0.16b, v1.16b
  eor v0.16b, v0.16b, v1.16b
  eor v0.16b, v0.16b, v1.16b
  eor v0.16b, v0.16b, v1.16b
  eor v0.16b, v0.16b, v1.16b
  eor v0.16b, v0.16b, v1.16b
  eor v0.16b, v0.16b, v1.16b
  eor v0.16b, v0.16b, v1.16b
  add x2, x2, 1
  cmp x2, x0
  b.lo @lp
  str q0, [x1, 1024]
  mov x0, x2
  ret
}
"""),
    ("lat_vec_ushr", 16.0, """target arm64
fn lat_vec_ushr as "k_lat_vec_ushr" {
  ldr q0, [x1, 0]
  mov x2, 0
@lp:
  ushr v0.4s, v0.4s, 7
  ushr v0.4s, v0.4s, 7
  ushr v0.4s, v0.4s, 7
  ushr v0.4s, v0.4s, 7
  ushr v0.4s, v0.4s, 7
  ushr v0.4s, v0.4s, 7
  ushr v0.4s, v0.4s, 7
  ushr v0.4s, v0.4s, 7
  ushr v0.4s, v0.4s, 7
  ushr v0.4s, v0.4s, 7
  ushr v0.4s, v0.4s, 7
  ushr v0.4s, v0.4s, 7
  ushr v0.4s, v0.4s, 7
  ushr v0.4s, v0.4s, 7
  ushr v0.4s, v0.4s, 7
  ushr v0.4s, v0.4s, 7
  add x2, x2, 1
  cmp x2, x0
  b.lo @lp
  str q0, [x1, 1024]
  mov x0, x2
  ret
}
"""),
    ("lat_vec_rev32", 16.0, """target arm64
fn lat_vec_rev32 as "k_lat_vec_rev32" {
  ldr q0, [x1, 0]
  mov x2, 0
@lp:
  rev32 v0.8h, v0.8h
  rev32 v0.8h, v0.8h
  rev32 v0.8h, v0.8h
  rev32 v0.8h, v0.8h
  rev32 v0.8h, v0.8h
  rev32 v0.8h, v0.8h
  rev32 v0.8h, v0.8h
  rev32 v0.8h, v0.8h
  rev32 v0.8h, v0.8h
  rev32 v0.8h, v0.8h
  rev32 v0.8h, v0.8h
  rev32 v0.8h, v0.8h
  rev32 v0.8h, v0.8h
  rev32 v0.8h, v0.8h
  rev32 v0.8h, v0.8h
  rev32 v0.8h, v0.8h
  add x2, x2, 1
  cmp x2, x0
  b.lo @lp
  str q0, [x1, 1024]
  mov x0, x2
  ret
}
"""),
    ("lat_vec_ext", 16.0, """target arm64
fn lat_vec_ext as "k_lat_vec_ext" {
  ldr q0, [x1, 0]
  mov x2, 0
@lp:
  ext v0.16b, v0.16b, v0.16b, 4
  ext v0.16b, v0.16b, v0.16b, 4
  ext v0.16b, v0.16b, v0.16b, 4
  ext v0.16b, v0.16b, v0.16b, 4
  ext v0.16b, v0.16b, v0.16b, 4
  ext v0.16b, v0.16b, v0.16b, 4
  ext v0.16b, v0.16b, v0.16b, 4
  ext v0.16b, v0.16b, v0.16b, 4
  ext v0.16b, v0.16b, v0.16b, 4
  ext v0.16b, v0.16b, v0.16b, 4
  ext v0.16b, v0.16b, v0.16b, 4
  ext v0.16b, v0.16b, v0.16b, 4
  ext v0.16b, v0.16b, v0.16b, 4
  ext v0.16b, v0.16b, v0.16b, 4
  ext v0.16b, v0.16b, v0.16b, 4
  ext v0.16b, v0.16b, v0.16b, 4
  add x2, x2, 1
  cmp x2, x0
  b.lo @lp
  str q0, [x1, 1024]
  mov x0, x2
  ret
}
"""),
]

TARGETED_KERNELS = [
    ("probe_cmp_fusion", "probe", """target arm64
fn probe_cmp_fusion as "k_probe_cmp_fusion" {
  mov x3, 0
  mov x2, 0
@lp:
  add x3, x3, 1
  add x2, x2, 1
  cmp x2, x0
  b.lo @lp
  mov x0, x3
  ret
}
"""),
    ("probe_nofusion_sep", "probe", """target arm64
fn probe_nofusion_sep as "k_probe_nofusion_sep" {
  mov x3, 0
  mov x2, 0
@lp:
  add x2, x2, 1
  cmp x2, x0
  add x3, x3, 1
  b.lo @lp
  mov x0, x3
  ret
}
"""),
    ("probe_mov_elim", "probe", """target arm64
fn probe_mov_elim as "k_probe_mov_elim" {
  mov x4, 1
  mov x5, 2
  mov x6, 3
  mov x7, 4
  mov x2, 0
@lp:
  mov x8, x4
  mov x9, x5
  mov x4, x6
  mov x5, x7
  mov x6, x8
  mov x7, x9
  mov x8, x4
  mov x9, x5
  mov x4, x6
  mov x5, x7
  mov x6, x8
  mov x7, x9
  add x2, x2, 1
  cmp x2, x0
  b.lo @lp
  mov x0, x4
  ret
}
"""),
    ("probe_alu_wide", "probe", """target arm64
fn probe_alu_wide as "k_probe_alu_wide" {
  mov x3, 1
  mov x4, 2
  mov x5, 3
  mov x6, 4
  mov x7, 5
  mov x8, 6
  mov x2, 0
@lp:
  add x3, x3, 1
  add x4, x4, 2
  add x5, x5, 3
  add x6, x6, 4
  add x7, x7, 5
  add x8, x8, 6
  add x3, x3, 7
  add x4, x4, 8
  add x5, x5, 9
  add x6, x6, 10
  add x7, x7, 11
  add x8, x8, 12
  add x2, x2, 1
  cmp x2, x0
  b.lo @lp
  add x0, x3, x4
  add x0, x0, x5
  add x0, x0, x6
  add x0, x0, x7
  add x0, x0, x8
  ret
}
"""),
    ("probe_dep_chain", "probe", """target arm64
fn probe_dep_chain as "k_probe_dep_chain" {
  mov x3, 1
  mov x2, 0
@lp:
  add x3, x3, 1
  add x3, x3, 3
  add x3, x3, 5
  add x3, x3, 7
  add x3, x3, 9
  add x3, x3, 11
  add x3, x3, 13
  add x3, x3, 15
  add x3, x3, 17
  add x3, x3, 19
  add x2, x2, 1
  cmp x2, x0
  b.lo @lp
  mov x0, x3
  ret
}
"""),
    ("probe_load_mix", "probe", """target arm64
fn probe_load_mix as "k_probe_load_mix" {
  mov x3, 0
  mov x4, 0
  mov x5, 0
  mov x6, 0
  mov x2, 0
@lp:
  ldr x7, [x1, 0]
  ldr x8, [x1, 8]
  ldr x9, [x1, 16]
  ldr x10, [x1, 24]
  add x3, x3, x7
  add x4, x4, x8
  add x5, x5, x9
  add x6, x6, x10
  ldr x7, [x1, 32]
  ldr x8, [x1, 40]
  ldr x9, [x1, 48]
  ldr x10, [x1, 56]
  add x3, x3, x7
  add x4, x4, x8
  add x5, x5, x9
  add x6, x6, x10
  add x2, x2, 1
  cmp x2, x0
  b.lo @lp
  add x0, x3, x4
  add x0, x0, x5
  add x0, x0, x6
  ret
}
"""),
    ("probe_vec_add_wide", "probe", """target arm64
fn probe_vec_add_wide as "k_probe_vec_add_wide" {
  ldr q0, [x1, 0]
  ldr q1, [x1, 16]
  ldr q2, [x1, 32]
  ldr q3, [x1, 48]
  ldr q4, [x1, 64]
  ldr q5, [x1, 80]
  ldr q6, [x1, 96]
  ldr q7, [x1, 112]
  ldr q16, [x1, 128]
  mov x2, 0
@lp:
  add v0.4s, v0.4s, v16.4s
  add v1.4s, v1.4s, v16.4s
  add v2.4s, v2.4s, v16.4s
  add v3.4s, v3.4s, v16.4s
  add v4.4s, v4.4s, v16.4s
  add v5.4s, v5.4s, v16.4s
  add v6.4s, v6.4s, v16.4s
  add v7.4s, v7.4s, v16.4s
  add v0.4s, v0.4s, v16.4s
  add v1.4s, v1.4s, v16.4s
  add v2.4s, v2.4s, v16.4s
  add v3.4s, v3.4s, v16.4s
  add v4.4s, v4.4s, v16.4s
  add v5.4s, v5.4s, v16.4s
  add v6.4s, v6.4s, v16.4s
  add v7.4s, v7.4s, v16.4s
  add x2, x2, 1
  cmp x2, x0
  b.lo @lp
  str q0, [x1, 1024]
  mov x0, x2
  ret
}
"""),
    ("probe_vec_shf_wide", "probe", """target arm64
fn probe_vec_shf_wide as "k_probe_vec_shf_wide" {
  ldr q0, [x1, 0]
  ldr q1, [x1, 16]
  ldr q2, [x1, 32]
  ldr q3, [x1, 48]
  ldr q4, [x1, 64]
  ldr q5, [x1, 80]
  ldr q6, [x1, 96]
  ldr q7, [x1, 112]
  mov x2, 0
@lp:
  ushr v0.4s, v0.4s, 7
  ushr v1.4s, v1.4s, 7
  ushr v2.4s, v2.4s, 7
  ushr v3.4s, v3.4s, 7
  ushr v4.4s, v4.4s, 7
  ushr v5.4s, v5.4s, 7
  ushr v6.4s, v6.4s, 7
  ushr v7.4s, v7.4s, 7
  shl v0.4s, v0.4s, 3
  shl v1.4s, v1.4s, 3
  shl v2.4s, v2.4s, 3
  shl v3.4s, v3.4s, 3
  shl v4.4s, v4.4s, 3
  shl v5.4s, v5.4s, 3
  shl v6.4s, v6.4s, 3
  shl v7.4s, v7.4s, 3
  add x2, x2, 1
  cmp x2, x0
  b.lo @lp
  str q0, [x1, 1024]
  mov x0, x2
  ret
}
"""),
    ("probe_vec_ext_wide", "probe", """target arm64
fn probe_vec_ext_wide as "k_probe_vec_ext_wide" {
  ldr q0, [x1, 0]
  ldr q1, [x1, 16]
  ldr q2, [x1, 32]
  ldr q3, [x1, 48]
  ldr q4, [x1, 64]
  ldr q5, [x1, 80]
  ldr q6, [x1, 96]
  ldr q7, [x1, 112]
  mov x2, 0
@lp:
  ext v0.16b, v0.16b, v0.16b, 4
  ext v1.16b, v1.16b, v1.16b, 4
  ext v2.16b, v2.16b, v2.16b, 4
  ext v3.16b, v3.16b, v3.16b, 4
  ext v4.16b, v4.16b, v4.16b, 4
  ext v5.16b, v5.16b, v5.16b, 4
  ext v6.16b, v6.16b, v6.16b, 4
  ext v7.16b, v7.16b, v7.16b, 4
  ext v0.16b, v0.16b, v0.16b, 8
  ext v1.16b, v1.16b, v1.16b, 8
  ext v2.16b, v2.16b, v2.16b, 8
  ext v3.16b, v3.16b, v3.16b, 8
  ext v4.16b, v4.16b, v4.16b, 8
  ext v5.16b, v5.16b, v5.16b, 8
  ext v6.16b, v6.16b, v6.16b, 8
  ext v7.16b, v7.16b, v7.16b, 8
  add x2, x2, 1
  cmp x2, x0
  b.lo @lp
  str q0, [x1, 1024]
  mov x0, x2
  ret
}
"""),
    ("probe_vec_add_16reg", "probe", """target arm64
fn probe_vec_add_16reg as "k_probe_vec_add_16reg" {
  ldr q0, [x1, 0]
  ldr q1, [x1, 16]
  ldr q2, [x1, 32]
  ldr q3, [x1, 48]
  ldr q4, [x1, 64]
  ldr q5, [x1, 80]
  ldr q6, [x1, 96]
  ldr q7, [x1, 112]
  ldr q16, [x1, 0]
  ldr q17, [x1, 16]
  ldr q18, [x1, 32]
  ldr q19, [x1, 48]
  ldr q20, [x1, 64]
  ldr q21, [x1, 80]
  ldr q22, [x1, 96]
  ldr q23, [x1, 112]
  ldr q24, [x1, 128]
  mov x2, 0
@lp:
  add v0.4s, v0.4s, v24.4s
  add v1.4s, v1.4s, v24.4s
  add v2.4s, v2.4s, v24.4s
  add v3.4s, v3.4s, v24.4s
  add v4.4s, v4.4s, v24.4s
  add v5.4s, v5.4s, v24.4s
  add v6.4s, v6.4s, v24.4s
  add v7.4s, v7.4s, v24.4s
  add v16.4s, v16.4s, v24.4s
  add v17.4s, v17.4s, v24.4s
  add v18.4s, v18.4s, v24.4s
  add v19.4s, v19.4s, v24.4s
  add v20.4s, v20.4s, v24.4s
  add v21.4s, v21.4s, v24.4s
  add v22.4s, v22.4s, v24.4s
  add v23.4s, v23.4s, v24.4s
  add x2, x2, 1
  cmp x2, x0
  b.lo @lp
  str q0, [x1, 1024]
  mov x0, x2
  ret
}
"""),
    ("real_adler32_body", "real", """target arm64
fn real_adler32_body as "k_real_adler32_body" {
  mov x3, 1
  mov x4, 0
  mov x10, 255
  mov x2, 0
@lp:
  and x5, x2, x10
  add x6, x1, x5
  ldrb w7, [x6, 0]
  add x3, x3, x7
  add x4, x4, x3
  add x2, x2, 1
  cmp x2, x0
  b.lo @lp
  add x0, x3, x4
  ret
}
"""),
    ("real_ct_lt_body", "real", """target arm64
fn real_ct_lt_body as "k_real_ct_lt_body" {
  mov x3, 0
  mov x2, 0
  mov x10, 255
@lp:
  and x4, x2, x10
  add x5, x1, x4
  ldrb w6, [x5, 0]
  ldrb w7, [x5, 256]
  add x8, x7, x3
  sub x9, x6, x8
  lsr x3, x9, 63
  add x2, x2, 1
  cmp x2, x0
  b.lo @lp
  mov x0, x3
  ret
}
"""),
    ("real_neon_b3_g1", "real", """target arm64
fn real_neon_b3_g1 as "k_real_neon_b3_g1" {
  ldr q0, [x1, 0]
  ldr q1, [x1, 16]
  ldr q2, [x1, 32]
  ldr q3, [x1, 48]
  ldr q4, [x1, 64]
  ldr q5, [x1, 80]
  mov x2, 0
@lp:
  add v0.4s, v0.4s, v1.4s
  add v0.4s, v0.4s, v4.4s
  eor v3.16b, v3.16b, v0.16b
  rev32 v3.8h, v3.8h
  add v2.4s, v2.4s, v3.4s
  eor v1.16b, v1.16b, v2.16b
  ushr v6.4s, v1.4s, 12
  shl v1.4s, v1.4s, 20
  orr v1.16b, v1.16b, v6.16b
  add v0.4s, v0.4s, v1.4s
  add v0.4s, v0.4s, v5.4s
  eor v3.16b, v3.16b, v0.16b
  ushr v6.4s, v3.4s, 8
  shl v3.4s, v3.4s, 24
  orr v3.16b, v3.16b, v6.16b
  add v2.4s, v2.4s, v3.4s
  eor v1.16b, v1.16b, v2.16b
  ushr v6.4s, v1.4s, 7
  shl v1.4s, v1.4s, 25
  orr v1.16b, v1.16b, v6.16b
  add x2, x2, 1
  cmp x2, x0
  b.lo @lp
  str q0, [x1, 1024]
  mov x0, x2
  ret
}
"""),
    ("real_neon_b3_round", "real", """target arm64
fn real_neon_b3_round as "k_real_neon_b3_round" {
  ldr q0, [x1, 0]
  ldr q1, [x1, 16]
  ldr q2, [x1, 32]
  ldr q3, [x1, 48]
  ldr q4, [x1, 64]
  ldr q5, [x1, 80]
  ldr q16, [x1, 96]
  ldr q17, [x1, 112]
  mov x2, 0
@lp:
  add v0.4s, v0.4s, v1.4s
  add v0.4s, v0.4s, v4.4s
  eor v3.16b, v3.16b, v0.16b
  rev32 v3.8h, v3.8h
  add v2.4s, v2.4s, v3.4s
  eor v1.16b, v1.16b, v2.16b
  ushr v6.4s, v1.4s, 12
  shl v1.4s, v1.4s, 20
  orr v1.16b, v1.16b, v6.16b
  add v0.4s, v0.4s, v1.4s
  add v0.4s, v0.4s, v5.4s
  eor v3.16b, v3.16b, v0.16b
  ushr v6.4s, v3.4s, 8
  shl v3.4s, v3.4s, 24
  orr v3.16b, v3.16b, v6.16b
  add v2.4s, v2.4s, v3.4s
  eor v1.16b, v1.16b, v2.16b
  ushr v6.4s, v1.4s, 7
  shl v1.4s, v1.4s, 25
  orr v1.16b, v1.16b, v6.16b
  ext v1.16b, v1.16b, v1.16b, 4
  ext v2.16b, v2.16b, v2.16b, 8
  ext v3.16b, v3.16b, v3.16b, 12
  add v0.4s, v0.4s, v1.4s
  add v0.4s, v0.4s, v16.4s
  eor v3.16b, v3.16b, v0.16b
  rev32 v3.8h, v3.8h
  add v2.4s, v2.4s, v3.4s
  eor v1.16b, v1.16b, v2.16b
  ushr v6.4s, v1.4s, 12
  shl v1.4s, v1.4s, 20
  orr v1.16b, v1.16b, v6.16b
  add v0.4s, v0.4s, v1.4s
  add v0.4s, v0.4s, v17.4s
  eor v3.16b, v3.16b, v0.16b
  ushr v6.4s, v3.4s, 8
  shl v3.4s, v3.4s, 24
  orr v3.16b, v3.16b, v6.16b
  add v2.4s, v2.4s, v3.4s
  eor v1.16b, v1.16b, v2.16b
  ushr v6.4s, v1.4s, 7
  shl v1.4s, v1.4s, 25
  orr v1.16b, v1.16b, v6.16b
  ext v1.16b, v1.16b, v1.16b, 12
  ext v2.16b, v2.16b, v2.16b, 8
  ext v3.16b, v3.16b, v3.16b, 4
  add x2, x2, 1
  cmp x2, x0
  b.lo @lp
  str q0, [x1, 1024]
  mov x0, x2
  ret
}
"""),
]


def generate_random_kernels(seed=20261126):
    """Generate 10 reproducible randomized AArch64 + NEON instruction-mix loops."""
    rng = random.Random(seed)
    gprs = ["x3", "x4", "x5", "x6", "x7", "x8", "x9", "x10"]
    vecs = ["v0", "v1", "v2", "v3", "v4", "v5", "v6", "v7"]
    out = []
    profiles = [
        ("rand_00_scalar", "scalar", 12),
        ("rand_01_scalar_mem", "scalar_mem", 14),
        ("rand_02_neon", "neon", 14),
        ("rand_03_neon_heavy", "neon", 22),
        ("rand_04_mixed", "mixed", 18),
        ("rand_05_scalar", "scalar", 18),
        ("rand_06_scalar_mem", "scalar_mem", 16),
        ("rand_07_neon", "neon", 18),
        ("rand_08_mixed", "mixed", 24),
        ("rand_09_neon_mem", "neon_mem", 16),
    ]
    for name, prof, n_ops in profiles:
        init = [f"  mov {r}, {i+1}" for i, r in enumerate(gprs)]
        if prof in ("neon", "mixed", "neon_mem"):
            init += [f"  ldr q{i}, [x1, {i*16}]" for i in range(8)]
        init.append("  mov x2, 0")
        body = []
        for _ in range(n_ops):
            k = prof
            if k == "mixed":
                k = rng.choice(["scalar", "scalar_mem", "neon", "neon_mem"])
            if k == "scalar":
                d, s1, s2 = rng.choice(gprs), rng.choice(gprs), rng.choice(gprs)
                op = rng.choice(["add", "sub", "orr", "and", "lsl", "lsr", "mov"])
                if op in ("lsl", "lsr"):
                    body.append(f"  {op} {d}, {s1}, {rng.choice([1, 2, 3, 5, 7])}")
                elif op == "mov":
                    body.append(f"  mov {d}, {s1}")
                else:
                    body.append(f"  {op} {d}, {s1}, {s2}")
            elif k == "scalar_mem":
                d = rng.choice(gprs)
                off = rng.choice([0, 8, 16, 24, 32, 40, 48, 56, 64, 72])
                if rng.random() < 0.72:
                    body.append(f"  ldr {d}, [x1, {off}]")
                else:
                    body.append(f"  add {d}, {d}, {rng.choice(gprs)}")
            elif k == "neon":
                d, s1, s2 = rng.choice(vecs), rng.choice(vecs), rng.choice(vecs)
                op = rng.choice(["add4s", "eor", "orr", "ushr", "shl", "rev32", "ext", "uzp1"])
                if op == "add4s":
                    body.append(f"  add {d}.4s, {s1}.4s, {s2}.4s")
                elif op in ("eor", "orr"):
                    body.append(f"  {op} {d}.16b, {s1}.16b, {s2}.16b")
                elif op in ("ushr", "shl"):
                    body.append(f"  {op} {d}.4s, {s1}.4s, {rng.choice([3, 7, 12, 16])}")
                elif op == "rev32":
                    body.append(f"  rev32 {d}.8h, {s1}.8h")
                elif op == "ext":
                    body.append(f"  ext {d}.16b, {s1}.16b, {s2}.16b, {rng.choice([4, 8, 12])}")
                else:
                    body.append(f"  uzp1 {d}.4s, {s1}.4s, {s2}.4s")
            elif k == "neon_mem":
                vi = rng.randrange(8)
                off = rng.choice([0, 16, 32, 48, 64, 80, 96, 112])
                if rng.random() < 0.5:
                    body.append(f"  ldr q{vi}, [x1, {off}]")
                else:
                    s1 = rng.choice(vecs)
                    body.append(f"  add v{vi}.4s, v{vi}.4s, {s1}.4s")
        tail = ["  add x2, x2, 1", "  cmp x2, x0", "  b.lo @lp", "  mov x0, x3"]
        if prof in ("neon", "mixed", "neon_mem"):
            tail.insert(-1, "  str q0, [x1, 1024]")
        tail.append("  ret")
        src = f'target arm64\nfn {name} as "k_{name}" {{\n' + "\n".join(init) + "\n@lp:\n" + "\n".join(body) + "\n" + "\n".join(tail) + "\n}\n"
        out.append((name, "random", src))
    return out


def extract_arm64_code_and_loop(elf_bytes, elf_path, symbol):
    """Extract raw 32-bit instruction words AND decoded loop sequence for `uica_sim`/`estimate`."""
    rows = arm_obj.read(elf_path, symbol)
    _, heads = estimate.load_table("arm64")
    parsed = []
    for pc, end_pc, text in rows:
        row, raw_bind = table.find(heads, table.parse_row(text))
        bind = estimate._conc_bind(raw_bind)
        reads, writes, _, _ = estimate.row_rw(row, bind, "arm64")
        cls = estimate.classify_row(row.name, "arm64")
        jump = None
        if row.name in ("b", "b_eq", "b_ne", "b_hs", "b_lo", "b_hi", "b_ls"):
            jump = int(text.split()[1], 0)
        parsed.append({
            "pc": pc, "end": end_pc, "len": end_pc - pc,
            "row": row.name, "class": cls, "reads": reads, "writes": writes,
            "jump": jump, "text": text,
        })
    # Read raw .text bytes of the ELF object
    e_shoff = struct.unpack_from("<Q", elf_bytes, 40)[0]
    e_shentsize, e_shnum, e_shstrndx = struct.unpack_from("<HHH", elf_bytes, 58)
    def sh(i):
        return struct.unpack_from("<IIQQQQIIQQ", elf_bytes, e_shoff + i * e_shentsize)
    shstr_off = sh(e_shstrndx)[4]
    text_bytes = None
    for i in range(e_shnum):
        s = sh(i)
        name_end = elf_bytes.index(b"\x00", shstr_off + s[0])
        sname = elf_bytes[shstr_off + s[0]:name_end].decode("ascii", "replace")
        if sname == ".text":
            text_bytes = elf_bytes[s[4]:s[4] + s[5]]
            break
    if text_bytes is None:
        raise RuntimeError(f"no .text section in {symbol}")
    words = list(struct.unpack(f"<{len(text_bytes)//4}I", text_bytes))

    for i, it in enumerate(parsed):
        if it["jump"] is not None and it["jump"] <= it["pc"]:
            for j in range(i):
                if parsed[j]["pc"] == it["jump"]:
                    return words, rows, parsed[j:i + 1]
    return words, rows, parsed


def run_llvm_mca_arm64(src, mcpu):
    """Run llvm-mca on the AArch64 loop body if available."""
    m = re.search(r"@lp:\n(.*?)\n\s*b\.lo\s+@lp", src, re.S)
    if not m:
        return None
    asm = m.group(1) + "\n  b.lo 0\n"
    try:
        r = subprocess.run(
            ["llvm-mca", "-mtriple=aarch64-linux-gnu", f"-mcpu={mcpu}", "-iterations=100"],
            input=asm, text=True, capture_output=True,
        )
    except FileNotFoundError:
        return None
    if r.returncode != 0:
        return None
    tc = re.search(r"Total Cycles:\s+(\d+)", r.stdout)
    return float(tc.group(1)) / 100.0 if tc else None


def emit_asm_and_harness(td, entries, is_darwin, iters, rounds):
    """Emit `.S` (exact Ode instruction words + 64-op calibration chains) + C timing harness."""
    pfx = "_" if is_darwin else ""
    asm_lines = [".text"]
    # Reference 64-op serial `add x3, x3, x4` chain (exact 64.000 cyc/iter on every AArch64 core)
    # and independent 64-op serial `orr x3, x3, x4` cross-check chain (also exact 64.000 cyc/iter).
    asm_lines += [
        ".p2align 6",
        f".globl {pfx}cal_add64",
        f"{pfx}cal_add64:",
        "  mov x3, #1",
        "  mov x4, #3",
        "  mov x2, #0",
        "1:",
    ] + ["  add x3, x3, x4"] * 64 + [
        "  add x2, x2, #1",
        "  cmp x2, x0",
        "  b.lo 1b",
        "  mov x0, x3",
        "  ret",
        ".p2align 6",
        f".globl {pfx}cal_orr64",
        f"{pfx}cal_orr64:",
        "  mov x3, #1",
        "  mov x4, #3",
        "  mov x2, #0",
        "1:",
    ] + ["  orr x3, x3, x4"] * 64 + [
        "  add x2, x2, #1",
        "  cmp x2, x0",
        "  b.lo 1b",
        "  mov x0, x3",
        "  ret",
    ]
    for name, words in entries:
        asm_lines.append(".p2align 6")
        asm_lines.append(f".globl {pfx}k_{name}")
        asm_lines.append(f"{pfx}k_{name}:")
        for w in words:
            asm_lines.append(f"  .long 0x{w:08x}")
    asm_path = os.path.join(td, "kernels.S")
    with open(asm_path, "w", encoding="utf-8") as f:
        f.write("\n".join(asm_lines) + "\n")

    decls = "\n".join(f"extern uint64_t k_{name}(uint64_t iters, uint8_t *buf);" for name, _ in entries)
    table_rows = "\n".join(f'  {{"{name}", k_{name}}},' for name, _ in entries)
    c_src = f"""#define _GNU_SOURCE
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#if defined(__APPLE__)
#include <pthread/qos.h>
#else
#include <linux/perf_event.h>
#include <sched.h>
#include <sys/ioctl.h>
#include <sys/syscall.h>
#include <unistd.h>
#endif

extern uint64_t cal_add64(uint64_t iters, uint8_t *buf);
extern uint64_t cal_orr64(uint64_t iters, uint8_t *buf);
{decls}

typedef uint64_t (*kfn_t)(uint64_t, uint8_t *);
struct K {{ const char *name; kfn_t fn; }};
static struct K KERNELS[] = {{
{table_rows}
}};

static inline uint64_t now_ns(void) {{
#if defined(__APPLE__)
    return clock_gettime_nsec_np(CLOCK_UPTIME_RAW);
#else
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC_RAW, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
#endif
}}

static int cmp_d(const void *a, const void *b) {{
    double x = *(const double *)a, y = *(const double *)b;
    return (x > y) - (x < y);
}}

#if !defined(__APPLE__)
static int open_perf_cycles(void) {{
    struct perf_event_attr pe;
    memset(&pe, 0, sizeof(pe));
    pe.type = PERF_TYPE_HARDWARE;
    pe.size = sizeof(pe);
    pe.config = PERF_COUNT_HW_CPU_CYCLES;
    pe.disabled = 1;
    pe.exclude_kernel = 1;
    pe.exclude_hv = 1;
    int fd = (int)syscall(__NR_perf_event_open, &pe, 0, -1, -1, 0);
    if (fd >= 0) {{
        uint64_t c = 0;
        ioctl(fd, PERF_EVENT_IOC_RESET, 0);
        ioctl(fd, PERF_EVENT_IOC_ENABLE, 0);
        volatile uint64_t s = cal_add64(2000, NULL);
        (void)s;
        ioctl(fd, PERF_EVENT_IOC_DISABLE, 0);
        if (read(fd, &c, sizeof(c)) != sizeof(c) || c < 10000) {{
            close(fd);
            return -1;
        }}
    }}
    return fd;
}}
#endif

static double measure_ref_ns_per_cyc(uint8_t *buf, uint64_t cal_iters) {{
    volatile uint64_t sink = 0;
    uint64_t t0 = now_ns();
    sink ^= cal_add64(cal_iters, buf);
    uint64_t t1 = now_ns();
    (void)sink;
    return (double)(t1 - t0) / ((double)cal_iters * 64.0);
}}

int main(void) {{
    uint8_t *buf = NULL;
    if (posix_memalign((void **)&buf, 64, 4096) != 0) return 2;
    for (int i = 0; i < 4096; i++) buf[i] = (uint8_t)((i * 37 + 13) & 0xff);

    int use_pmu = 0;
    int pmu_fd = -1;
#if defined(__APPLE__)
    pthread_set_qos_class_self_np(QOS_CLASS_USER_INTERACTIVE, 0);
#else
    cpu_set_t set; CPU_ZERO(&set); CPU_SET(1, &set);
    sched_setaffinity(0, sizeof(set), &set);
    pmu_fd = open_perf_cycles();
    if (pmu_fd >= 0) use_pmu = 1;
#endif

    // Warmup & cross-check cal_add64 vs cal_orr64
    volatile uint64_t sink = 0;
    uint64_t cal_iters = 60000;
    sink ^= cal_add64(cal_iters, buf);
    sink ^= cal_orr64(cal_iters, buf);
    double ratios[9];
    for (int r = 0; r < 9; r++) {{
        uint64_t t0 = now_ns(); sink ^= cal_add64(cal_iters, buf); uint64_t dt_a = now_ns() - t0;
        uint64_t t1 = now_ns(); sink ^= cal_orr64(cal_iters, buf); uint64_t dt_o = now_ns() - t1;
        ratios[r] = (double)dt_o / (double)dt_a;
    }}
    qsort(ratios, 9, sizeof(double), cmp_d);
    double freq_ghz = 1.0 / measure_ref_ns_per_cyc(buf, cal_iters);
    printf("META mode=%s freq_ghz=%.3f orr_over_add=%.4f\\n",
           use_pmu ? "perf_event_open" : "ref_add64_clock", freq_ghz, ratios[4]);

    int n = (int)(sizeof(KERNELS) / sizeof(KERNELS[0]));
    uint64_t iters = {iters}ULL;
    int rounds = {rounds};
    for (int i = 0; i < n; i++) {{
        sink ^= KERNELS[i].fn(iters / 4, buf);
        double vals[64];
        for (int r = 0; r < rounds; r++) {{
#if !defined(__APPLE__)
            if (use_pmu) {{
                uint64_t c = 0;
                ioctl(pmu_fd, PERF_EVENT_IOC_RESET, 0);
                ioctl(pmu_fd, PERF_EVENT_IOC_ENABLE, 0);
                sink ^= KERNELS[i].fn(iters, buf);
                ioctl(pmu_fd, PERF_EVENT_IOC_DISABLE, 0);
                if (read(pmu_fd, &c, sizeof(c)) != sizeof(c)) c = 0;
                vals[r] = (double)c / (double)iters;
                continue;
            }}
#endif
            double ns_cyc_a = 0.0, ns_cyc_b = 0.0;
            uint64_t dt = 0;
            for (int tries = 0; tries < 8; tries++) {{
                ns_cyc_a = measure_ref_ns_per_cyc(buf, cal_iters);
                uint64_t t0 = now_ns();
                sink ^= KERNELS[i].fn(iters, buf);
                dt = now_ns() - t0;
                ns_cyc_b = measure_ref_ns_per_cyc(buf, cal_iters);
                double diff = ns_cyc_a > ns_cyc_b ? (ns_cyc_a - ns_cyc_b) : (ns_cyc_b - ns_cyc_a);
                if (diff <= 0.008 * ns_cyc_a) break;
            }}
            double ns_cyc = 0.5 * (ns_cyc_a + ns_cyc_b);
            vals[r] = ((double)dt / (double)iters) / ns_cyc;
        }}
        qsort(vals, rounds, sizeof(double), cmp_d);
        printf("RESULT %s %.4f %.4f %.4f\\n", KERNELS[i].name, vals[rounds/2], vals[0], vals[rounds-1]);
    }}
    (void)sink;
    return 0;
}}
"""
    c_path = os.path.join(td, "harness.c")
    with open(c_path, "w", encoding="utf-8") as f:
        f.write(c_src)
    bin_path = os.path.join(td, "harness")
    subprocess.run(["cc", "-O2", c_path, asm_path, "-o", bin_path], check=True)
    return bin_path


def main():
    ap = argparse.ArgumentParser(description="Validate AArch64 uica_sim against bare-metal hardware.")
    ap.add_argument("--arch", default="apple_m", choices=["apple_m", "ampere1"])
    ap.add_argument("--run", action="store_true", help="Compile and measure on local AArch64 hardware")
    ap.add_argument("--iters", type=int, default=120000)
    ap.add_argument("--rounds", type=int, default=11)
    ap.add_argument("--mcpu", default=None, help="Optional llvm-mca -mcpu (e.g. apple-m3, ampere1)")
    ap.add_argument("--json-out", default=None)
    args = ap.parse_args()

    eval_kernels = list(TARGETED_KERNELS) + generate_random_kernels()
    all_build = [(n, "lat", s) for n, _, s in LATENCY_PROBES] + eval_kernels
    lat_divs = {n: d for n, d, _ in LATENCY_PROBES}

    with tempfile.TemporaryDirectory() as td:
        entries = []
        compiled = {}
        for name, kind, src in all_build:
            ode_p = os.path.join(td, f"{name}.ode")
            with open(ode_p, "w", encoding="utf-8") as f:
                f.write(src)
            info = odec.compile_info(ode_p, name)
            elf_p = os.path.join(td, f"{name}.o")
            with open(elf_p, "wb") as f:
                f.write(info["elf"])
            words, rows, loop_seq = extract_arm64_code_and_loop(info["elf"], elf_p, info["symbol"])
            entries.append((name, words))
            rep = estimate.static_analyze(rows, "arm64", args.arch)
            old_b = rep["loops"][0]["body"]["compute_lower_bound"] if rep["loops"] else rep["whole"]["compute_lower_bound"]
            sim = uica_sim.simulate_loop(loop_seq, args.arch, iterations=16)
            mca = run_llvm_mca_arm64(src, args.mcpu) if args.mcpu else None
            compiled[name] = {"kind": kind, "ins": len(loop_seq), "old": old_b, "sim": sim, "mca": mca}

        measured = {}
        meta = {}
        if args.run:
            bin_p = emit_asm_and_harness(td, entries, platform.system() == "Darwin", args.iters, args.rounds)
            r = subprocess.run([bin_p], capture_output=True, text=True, check=True)
            for line in r.stdout.splitlines():
                parts = line.split()
                if parts and parts[0] == "META":
                    for kv in parts[1:]:
                        k, v = kv.split("=", 1)
                        meta[k] = v
                elif parts and parts[0] == "RESULT":
                    measured[parts[1]] = (float(parts[2]), float(parts[3]), float(parts[4]))

        print(f"AArch64 Hardware Pipeline Validation — arch={args.arch} ({len(LATENCY_PROBES)} latency probes + {len(eval_kernels)} eval kernels)")
        if meta:
            print(f"Timing meta: {meta}")

        lat_out = {}
        if measured:
            print("\n=== Exact Instruction Latency Probes (cycles / instruction) ===")
            for n, div, _ in LATENCY_PROBES:
                med, lo, hi = measured[n]
                per_op = med / div
                lat_out[n] = round(per_op, 3)
                print(f"  {n:16s}  total={med:6.2f} cyc  ->  {per_op:5.3f} cyc/op  (min={lo/div:.3f}, max={hi/div:.3f})")

        print(f"\n{'Kernel':22s} {'Kind':6s} {'Ins':>3s} {'OldEst':>7s} {'uiCA':>7s} {'MCA':>7s} {'Meas':>7s} {'uiCA%':>7s}  Bottleneck")
        print("-" * 92)
        old_e, new_e, mca_e = [], [], []
        recs = []
        for name, kind, _ in eval_kernels:
            c = compiled[name]
            meas = measured[name][0] if name in measured else None
            old_b, u_b, m_b = c["old"], c["sim"]["cycles_per_iter"], c["mca"]
            ue_s = f"{100.0*(u_b-meas)/meas:+6.1f}%" if meas else "    n/a"
            m_s = f"{m_b:7.2f}" if m_b is not None else "    n/a"
            me_s = f"{meas:7.2f}" if meas is not None else "    n/a"
            print(f"{name:22s} {kind:6s} {c['ins']:3d} {old_b:7.2f} {u_b:7.2f} {m_s} {me_s} {ue_s}  {c['sim']['bottleneck']}")
            if meas is not None:
                old_e.append(abs(100.0 * (old_b - meas) / meas))
                new_e.append(abs(100.0 * (u_b - meas) / meas))
                if m_b is not None:
                    mca_e.append(abs(100.0 * (m_b - meas) / meas))
            recs.append({
                "name": name, "kind": kind, "loop_insns": c["ins"],
                "old_bound": round(old_b, 3), "uica_sim": round(u_b, 3),
                "uica_bottleneck": c["sim"]["bottleneck"],
                "llvm_mca": round(m_b, 3) if m_b is not None else None,
                "measured": round(meas, 4) if meas is not None else None,
            })

        def _sum(es):
            w10 = sum(1 for e in es if e <= 10.0)
            w15 = sum(1 for e in es if e <= 15.0)
            return {
                "n": len(es), "within_10pct": w10, "within_10pct_rate": round(100.0 * w10 / len(es), 1),
                "within_15pct": w15, "median_abs_err_pct": round(statistics.median(es), 1),
                "mean_abs_err_pct": round(statistics.mean(es), 1),
            }

        if measured:
            print(f"\n=== Accuracy Summary ({len(eval_kernels)} AArch64 kernels) ===")
            for label, es in [("old estimate.py", old_e), ("uica_sim.py    ", new_e)] + ([("llvm-mca       ", mca_e)] if mca_e else []):
                s = _sum(es)
                print(f"  {label}: {s['within_10pct']:2d}/{s['n']} ({s['within_10pct_rate']:5.1f}%) within 10% | "
                      f"{s['within_15pct']:2d}/{s['n']} within 15% | median {s['median_abs_err_pct']:4.1f}% | mean {s['mean_abs_err_pct']:4.1f}%")

        if args.json_out:
            out = {
                "arch": args.arch, "meta": meta, "latencies": lat_out,
                "old_bound_accuracy": _sum(old_e) if old_e else None,
                "uica_sim_accuracy": _sum(new_e) if new_e else None,
                "llvm_mca_accuracy": _sum(mca_e) if mca_e else None,
                "records": recs,
            }
            with open(args.json_out, "w", encoding="utf-8") as f:
                json.dump(out, f, indent=2)
                f.write("\n")


if __name__ == "__main__":
    main()
