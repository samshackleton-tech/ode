#!/usr/bin/env python3
"""advice/calibrate.py: real-hardware variant-ranking calibration for advice/estimate.py.

Compiles Ode variant pairs directly with lang/odec.py (x86-64 and AArch64), predicts their
costs and Layer-1 hazards with advice/estimate.py, and (with --run on Linux) links a small
C harness using perf_event_open hardware CPU cycles and interleaved A/B rounds to check
whether the estimator's rankings agree with real processors.

Usage:
    python3 advice/calibrate.py --arch zen5              # offline predictions only
    python3 advice/calibrate.py --arch zen5 --run        # predictions + hardware timing
    python3 advice/calibrate.py --arch ampere1 --run     # AArch64 predictions + hardware timing
"""
import argparse, json, os, platform, statistics, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for d in (HERE, os.path.join(ROOT, "lang"), os.path.join(ROOT, "arm64"), os.path.join(ROOT, "core")):
    if d not in sys.path:
        sys.path.insert(0, d)
import estimate, odec


# --- Small Ode calibration kernels (assembled by lang/odec.py) ---

X86_ALIAS_ODE = """target x86_64
fn st_ld_loop as "cal_x86_st_ld" {
  // rdi = dst (64*8 B), rsi = src (64*8 B), rdx = val; 64 store-then-load pairs
  xor ecx, ecx
@lp:
  mov qword ptr [rdi], rdx
  mov rax, qword ptr [rsi]
  add rdx, rax
  add rdi, 8
  add rsi, 8
  add rcx, 1
  cmp rcx, 64
  jb @lp
  mov rax, rdx
  ret
}
"""

X86_STLF_CLEAN_ODE = """target x86_64
fn stlf_clean as "cal_x86_stlf_clean" {
  // rdi = input ptr (16 B), rsi = count (64); 16 B store -> 16 B load (clean STLF)
  sub rsp, 32
  vmovdqu xmm0, xmmword ptr [rdi]
  xor ecx, ecx
@lp:
  vmovdqu xmmword ptr [rsp], xmm0
  vmovdqu xmm1, xmmword ptr [rsp]
  vpaddd xmm0, xmm0, xmm1
  add rcx, 1
  cmp rcx, rsi
  jb @lp
  vmovdqu xmmword ptr [rdi], xmm0
  add rsp, 32
  ret
}
"""

X86_STLF_PARTIAL_ODE = """target x86_64
fn stlf_partial as "cal_x86_stlf_partial" {
  // rdi = input ptr (16 B), rsi = count (64); two 8 B stores -> 16 B load (partial STLF!)
  sub rsp, 32
  mov rax, qword ptr [rdi]
  mov rdx, qword ptr [rdi + 8]
  xor ecx, ecx
@lp:
  mov qword ptr [rsp], rax
  mov qword ptr [rsp + 8], rdx
  vmovdqu xmm1, xmmword ptr [rsp]
  add rax, 1
  add rcx, 1
  cmp rcx, rsi
  jb @lp
  vmovdqu xmmword ptr [rdi], xmm1
  add rsp, 32
  ret
}
"""

X86_L1D_SET_ODE = """target x86_64
fn l1d_stride as "cal_x86_l1d_stride" {
  // rdi = base (4096 B aligned), rsi = mask ((n_lines - 1) * 4096); 64 loads all in L1D set 0
  xor eax, eax
  xor ecx, ecx
  xor r8d, r8d
@lp:
  mov r9, rdi
  add r9, r8
  mov rdx, qword ptr [r9]
  add rax, rdx
  add r8, 4096
  and r8, rsi
  add rcx, 1
  cmp rcx, 64
  jb @lp
  ret
}
"""

ARM_STLF_CLEAN_ODE = """target arm64
fn stlf_clean as "cal_arm_stlf_clean" {
  // x0 = in/out ptr (16 B); 16 rounds of 16 B st1 -> 16 B ld1 (clean STLF)
  sub sp, sp, 32
  add x2, sp, 0
  ld1 {v0.4s}, [x0]
  for i in 0..16 {
    st1 {v0.4s}, [x2]
    ld1 {v1.4s}, [x2]
    add v0.4s, v0.4s, v1.4s
  }
  st1 {v0.4s}, [x0]
  add sp, sp, 32
  ret
}
"""

ARM_STLF_PARTIAL_ODE = """target arm64
fn stlf_partial as "cal_arm_stlf_partial" {
  // x0 = in/out ptr (16 B); 16 rounds of two 8 B str -> 16 B ld1 (partial STLF!)
  sub sp, sp, 32
  add x2, sp, 0
  ldr x3, [x0, 0]
  ldr x4, [x0, 8]
  ld1 {v0.4s}, [x0]
  for i in 0..16 {
    str x3, [sp, 0]
    str x4, [sp, 8]
    ld1 {v1.4s}, [x2]
    add v0.4s, v0.4s, v1.4s
    add x3, x3, 1
  }
  st1 {v0.4s}, [x0]
  add sp, sp, 32
  ret
}
"""

ARM_L1D_4_ODE = """target arm64
fn l1d_4 as "cal_arm_l1d_4" {
  // x0 = base (16384 B aligned), x1 = stride (16384); 32 loads across 4 lines in L1D set 0 (fits 4-way L1D)
  add x9, x0, 0
  add x3, x3, 0
  for pass in 0..8 {
    add x5, x9, 0
    for j in 0..4 {
      ldr x2, [x5, 0]
      add x3, x3, x2
      add x5, x5, x1
    }
  }
  add x0, x3, 0
  ret
}
"""

ARM_L1D_8_ODE = """target arm64
fn l1d_8 as "cal_arm_l1d_8" {
  // x0 = base (16384 B aligned), x1 = stride (16384); 32 loads across 8 lines in L1D set 0 (overflows 4-way L1D!)
  add x9, x0, 0
  add x3, x3, 0
  for pass in 0..4 {
    add x5, x9, 0
    for j in 0..8 {
      ldr x2, [x5, 0]
      add x3, x3, x2
      add x5, x5, x1
    }
  }
  add x0, x3, 0
  ret
}
"""


def _make_adler_aligned_source():
    """Insert 1-byte `nop` instructions right before `@l0:` in adler32.ode so `@l0` starts at +0x40."""
    src_path = os.path.join(ROOT, "kcheck", "programs", "adler32", "adler32.ode")
    with open(src_path) as f:
        text = f.read()
    # Original @l0 is at +0x2c (44 bytes); 20 nops move @l0 to +0x40 (64 bytes, 2 i-cache lines instead of 3!)
    nops = "".join("  nop\n" for _ in range(20))
    mod = text.replace("fn adler32 as \"ode_adler32\"", "fn adler32 as \"ode_adler32_aligned\"")
    assert "@l0:\n" in mod
    return mod.replace("@l0:\n", nops + "@l0:\n", 1)


def compile_temp(d, fname, src_text, fn_names):
    p = os.path.join(d, fname)
    with open(p, "w") as f:
        f.write(src_text)
    target, _, _, _ = odec.source(src_text, p)
    infos, progs, lmaps, obj_paths = {}, {}, {}, []
    for name in fn_names:
        info = odec.compile_info(p, name)
        sym = info["symbol"]
        op = os.path.join(d, f"{sym}.o")
        with open(op, "wb") as f:
            f.write(info["elf"])
        _, dec = estimate.decode_object(op, sym, target)
        infos[sym] = info
        progs[sym] = dec
        lmaps[sym] = info["line_map"]
        obj_paths.append(op)
    return target, infos, progs, lmaps, obj_paths


def predict_x86(arch, workdir):
    """Build x86-64 calibration objects and compute advice/estimate.py predictions for all 5 pairs."""
    objs = []
    pairs = []

    # 1. p16_align (real wide/p16.ode: aligned vs +7 B misaligned)
    p16_src_path = os.path.join(ROOT, "wide", "p16.ode")
    info_p16 = odec.compile_info(p16_src_path, "p16")
    p16_sym = info_p16["symbol"]
    p16_obj = os.path.join(workdir, f"{p16_sym}.o")
    with open(p16_obj, "wb") as f: f.write(info_p16["elf"])
    objs.append(p16_obj)
    _, dec_p16 = estimate.decode_object(p16_obj, p16_sym, "x86_64")
    st_p16 = estimate.static_analyze(dec_p16, "x86_64", arch, info_p16["line_map"], info_p16["frame"])

    def trace_p16(align_off):
        tbl = 0x100000
        key = 0x110400
        out = 0x120800
        mem = {}
        for i in range(16):
            ptr = 0x200000 + i * 0x10400 + align_off
            for b in range(8):
                mem[tbl + i * 8 + b] = (ptr >> (8 * b)) & 0xFF
        packed = 0 | (1 << 8) | (2 << 16) | (64 << 24)
        tr = estimate.trace_memory({p16_sym: dec_p16}, p16_sym, "x86_64",
                                   init_regs={"rdi": tbl, "rsi": 4, "rdx": key, "rcx": 0, "r8": packed, "r9": out},
                                   init_mem=mem, line_maps={p16_sym: info_p16["line_map"]})
        return estimate.analyze_memory(tr, "x86_64", arch, info_p16["frame"])

    m_p16_a, m_p16_b = trace_p16(0), trace_p16(7)
    pairs.append({
        "name": "p16_align", "desc": "wide/p16.ode (aligned vs +7 B misaligned inputs)",
        "a_label": "aligned", "b_label": "+7B_misalign",
        "pred_a_warm": m_p16_a["est_warm_cycles"], "pred_b_warm": m_p16_b["est_warm_cycles"],
        "hazards_a": f"splits={m_p16_a['line_splits']}", "hazards_b": f"splits={m_p16_b['line_splits']}",
    })

    # 2. alias_4k
    _, infos_al, progs_al, lmaps_al, op_al = compile_temp(workdir, "alias.ode", X86_ALIAS_ODE, ["st_ld_loop"])
    objs.extend(op_al)
    sym_al = "cal_x86_st_ld"
    tr_al_a = estimate.trace_memory(progs_al, sym_al, "x86_64",
                                    init_regs={"rdi": 0x100000, "rsi": 0x110400, "rdx": 1}, line_maps=lmaps_al)
    tr_al_b = estimate.trace_memory(progs_al, sym_al, "x86_64",
                                    init_regs={"rdi": 0x100000, "rsi": 0x110000, "rdx": 1}, line_maps=lmaps_al)
    m_al_a = estimate.analyze_memory(tr_al_a, "x86_64", arch)
    m_al_b = estimate.analyze_memory(tr_al_b, "x86_64", arch)
    pairs.append({
        "name": "alias_4k", "desc": "64-iter store-then-load (+0x10400 clean vs +0x10000 4K-aliased)",
        "a_label": "no_alias", "b_label": "alias_4k",
        "pred_a_warm": m_al_a["est_warm_cycles"], "pred_b_warm": m_al_b["est_warm_cycles"],
        "hazards_a": f"alias4k={m_al_a['alias_4k']}", "hazards_b": f"alias4k={m_al_b['alias_4k']}",
    })

    # 3. stlf_width
    _, _, progs_sc, lmaps_sc, op_sc = compile_temp(workdir, "stlf_c.ode", X86_STLF_CLEAN_ODE, ["stlf_clean"])
    _, _, progs_sp, lmaps_sp, op_sp = compile_temp(workdir, "stlf_p.ode", X86_STLF_PARTIAL_ODE, ["stlf_partial"])
    objs.extend(op_sc + op_sp)
    m_sc = estimate.analyze_memory(
        estimate.trace_memory(progs_sc, "cal_x86_stlf_clean", "x86_64",
                              init_regs={"rdi": 0x100000, "rsi": 64}, line_maps=lmaps_sc), "x86_64", arch)
    m_sp = estimate.analyze_memory(
        estimate.trace_memory(progs_sp, "cal_x86_stlf_partial", "x86_64",
                              init_regs={"rdi": 0x100000, "rsi": 64}, line_maps=lmaps_sp), "x86_64", arch)
    pairs.append({
        "name": "stlf_width", "desc": "64-iter stack forwarding (16B->16B clean vs 2x8B->16B partial STLF)",
        "a_label": "clean_16B", "b_label": "partial_2x8B",
        "pred_a_warm": m_sc["est_warm_cycles"], "pred_b_warm": m_sp["est_warm_cycles"],
        "hazards_a": f"stlf_partial={m_sc['stlf_partial']},clean={m_sc['stlf_clean']}",
        "hazards_b": f"stlf_partial={m_sp['stlf_partial']},clean={m_sp['stlf_clean']}",
    })

    # 4. adler_loop_align (real adler32.ode: 3 i-cache lines vs 2 i-cache lines aligned)
    adler_path = os.path.join(ROOT, "kcheck", "programs", "adler32", "adler32.ode")
    info_ad_a = odec.compile_info(adler_path, "adler32")
    op_ad_a = os.path.join(workdir, "ode_adler32.o")
    with open(op_ad_a, "wb") as f: f.write(info_ad_a["elf"])
    objs.append(op_ad_a)
    _, dec_ad_a = estimate.decode_object(op_ad_a, "ode_adler32", "x86_64")
    st_ad_a = estimate.static_analyze(dec_ad_a, "x86_64", arch, info_ad_a["line_map"])

    _, infos_ad_b, progs_ad_b, lmaps_ad_b, op_ad_b = compile_temp(
        workdir, "adler_al.ode", _make_adler_aligned_source(), ["adler32"])
    objs.extend(op_ad_b)
    st_ad_b = estimate.static_analyze(progs_ad_b["ode_adler32_aligned"], "x86_64", arch, lmaps_ad_b["ode_adler32_aligned"])
    m_ad_a = estimate.analyze_memory(
        estimate.trace_memory({"ode_adler32": dec_ad_a}, "ode_adler32", "x86_64",
                              init_regs={"rdi": 0x100000, "rsi": 256}), "x86_64", arch)
    m_ad_b = estimate.analyze_memory(
        estimate.trace_memory(progs_ad_b, "ode_adler32_aligned", "x86_64",
                              init_regs={"rdi": 0x100000, "rsi": 256}), "x86_64", arch)
    pairs.append({
        "name": "adler_loop_align", "desc": "adler32.ode loop (aligned 2 i-cache lines vs default 3 lines)",
        "a_label": "loop_2lines", "b_label": "loop_3lines",
        "pred_a_warm": m_ad_b["est_warm_cycles"], "pred_b_warm": m_ad_a["est_warm_cycles"],
        "hazards_a": f"loop_lines={st_ad_b['loops'][0]['icache_lines']}",
        "hazards_b": f"loop_lines={st_ad_a['loops'][0]['icache_lines']}",
        "advisory_only": True,   # static loop-line hint; same warm compute cycles
    })

    # 5. l1d_set_conflict (8 lines vs 16 lines in set 0 on 12-way L1D)
    _, _, progs_l1, lmaps_l1, op_l1 = compile_temp(workdir, "l1d.ode", X86_L1D_SET_ODE, ["l1d_stride"])
    objs.extend(op_l1)
    sym_l1 = "cal_x86_l1d_stride"
    m_l1_a = estimate.analyze_memory(
        estimate.trace_memory(progs_l1, sym_l1, "x86_64",
                              init_regs={"rdi": 0x100000, "rsi": 7 * 4096}, line_maps=lmaps_l1), "x86_64", arch)
    m_l1_b = estimate.analyze_memory(
        estimate.trace_memory(progs_l1, sym_l1, "x86_64",
                              init_regs={"rdi": 0x100000, "rsi": 15 * 4096}, line_maps=lmaps_l1), "x86_64", arch)
    pairs.append({
        "name": "l1d_set_conflict", "desc": "64 strided loads in L1D set 0 (8 lines fit 12-way vs 16 lines thrash)",
        "a_label": "8_lines_fit", "b_label": "16_lines_thrash",
        "pred_a_warm": m_l1_a["est_warm_cycles"], "pred_b_warm": m_l1_b["est_warm_cycles"],
        "hazards_a": f"depth={m_l1_a['l1d_max_set_depth']}/{m_l1_a['l1d_ways']},warm_miss={m_l1_a['l1d_warm_misses']}",
        "hazards_b": f"depth={m_l1_b['l1d_max_set_depth']}/{m_l1_b['l1d_ways']},warm_miss={m_l1_b['l1d_warm_misses']}",
    })
    return objs, pairs


def predict_arm64(arch, workdir):
    """Build AArch64 calibration objects and compute advice/estimate.py predictions for all 3 pairs."""
    objs = []
    pairs = []

    # 1. arm_mix_align (verified mix.ode: aligned vs +7 B misaligned)
    mix_path = os.path.join(ROOT, "proof-core", "examples", "arm64", "mix.ode")
    progs_m, lmaps_m, frames_m = {}, {}, {}
    for name in ("mix16_3", "mix16_again", "mix16_6"):
        info = odec.compile_info(mix_path, name)
        sym = info["symbol"]
        op = os.path.join(workdir, f"{sym}.o")
        with open(op, "wb") as f: f.write(info["elf"])
        objs.append(op)
        _, dec = estimate.decode_object(op, sym, "arm64")
        progs_m[sym] = dec
        lmaps_m[sym] = info["line_map"]
        frames_m[sym] = info["frame"]
    m_mix_a = estimate.analyze_memory(
        estimate.trace_memory(progs_m, "arm_mix16_6", "arm64",
                              init_regs={"x0": 0x100000, "x1": 0x110400, "x2": 0x120800}, line_maps=lmaps_m),
        "arm64", arch, frames_m["arm_mix16_6"])
    m_mix_b = estimate.analyze_memory(
        estimate.trace_memory(progs_m, "arm_mix16_6", "arm64",
                              init_regs={"x0": 0x100007, "x1": 0x110407, "x2": 0x120807}, line_maps=lmaps_m),
        "arm64", arch, frames_m["arm_mix16_6"])
    pairs.append({
        "name": "arm_mix_align", "desc": "arm64/mix.ode arm_mix16_6 (64B aligned vs +7B misaligned)",
        "a_label": "aligned", "b_label": "+7B_misalign",
        "pred_a_warm": m_mix_a["est_warm_cycles"], "pred_b_warm": m_mix_b["est_warm_cycles"],
        "hazards_a": f"splits={m_mix_a['line_splits']}", "hazards_b": f"splits={m_mix_b['line_splits']}",
    })

    # 2. arm_stlf_width
    _, _, p_sc, lm_sc, op_sc = compile_temp(workdir, "arm_stlf_c.ode", ARM_STLF_CLEAN_ODE, ["stlf_clean"])
    _, _, p_sp, lm_sp, op_sp = compile_temp(workdir, "arm_stlf_p.ode", ARM_STLF_PARTIAL_ODE, ["stlf_partial"])
    objs.extend(op_sc + op_sp)
    m_sc = estimate.analyze_memory(
        estimate.trace_memory(p_sc, "cal_arm_stlf_clean", "arm64", init_regs={"x0": 0x100000}, line_maps=lm_sc), "arm64", arch)
    m_sp = estimate.analyze_memory(
        estimate.trace_memory(p_sp, "cal_arm_stlf_partial", "arm64", init_regs={"x0": 0x100000}, line_maps=lm_sp), "arm64", arch)
    pairs.append({
        "name": "arm_stlf_width", "desc": "16-round AArch64 stack forwarding (16B->16B clean vs 2x8B->16B partial)",
        "a_label": "clean_16B", "b_label": "partial_2x8B",
        "pred_a_warm": m_sc["est_warm_cycles"], "pred_b_warm": m_sp["est_warm_cycles"],
        "hazards_a": f"stlf_partial={m_sc['stlf_partial']}", "hazards_b": f"stlf_partial={m_sp['stlf_partial']}",
    })

    # 3. arm_l1d_conflict (4 lines vs 8 lines spaced by 16 KiB in set 0 of Ampere-1a 4-way L1D)
    _, _, p_l4, lm_l4, op_l4 = compile_temp(workdir, "arm_l4.ode", ARM_L1D_4_ODE, ["l1d_4"])
    _, _, p_l8, lm_l8, op_l8 = compile_temp(workdir, "arm_l8.ode", ARM_L1D_8_ODE, ["l1d_8"])
    objs.extend(op_l4 + op_l8)
    m_l4 = estimate.analyze_memory(
        estimate.trace_memory(p_l4, "cal_arm_l1d_4", "arm64", init_regs={"x0": 0x100000, "x1": 16384}, line_maps=lm_l4), "arm64", arch)
    m_l8 = estimate.analyze_memory(
        estimate.trace_memory(p_l8, "cal_arm_l1d_8", "arm64", init_regs={"x0": 0x100000, "x1": 16384}, line_maps=lm_l8), "arm64", arch)
    pairs.append({
        "name": "arm_l1d_conflict", "desc": "32 loads spaced by 16 KiB in L1D set 0 (4 lines fit 4-way vs 8 thrash)",
        "a_label": "4_lines_fit", "b_label": "8_lines_thrash",
        "pred_a_warm": m_l4["est_warm_cycles"], "pred_b_warm": m_l8["est_warm_cycles"],
        "hazards_a": f"depth={m_l4['l1d_max_set_depth']}/{m_l4['l1d_ways']},warm_miss={m_l4['l1d_warm_misses']}",
        "hazards_b": f"depth={m_l8['l1d_max_set_depth']}/{m_l8['l1d_ways']},warm_miss={m_l8['l1d_warm_misses']}",
    })
    return objs, pairs


C_HARNESS_COMMON = r"""
#define _GNU_SOURCE
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <sys/syscall.h>
#include <linux/perf_event.h>

static int open_cycles(void) {
    struct perf_event_attr a;
    memset(&a, 0, sizeof a);
    a.type = PERF_TYPE_HARDWARE; a.size = sizeof a; a.config = PERF_COUNT_HW_CPU_CYCLES;
    a.exclude_kernel = 1; a.exclude_hv = 1; a.disabled = 0;
    return (int)syscall(SYS_perf_event_open, &a, 0, -1, -1, 0);
}
static uint64_t rd_fd(int fd) { uint64_t v = 0; if (fd < 0 || read(fd, &v, 8) != 8) return 0; return v; }
static double now_ns(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec * 1e9 + ts.tv_nsec; }
static volatile uint64_t sink = 0;
"""

C_HARNESS_X86 = C_HARNESS_COMMON + r"""
extern void blake3_servil_avx512_p16(const uint8_t *const *in, uint64_t n, const uint8_t *key, uint64_t t, uint64_t packed, uint8_t *out);
extern uint64_t cal_x86_st_ld(uint8_t *dst, const uint8_t *src, uint64_t val);
extern void cal_x86_stlf_clean(uint8_t *buf, uint64_t count);
extern void cal_x86_stlf_partial(uint8_t *buf, uint64_t count);
extern uint64_t ode_adler32(const uint8_t *a, uint64_t n);
extern uint64_t ode_adler32_aligned(const uint8_t *a, uint64_t n);
extern uint64_t cal_x86_l1d_stride(const uint8_t *base, uint64_t mask);

int main(int argc, char **argv) {
    int fd = open_cycles();
    const char *mode = fd >= 0 ? "perf_cycles" : "wall_ns";
    int rounds = argc > 1 ? atoi(argv[1]) : 9;

    /* Buffers */
    uint8_t *p16_raw[16];
    const uint8_t *p16_a[16], *p16_b[16];
    for (int i = 0; i < 16; i++) {
        p16_raw[i] = aligned_alloc(4096, 4096);
        memset(p16_raw[i], i + 1, 4096);
        p16_a[i] = p16_raw[i];
        p16_b[i] = p16_raw[i] + 7;
    }
    uint8_t *key = aligned_alloc(64, 64), *out = aligned_alloc(64, 512);
    memset(key, 3, 64);
    uint64_t packed = 0 | (1u << 8) | (2u << 16) | (64u << 24);

    uint8_t *big = aligned_alloc(4096, 256 * 4096);
    for (size_t i = 0; i < 256 * 4096; i++) big[i] = (uint8_t)(i * 13 + 7);
    uint8_t *stlf_buf = aligned_alloc(64, 64);
    memset(stlf_buf, 5, 64);

    printf("mode %s\n", mode);
    for (int r = 0; r < rounds; r++) {
        uint64_t c0, c1; double t0, t1; uint64_t acc = 0;

        /* 1. p16_align (n=4 blocks per call, 40000 reps) */
        const uint64_t rp1 = 40000;
        for (uint64_t k = 0; k < 2000; k++) blake3_servil_avx512_p16(p16_a, 4, key, k, packed, out);
        c0 = rd_fd(fd); t0 = now_ns();
        for (uint64_t k = 0; k < rp1; k++) blake3_servil_avx512_p16(p16_a, 4, key, k, packed, out);
        c1 = rd_fd(fd); t1 = now_ns();
        printf("sample p16_align A %.3f %.3f\n", (double)(c1 - c0) / rp1, (t1 - t0) / rp1);
        for (uint64_t k = 0; k < 2000; k++) blake3_servil_avx512_p16(p16_b, 4, key, k, packed, out);
        c0 = rd_fd(fd); t0 = now_ns();
        for (uint64_t k = 0; k < rp1; k++) blake3_servil_avx512_p16(p16_b, 4, key, k, packed, out);
        c1 = rd_fd(fd); t1 = now_ns();
        printf("sample p16_align B %.3f %.3f\n", (double)(c1 - c0) / rp1, (t1 - t0) / rp1);

        /* 2. alias_4k (100000 reps) */
        const uint64_t rp2 = 100000;
        for (uint64_t k = 0; k < 5000; k++) acc += cal_x86_st_ld(big, big + 0x10400, k);
        c0 = rd_fd(fd); t0 = now_ns();
        for (uint64_t k = 0; k < rp2; k++) acc += cal_x86_st_ld(big, big + 0x10400, k);
        c1 = rd_fd(fd); t1 = now_ns();
        printf("sample alias_4k A %.3f %.3f\n", (double)(c1 - c0) / rp2, (t1 - t0) / rp2);
        for (uint64_t k = 0; k < 5000; k++) acc += cal_x86_st_ld(big, big + 0x10000, k);
        c0 = rd_fd(fd); t0 = now_ns();
        for (uint64_t k = 0; k < rp2; k++) acc += cal_x86_st_ld(big, big + 0x10000, k);
        c1 = rd_fd(fd); t1 = now_ns();
        printf("sample alias_4k B %.3f %.3f\n", (double)(c1 - c0) / rp2, (t1 - t0) / rp2);

        /* 3. stlf_width (100000 reps) */
        const uint64_t rp3 = 100000;
        for (uint64_t k = 0; k < 5000; k++) cal_x86_stlf_clean(stlf_buf, 64);
        c0 = rd_fd(fd); t0 = now_ns();
        for (uint64_t k = 0; k < rp3; k++) cal_x86_stlf_clean(stlf_buf, 64);
        c1 = rd_fd(fd); t1 = now_ns();
        printf("sample stlf_width A %.3f %.3f\n", (double)(c1 - c0) / rp3, (t1 - t0) / rp3);
        for (uint64_t k = 0; k < 5000; k++) cal_x86_stlf_partial(stlf_buf, 64);
        c0 = rd_fd(fd); t0 = now_ns();
        for (uint64_t k = 0; k < rp3; k++) cal_x86_stlf_partial(stlf_buf, 64);
        c1 = rd_fd(fd); t1 = now_ns();
        printf("sample stlf_width B %.3f %.3f\n", (double)(c1 - c0) / rp3, (t1 - t0) / rp3);

        /* 4. adler_loop_align (256 B input, 50000 reps; A = 2-line aligned, B = 3-line default) */
        const uint64_t rp4 = 50000;
        for (uint64_t k = 0; k < 2000; k++) acc += ode_adler32_aligned(big, 256);
        c0 = rd_fd(fd); t0 = now_ns();
        for (uint64_t k = 0; k < rp4; k++) acc += ode_adler32_aligned(big, 256);
        c1 = rd_fd(fd); t1 = now_ns();
        printf("sample adler_loop_align A %.3f %.3f\n", (double)(c1 - c0) / rp4, (t1 - t0) / rp4);
        for (uint64_t k = 0; k < 2000; k++) acc += ode_adler32(big, 256);
        c0 = rd_fd(fd); t0 = now_ns();
        for (uint64_t k = 0; k < rp4; k++) acc += ode_adler32(big, 256);
        c1 = rd_fd(fd); t1 = now_ns();
        printf("sample adler_loop_align B %.3f %.3f\n", (double)(c1 - c0) / rp4, (t1 - t0) / rp4);

        /* 5. l1d_set_conflict (8 lines vs 16 lines in L1D set 0, 100000 reps) */
        const uint64_t rp5 = 100000;
        for (uint64_t k = 0; k < 5000; k++) acc += cal_x86_l1d_stride(big, 7 * 4096);
        c0 = rd_fd(fd); t0 = now_ns();
        for (uint64_t k = 0; k < rp5; k++) acc += cal_x86_l1d_stride(big, 7 * 4096);
        c1 = rd_fd(fd); t1 = now_ns();
        printf("sample l1d_set_conflict A %.3f %.3f\n", (double)(c1 - c0) / rp5, (t1 - t0) / rp5);
        for (uint64_t k = 0; k < 5000; k++) acc += cal_x86_l1d_stride(big, 15 * 4096);
        c0 = rd_fd(fd); t0 = now_ns();
        for (uint64_t k = 0; k < rp5; k++) acc += cal_x86_l1d_stride(big, 15 * 4096);
        c1 = rd_fd(fd); t1 = now_ns();
        printf("sample l1d_set_conflict B %.3f %.3f\n", (double)(c1 - c0) / rp5, (t1 - t0) / rp5);

        sink ^= acc ^ out[0] ^ stlf_buf[0];
    }
    return 0;
}
"""

C_HARNESS_ARM64 = C_HARNESS_COMMON + r"""
extern void arm_mix16_6(uint8_t *out, const uint8_t *d, const uint8_t *a);
extern void cal_arm_stlf_clean(uint8_t *buf);
extern void cal_arm_stlf_partial(uint8_t *buf);
extern uint64_t cal_arm_l1d_4(const uint8_t *base, uint64_t stride);
extern uint64_t cal_arm_l1d_8(const uint8_t *base, uint64_t stride);

int main(int argc, char **argv) {
    int fd = open_cycles();
    const char *mode = fd >= 0 ? "perf_cycles" : "wall_ns";
    int rounds = argc > 1 ? atoi(argv[1]) : 9;

    uint8_t *big = aligned_alloc(16384, 32 * 16384);
    for (size_t i = 0; i < 32 * 16384; i++) big[i] = (uint8_t)(i * 17 + 3);
    uint8_t *out = aligned_alloc(4096, 4096), *d = aligned_alloc(4096, 4096), *a = aligned_alloc(4096, 4096);
    memset(d, 11, 4096); memset(a, 29, 4096);
    uint8_t *stlf_buf = aligned_alloc(64, 64);
    memset(stlf_buf, 9, 64);

    printf("mode %s\n", mode);
    for (int r = 0; r < rounds; r++) {
        uint64_t c0, c1; double t0, t1; uint64_t acc = 0;

        /* 1. arm_mix_align (200000 reps) */
        const uint64_t rp1 = 200000;
        for (uint64_t k = 0; k < 5000; k++) arm_mix16_6(out, d, a);
        c0 = rd_fd(fd); t0 = now_ns();
        for (uint64_t k = 0; k < rp1; k++) arm_mix16_6(out, d, a);
        c1 = rd_fd(fd); t1 = now_ns();
        printf("sample arm_mix_align A %.3f %.3f\n", (double)(c1 - c0) / rp1, (t1 - t0) / rp1);
        for (uint64_t k = 0; k < 5000; k++) arm_mix16_6(out + 7, d + 7, a + 7);
        c0 = rd_fd(fd); t0 = now_ns();
        for (uint64_t k = 0; k < rp1; k++) arm_mix16_6(out + 7, d + 7, a + 7);
        c1 = rd_fd(fd); t1 = now_ns();
        printf("sample arm_mix_align B %.3f %.3f\n", (double)(c1 - c0) / rp1, (t1 - t0) / rp1);

        /* 2. arm_stlf_width (200000 reps) */
        const uint64_t rp2 = 200000;
        for (uint64_t k = 0; k < 5000; k++) cal_arm_stlf_clean(stlf_buf);
        c0 = rd_fd(fd); t0 = now_ns();
        for (uint64_t k = 0; k < rp2; k++) cal_arm_stlf_clean(stlf_buf);
        c1 = rd_fd(fd); t1 = now_ns();
        printf("sample arm_stlf_width A %.3f %.3f\n", (double)(c1 - c0) / rp2, (t1 - t0) / rp2);
        for (uint64_t k = 0; k < 5000; k++) cal_arm_stlf_partial(stlf_buf);
        c0 = rd_fd(fd); t0 = now_ns();
        for (uint64_t k = 0; k < rp2; k++) cal_arm_stlf_partial(stlf_buf);
        c1 = rd_fd(fd); t1 = now_ns();
        printf("sample arm_stlf_width B %.3f %.3f\n", (double)(c1 - c0) / rp2, (t1 - t0) / rp2);

        /* 3. arm_l1d_conflict (200000 reps) */
        const uint64_t rp3 = 200000;
        for (uint64_t k = 0; k < 5000; k++) acc += cal_arm_l1d_4(big, 16384);
        c0 = rd_fd(fd); t0 = now_ns();
        for (uint64_t k = 0; k < rp3; k++) acc += cal_arm_l1d_4(big, 16384);
        c1 = rd_fd(fd); t1 = now_ns();
        printf("sample arm_l1d_conflict A %.3f %.3f\n", (double)(c1 - c0) / rp3, (t1 - t0) / rp3);
        for (uint64_t k = 0; k < 5000; k++) acc += cal_arm_l1d_8(big, 16384);
        c0 = rd_fd(fd); t0 = now_ns();
        for (uint64_t k = 0; k < rp3; k++) acc += cal_arm_l1d_8(big, 16384);
        c1 = rd_fd(fd); t1 = now_ns();
        printf("sample arm_l1d_conflict B %.3f %.3f\n", (double)(c1 - c0) / rp3, (t1 - t0) / rp3);

        sink ^= acc ^ out[0] ^ out[7] ^ stlf_buf[0];
    }
    return 0;
}
"""


def run_hardware(target, objs, workdir, rounds=9, core=None):
    c_path = os.path.join(workdir, "cal_main.c")
    exe_path = os.path.join(workdir, "cal_main")
    with open(c_path, "w") as f:
        f.write(C_HARNESS_ARM64 if target == "arm64" else C_HARNESS_X86)
    cmd_cc = ["cc", "-O2", "-no-pie", "-o", exe_path, c_path] + objs
    r = subprocess.run(cmd_cc, capture_output=True, text=True)
    if r.returncode != 0:
        # Retry without -no-pie if toolchain defaults differently
        r = subprocess.run(["cc", "-O2", "-o", exe_path, c_path] + objs, capture_output=True, text=True)
    if r.returncode != 0:
        raise SystemExit(f"calibrate: cc failed:\n{r.stdout}\n{r.stderr}")
    run_cmd = (["taskset", "-c", str(core), exe_path, str(rounds)] if core is not None else [exe_path, str(rounds)])
    rr = subprocess.run(run_cmd, capture_output=True, text=True)
    if rr.returncode != 0:
        raise SystemExit(f"calibrate: harness failed:\n{rr.stdout}\n{rr.stderr}")
    mode = "wall_ns"
    samples = {}
    for line in rr.stdout.splitlines():
        parts = line.split()
        if not parts: continue
        if parts[0] == "mode":
            mode = parts[1]
        elif parts[0] == "sample":
            name, side, cyc, ns = parts[1], parts[2], float(parts[3]), float(parts[4])
            samples.setdefault(name, {"A_cyc": [], "B_cyc": [], "A_ns": [], "B_ns": []})
            samples[name][f"{side}_cyc"].append(cyc)
            samples[name][f"{side}_ns"].append(ns)
    return mode, samples


def main(argv=None):
    ap = argparse.ArgumentParser(description="Variant-ranking calibration for advice/estimate.py.")
    ap.add_argument("--arch", choices=sorted(estimate.ARCHS), required=True)
    ap.add_argument("--run", action="store_true", help="compile C harness and measure on this processor")
    ap.add_argument("--rounds", type=int, default=9)
    ap.add_argument("--core", type=int, default=None, help="optional taskset CPU core")
    ap.add_argument("--json-out", default=None, help="write full results JSON")
    args = ap.parse_args(argv)

    target = estimate.ARCHS[args.arch]["target"]
    with tempfile.TemporaryDirectory() as wd:
        objs, pairs = predict_arm64(args.arch, wd) if target == "arm64" else predict_x86(args.arch, wd)
        mode, samples = (run_hardware(target, objs, wd, rounds=args.rounds, core=args.core) if args.run else (None, {}))

    print(f"calibration arch={args.arch} ({estimate.ARCHS[args.arch]['name']}) target={target}" + (f" mode={mode}" if mode else " (predictions only)"))
    print(f"  {'pair':<18} {'pred_A':>8} {'pred_B':>8} {'pred_B/A':>9}  {'meas_A':>9} {'meas_B':>9} {'meas_B/A':>9}  rank")
    results = []
    for p in pairs:
        pa, pb = p["pred_a_warm"], p["pred_b_warm"]
        pr = pb / pa if pa > 0 else 0.0
        row = dict(p, pred_ratio=round(pr, 3))
        if p["name"] in samples:
            s = samples[p["name"]]
            use_cyc = mode == "perf_cycles" and statistics.median(s["A_cyc"]) > 0
            va = statistics.median(s["A_cyc"] if use_cyc else s["A_ns"])
            vb = statistics.median(s["B_cyc"] if use_cyc else s["B_ns"])
            mr = vb / va if va > 0 else 0.0
            unit = "cyc" if use_cyc else "ns"
            row.update({"unit": unit, "meas_a": round(va, 3), "meas_b": round(vb, 3),
                        "meas_a_ns": round(statistics.median(s["A_ns"]), 3),
                        "meas_b_ns": round(statistics.median(s["B_ns"]), 3),
                        "meas_ratio": round(mr, 3)})
            if p.get("advisory_only"):
                rank = f"hint ({mr:.3f}x)"
            else:
                agree = (pb > pa and vb > va) or (pb < pa and vb < va)
                rank = "AGREE" if agree else "DISAGREE"
            row["rank"] = rank
            print(f"  {p['name']:<18} {pa:8.1f} {pb:8.1f} {pr:8.2f}x  {va:8.2f}{unit[0]} {vb:8.2f}{unit[0]} {mr:8.2f}x  {rank}")
        else:
            print(f"  {p['name']:<18} {pa:8.1f} {pb:8.1f} {pr:8.2f}x  {'-':>9} {'-':>9} {'-':>9}  {p['hazards_a']} vs {p['hazards_b']}")
        results.append(row)

    if args.json_out:
        with open(args.json_out, "w") as f:
            json.dump({"arch": args.arch, "target": target, "mode": mode, "results": results}, f, indent=2)
    return 0


if __name__ == "__main__":
    sys.exit(main())
