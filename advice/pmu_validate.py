#!/usr/bin/env python3
"""advice/pmu_validate.py: real + randomized microarchitectural validation suite for
`advice/uica_sim.py` vs. `advice/estimate.py` vs. `llvm-mca` against bare-metal hardware
`perf_event_open` cycle counters.

Assembles 24 loop kernels (real Ode kernels + targeted pipeline probes + reproducible randomized
instruction-mix loops) directly through `lang/odec.py` / `core/x86.tab`, predicts steady-state
cycles/iteration with both models (and `llvm-mca` when available), and with `--run` on Linux
measures real hardware cycles/iteration via `perf_event_open` on a pinned core.

Strictly advisory — never imported by `proof-core/odeverify`.
"""
import argparse, json, os, platform, random, re, statistics, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for d in (HERE, os.path.join(ROOT, "lang"), os.path.join(ROOT, "core"), os.path.join(ROOT, "kcheck")):
    if d not in sys.path:
        sys.path.insert(0, d)
import estimate, odec, table, uica_sim

# All kernels follow C ABI: `uint64_t fn(uint64_t iters, uint8_t *buf)` where `rdi = iters`, `rsi = buf` (4096 B, 64B aligned).

TARGETED_KERNELS = [
    ("probe_fusion_cmp", "probe", """target x86_64
fn probe_fusion_cmp as "k_probe_fusion_cmp" {
  xor eax, eax
  xor ecx, ecx
@lp:
  add rax, 1
  add rcx, 1
  cmp rcx, rdi
  jb @lp
  ret
}
"""),
    ("probe_nofusion_sep", "probe", """target x86_64
fn probe_nofusion_sep as "k_probe_nofusion_sep" {
  xor eax, eax
  xor ecx, ecx
@lp:
  add rcx, 1
  cmp rcx, rdi
  lea rax, [rax + 1]
  jb @lp
  ret
}
"""),
    ("probe_mov_elim", "probe", """target x86_64
fn probe_mov_elim as "k_probe_mov_elim" {
  mov r8, 1
  mov r9, 2
  mov r10, 3
  mov r11, 4
  xor ecx, ecx
@lp:
  mov rax, r8
  mov rdx, r9
  mov r8, r10
  mov r9, r11
  mov r10, rax
  mov r11, rdx
  mov rax, r8
  mov rdx, r9
  mov r8, r10
  mov r9, r11
  mov r10, rax
  mov r11, rdx
  add rcx, 1
  cmp rcx, rdi
  jb @lp
  mov rax, r8
  ret
}
"""),
    ("probe_alu_wide", "probe", """target x86_64
fn probe_alu_wide as "k_probe_alu_wide" {
  xor eax, eax
  xor edx, edx
  xor r8d, r8d
  xor r9d, r9d
  xor r10d, r10d
  xor r11d, r11d
  xor ecx, ecx
@lp:
  add rax, 1
  add rdx, 2
  add r8, 3
  add r9, 4
  add r10, 5
  add r11, 6
  add rax, 7
  add rdx, 8
  add r8, 9
  add r9, 10
  add r10, 11
  add r11, 12
  add rcx, 1
  cmp rcx, rdi
  jb @lp
  add rax, rdx
  add rax, r8
  add rax, r9
  add rax, r10
  add rax, r11
  ret
}
"""),
    ("probe_dep_chain", "probe", """target x86_64
fn probe_dep_chain as "k_probe_dep_chain" {
  mov rax, 1
  xor ecx, ecx
@lp:
  add rax, 1
  add rax, 3
  add rax, 5
  add rax, 7
  add rax, 9
  add rax, 11
  add rax, 13
  add rax, 15
  add rax, 17
  add rax, 19
  add rcx, 1
  cmp rcx, rdi
  jb @lp
  ret
}
"""),
    ("probe_load_mix", "probe", """target x86_64
fn probe_load_mix as "k_probe_load_mix" {
  xor eax, eax
  xor edx, edx
  xor r8d, r8d
  xor r9d, r9d
  xor ecx, ecx
@lp:
  add rax, qword ptr [rsi]
  add rdx, qword ptr [rsi + 8]
  add r8, qword ptr [rsi + 16]
  add r9, qword ptr [rsi + 24]
  add rax, qword ptr [rsi + 32]
  add rdx, qword ptr [rsi + 40]
  add r8, qword ptr [rsi + 48]
  add r9, qword ptr [rsi + 56]
  add rcx, 1
  cmp rcx, rdi
  jb @lp
  add rax, rdx
  add rax, r8
  add rax, r9
  ret
}
"""),
    ("real_adler32_body", "real", """target x86_64
fn real_adler32_body as "k_real_adler32_body" {
  mov rax, 1
  xor edx, edx
  xor ecx, ecx
@lp:
  mov r8, rcx
  and r8, 255
  mov r9, rsi
  add r9, r8
  movzx r10d, byte ptr [r9]
  add rax, r10
  add rdx, rax
  add rcx, 1
  cmp rcx, rdi
  jb @lp
  add rax, rdx
  ret
}
"""),
    ("real_ct_lt_body", "real", """target x86_64
fn real_ct_lt_body as "k_real_ct_lt_body" {
  xor eax, eax
  mov rcx, rdi
@lp:
  cmp rcx, 0
  je @dn
  sub rcx, 1
  mov r8, rcx
  and r8, 255
  mov r9, rsi
  add r9, r8
  movzx r10d, byte ptr [r9]
  movzx r11d, byte ptr [r9 + 256]
  add r11, r11
  add r11, rax
  add r11, 511
  sub r11, r10
  sub r11, r10
  shr r11, 9
  mov rax, r11
  jmp @lp
@dn:
  ret
}
"""),
    ("real_sse2_g_round", "real", """target x86_64
fn real_sse2_g_round as "k_real_sse2_g_round" {
  vmovdqu xmm0, xmmword ptr [rsi]
  vmovdqu xmm1, xmmword ptr [rsi + 16]
  vmovdqu xmm2, xmmword ptr [rsi + 32]
  vmovdqu xmm3, xmmword ptr [rsi + 48]
  vmovdqu xmm4, xmmword ptr [rsi + 64]
  vmovdqu xmm5, xmmword ptr [rsi + 80]
  xor ecx, ecx
@lp:
  vpaddd xmm0, xmm0, xmm4
  vpaddd xmm0, xmm0, xmm1
  vpxor xmm3, xmm3, xmm0
  vmovdqa xmm6, xmm3
  vpslld xmm3, xmm3, 16
  vpsrld xmm6, xmm6, 16
  vpor xmm3, xmm3, xmm6
  vpaddd xmm2, xmm2, xmm3
  vpxor xmm1, xmm1, xmm2
  vmovdqa xmm6, xmm1
  vpslld xmm1, xmm1, 20
  vpsrld xmm6, xmm6, 12
  vpor xmm1, xmm1, xmm6
  vpaddd xmm0, xmm0, xmm5
  vpaddd xmm0, xmm0, xmm1
  vpxor xmm3, xmm3, xmm0
  vmovdqa xmm6, xmm3
  vpslld xmm3, xmm3, 24
  vpsrld xmm6, xmm6, 8
  vpor xmm3, xmm3, xmm6
  vpaddd xmm2, xmm2, xmm3
  vpxor xmm1, xmm1, xmm2
  vmovdqa xmm6, xmm1
  vpslld xmm1, xmm1, 25
  vpsrld xmm6, xmm6, 7
  vpor xmm1, xmm1, xmm6
  add rcx, 1
  cmp rcx, rdi
  jb @lp
  vmovdqu xmmword ptr [rsi + 128], xmm0
  vzeroupper
  xor eax, eax
  ret
}
"""),
]

AVX512_KERNELS = [
    ("probe_zmm_vpaddd", "probe512", """target x86_64
fn probe_zmm_vpaddd as "k_probe_zmm_vpaddd" {
  vmovdqa32 zmm0, zmmword ptr [rsi]
  vmovdqa32 zmm1, zmmword ptr [rsi + 64]
  vmovdqa32 zmm2, zmmword ptr [rsi + 128]
  vmovdqa32 zmm3, zmmword ptr [rsi + 192]
  vmovdqa32 zmm4, zmmword ptr [rsi + 256]
  vmovdqa32 zmm5, zmmword ptr [rsi + 320]
  vmovdqa32 zmm6, zmmword ptr [rsi + 384]
  vmovdqa32 zmm7, zmmword ptr [rsi + 448]
  vmovdqa32 zmm8, zmmword ptr [rsi]
  xor ecx, ecx
@lp:
  vpaddd zmm0, zmm0, zmm8
  vpaddd zmm1, zmm1, zmm8
  vpaddd zmm2, zmm2, zmm8
  vpaddd zmm3, zmm3, zmm8
  vpaddd zmm4, zmm4, zmm8
  vpaddd zmm5, zmm5, zmm8
  vpaddd zmm6, zmm6, zmm8
  vpaddd zmm7, zmm7, zmm8
  vpaddd zmm0, zmm0, zmm8
  vpaddd zmm1, zmm1, zmm8
  vpaddd zmm2, zmm2, zmm8
  vpaddd zmm3, zmm3, zmm8
  vpaddd zmm4, zmm4, zmm8
  vpaddd zmm5, zmm5, zmm8
  vpaddd zmm6, zmm6, zmm8
  vpaddd zmm7, zmm7, zmm8
  add rcx, 1
  cmp rcx, rdi
  jb @lp
  vmovdqa32 zmmword ptr [rsi + 512], zmm0
  vzeroupper
  xor eax, eax
  ret
}
"""),
    ("probe_zmm_vpxord", "probe512", """target x86_64
fn probe_zmm_vpxord as "k_probe_zmm_vpxord" {
  vmovdqa32 zmm0, zmmword ptr [rsi]
  vmovdqa32 zmm1, zmmword ptr [rsi + 64]
  vmovdqa32 zmm2, zmmword ptr [rsi + 128]
  vmovdqa32 zmm3, zmmword ptr [rsi + 192]
  vmovdqa32 zmm4, zmmword ptr [rsi + 256]
  vmovdqa32 zmm5, zmmword ptr [rsi + 320]
  vmovdqa32 zmm6, zmmword ptr [rsi + 384]
  vmovdqa32 zmm7, zmmword ptr [rsi + 448]
  vmovdqa32 zmm8, zmmword ptr [rsi]
  xor ecx, ecx
@lp:
  vpxord zmm0, zmm0, zmm8
  vpxord zmm1, zmm1, zmm8
  vpxord zmm2, zmm2, zmm8
  vpxord zmm3, zmm3, zmm8
  vpxord zmm4, zmm4, zmm8
  vpxord zmm5, zmm5, zmm8
  vpxord zmm6, zmm6, zmm8
  vpxord zmm7, zmm7, zmm8
  vpxord zmm0, zmm0, zmm8
  vpxord zmm1, zmm1, zmm8
  vpxord zmm2, zmm2, zmm8
  vpxord zmm3, zmm3, zmm8
  vpxord zmm4, zmm4, zmm8
  vpxord zmm5, zmm5, zmm8
  vpxord zmm6, zmm6, zmm8
  vpxord zmm7, zmm7, zmm8
  add rcx, 1
  cmp rcx, rdi
  jb @lp
  vmovdqa32 zmmword ptr [rsi + 512], zmm0
  vzeroupper
  xor eax, eax
  ret
}
"""),
    ("probe_zmm_vprord", "probe512", """target x86_64
fn probe_zmm_vprord as "k_probe_zmm_vprord" {
  vmovdqa32 zmm0, zmmword ptr [rsi]
  vmovdqa32 zmm1, zmmword ptr [rsi + 64]
  vmovdqa32 zmm2, zmmword ptr [rsi + 128]
  vmovdqa32 zmm3, zmmword ptr [rsi + 192]
  vmovdqa32 zmm4, zmmword ptr [rsi + 256]
  vmovdqa32 zmm5, zmmword ptr [rsi + 320]
  vmovdqa32 zmm6, zmmword ptr [rsi + 384]
  vmovdqa32 zmm7, zmmword ptr [rsi + 448]
  xor ecx, ecx
@lp:
  vprord zmm0, zmm0, 16
  vprord zmm1, zmm1, 16
  vprord zmm2, zmm2, 16
  vprord zmm3, zmm3, 16
  vprord zmm4, zmm4, 16
  vprord zmm5, zmm5, 16
  vprord zmm6, zmm6, 16
  vprord zmm7, zmm7, 16
  vprord zmm0, zmm0, 12
  vprord zmm1, zmm1, 12
  vprord zmm2, zmm2, 12
  vprord zmm3, zmm3, 12
  vprord zmm4, zmm4, 12
  vprord zmm5, zmm5, 12
  vprord zmm6, zmm6, 12
  vprord zmm7, zmm7, 12
  add rcx, 1
  cmp rcx, rdi
  jb @lp
  vmovdqa32 zmmword ptr [rsi + 512], zmm0
  vzeroupper
  xor eax, eax
  ret
}
"""),
    ("probe_zmm_b3_g4", "real512", """target x86_64
fn probe_zmm_b3_g4 as "k_probe_zmm_b3_g4" {
  // 4 independent AVX-512 BLAKE3 G columns (exact instruction mix of p16, small loop footprint!)
  vmovdqa32 zmm0, zmmword ptr [rsi]
  vmovdqa32 zmm1, zmmword ptr [rsi + 64]
  vmovdqa32 zmm2, zmmword ptr [rsi + 128]
  vmovdqa32 zmm3, zmmword ptr [rsi + 192]
  vmovdqa32 zmm4, zmmword ptr [rsi + 256]
  vmovdqa32 zmm5, zmmword ptr [rsi + 320]
  vmovdqa32 zmm6, zmmword ptr [rsi + 384]
  vmovdqa32 zmm7, zmmword ptr [rsi + 448]
  vmovdqa32 zmm8, zmmword ptr [rsi + 512]
  vmovdqa32 zmm9, zmmword ptr [rsi + 576]
  vmovdqa32 zmm10, zmmword ptr [rsi + 640]
  vmovdqa32 zmm11, zmmword ptr [rsi + 704]
  vmovdqa32 zmm12, zmmword ptr [rsi + 768]
  vmovdqa32 zmm13, zmmword ptr [rsi + 832]
  vmovdqa32 zmm14, zmmword ptr [rsi + 896]
  vmovdqa32 zmm15, zmmword ptr [rsi + 960]
  vmovdqa32 zmm16, zmmword ptr [rsi]
  vmovdqa32 zmm17, zmmword ptr [rsi + 64]
  xor ecx, ecx
@lp:
  vpaddd zmm0, zmm0, zmm4
  vpaddd zmm1, zmm1, zmm5
  vpaddd zmm2, zmm2, zmm6
  vpaddd zmm3, zmm3, zmm7
  vpaddd zmm0, zmm0, zmm16
  vpaddd zmm1, zmm1, zmm16
  vpaddd zmm2, zmm2, zmm16
  vpaddd zmm3, zmm3, zmm16
  vpxord zmm12, zmm12, zmm0
  vpxord zmm13, zmm13, zmm1
  vpxord zmm14, zmm14, zmm2
  vpxord zmm15, zmm15, zmm3
  vprord zmm12, zmm12, 16
  vprord zmm13, zmm13, 16
  vprord zmm14, zmm14, 16
  vprord zmm15, zmm15, 16
  vpaddd zmm8, zmm8, zmm12
  vpaddd zmm9, zmm9, zmm13
  vpaddd zmm10, zmm10, zmm14
  vpaddd zmm11, zmm11, zmm15
  vpxord zmm4, zmm4, zmm8
  vpxord zmm5, zmm5, zmm9
  vpxord zmm6, zmm6, zmm10
  vpxord zmm7, zmm7, zmm11
  vprord zmm4, zmm4, 12
  vprord zmm5, zmm5, 12
  vprord zmm6, zmm6, 12
  vprord zmm7, zmm7, 12
  vpaddd zmm0, zmm0, zmm4
  vpaddd zmm1, zmm1, zmm5
  vpaddd zmm2, zmm2, zmm6
  vpaddd zmm3, zmm3, zmm7
  vpaddd zmm0, zmm0, zmm17
  vpaddd zmm1, zmm1, zmm17
  vpaddd zmm2, zmm2, zmm17
  vpaddd zmm3, zmm3, zmm17
  vpxord zmm12, zmm12, zmm0
  vpxord zmm13, zmm13, zmm1
  vpxord zmm14, zmm14, zmm2
  vpxord zmm15, zmm15, zmm3
  vprord zmm12, zmm12, 8
  vprord zmm13, zmm13, 8
  vprord zmm14, zmm14, 8
  vprord zmm15, zmm15, 8
  vpaddd zmm8, zmm8, zmm12
  vpaddd zmm9, zmm9, zmm13
  vpaddd zmm10, zmm10, zmm14
  vpaddd zmm11, zmm11, zmm15
  vpxord zmm4, zmm4, zmm8
  vpxord zmm5, zmm5, zmm9
  vpxord zmm6, zmm6, zmm10
  vpxord zmm7, zmm7, zmm11
  vprord zmm4, zmm4, 7
  vprord zmm5, zmm5, 7
  vprord zmm6, zmm6, 7
  vprord zmm7, zmm7, 7
  add rcx, 1
  cmp rcx, rdi
  jb @lp
  vmovdqa32 zmmword ptr [rsi + 1024], zmm0
  vzeroupper
  xor eax, eax
  ret
}
"""),
]


def generate_random_kernels(has_avx512=True, count=12, seed=20261125):
    """Generate `count` reproducible randomized loop kernels spanning scalar, memory, SSE, and AVX-512."""
    rng = random.Random(seed)
    gprs = ["rax", "rdx", "r8", "r9", "r10", "r11"]
    xmms = ["xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7"]
    zmms = [f"zmm{i}" for i in range(10)]
    out = []
    profiles = ["scalar", "scalar_mem", "sse", "mixed"] + (["avx512", "avx512_mix"] if has_avx512 else ["scalar", "sse"])
    for idx in range(count):
        prof = profiles[idx % len(profiles)]
        n_ins = rng.randint(10, 32)
        setup = ["  xor eax, eax", "  xor edx, edx", "  xor r8d, r8d", "  xor r9d, r9d",
                 "  xor r10d, r10d", "  xor r11d, r11d", "  xor ecx, ecx"]
        if prof in ("sse", "mixed"):
            for k in range(8):
                setup.append(f"  vmovdqu xmm{k}, xmmword ptr [rsi + {k * 16}]")
        if prof in ("avx512", "avx512_mix"):
            for k in range(10):
                setup.append(f"  vmovdqa32 zmm{k}, zmmword ptr [rsi + {k * 64}]")
        body = []
        for _ in range(n_ins):
            if prof == "scalar":
                op = rng.choice(["add_rr", "sub_rr", "and_ri", "or_rr", "shl_ri", "shr_ri", "lea", "mov_rr"])
            elif prof == "scalar_mem":
                op = rng.choice(["add_rr", "add_rm", "mov_rm", "mov_mr", "lea", "shr_ri", "sub_rr"])
            elif prof == "sse":
                op = rng.choice(["vpaddd_x", "vpxord_x", "vpslld_x", "vpsrld_x", "vpshufd_x", "vmovdqa_x", "vload_x"])
            elif prof == "mixed":
                op = rng.choice(["add_rr", "add_rm", "lea", "vpaddd_x", "vpxord_x", "vpshufd_x", "mov_rr"])
            elif prof == "avx512":
                op = rng.choice(["vpaddd_z", "vpxord_z", "vprord_z", "vshufi_z", "vmov_z", "vunpck_z"])
            else:
                op = rng.choice(["vpaddd_z", "vpxord_z", "vprord_z", "vload_z", "add_rr", "add_rm", "vshufi_z"])

            d, s = rng.choice(gprs), rng.choice(gprs)
            xd, xs1, xs2 = rng.choice(xmms), rng.choice(xmms), rng.choice(xmms)
            zd, zs1, zs2 = rng.choice(zmms), rng.choice(zmms), rng.choice(zmms)
            off8 = rng.randint(0, 15) * 8
            off16 = rng.randint(0, 15) * 16
            off64 = rng.randint(0, 15) * 64

            if op == "add_rr": body.append(f"  add {d}, {s}")
            elif op == "sub_rr": body.append(f"  sub {d}, {s}")
            elif op == "and_ri": body.append(f"  and {d}, {rng.randint(1, 127)}")
            elif op == "or_rr": body.append(f"  or {d}, {s}")
            elif op == "shl_ri": body.append(f"  shl {d}, {rng.randint(1, 7)}")
            elif op == "shr_ri": body.append(f"  shr {d}, {rng.randint(1, 7)}")
            elif op == "lea": body.append(f"  lea {d}, [{s} + {rng.randint(1, 64)}]")
            elif op == "mov_rr": body.append(f"  mov {d}, {s}")
            elif op == "add_rm": body.append(f"  add {d}, qword ptr [rsi + {off8}]")
            elif op == "mov_rm": body.append(f"  mov {d}, qword ptr [rsi + {off8}]")
            elif op == "mov_mr": body.append(f"  mov qword ptr [rsi + {2048 + off8}], {s}")
            elif op == "vpaddd_x": body.append(f"  vpaddd {xd}, {xs1}, {xs2}")
            elif op == "vpxord_x": body.append(f"  vpxor {xd}, {xs1}, {xs2}")
            elif op == "vpslld_x": body.append(f"  vpslld {xd}, {xs1}, {rng.randint(1, 16)}")
            elif op == "vpsrld_x": body.append(f"  vpsrld {xd}, {xs1}, {rng.randint(1, 16)}")
            elif op == "vpshufd_x": body.append(f"  pshufd {xd}, {xs1}, 0x4E")
            elif op == "vmovdqa_x": body.append(f"  vmovdqa {xd}, {xs1}")
            elif op == "vload_x": body.append(f"  vmovdqu {xd}, xmmword ptr [rsi + {off16}]")
            elif op == "vpaddd_z": body.append(f"  vpaddd {zd}, {zs1}, {zs2}")
            elif op == "vpxord_z": body.append(f"  vpxord {zd}, {zs1}, {zs2}")
            elif op == "vprord_z": body.append(f"  vprord {zd}, {zs1}, {rng.choice([7, 8, 12, 16])}")
            elif op == "vshufi_z": body.append(f"  vshufi32x4 {zd}, {zs1}, {zs2}, 0x4E")
            elif op == "vmov_z": body.append(f"  vmovdqa32 {zd}, {zs1}")
            elif op == "vunpck_z": body.append(f"  vpunpckldq {zd}, {zs1}, {zs2}")
            elif op == "vload_z": body.append(f"  vmovdqa32 {zd}, zmmword ptr [rsi + {off64}]")

        epilogue = []
        if prof in ("sse", "mixed"):
            epilogue.append("  vmovdqu xmmword ptr [rsi + 1536], xmm0")
            epilogue.append("  vzeroupper")
        elif prof in ("avx512", "avx512_mix"):
            epilogue.append("  vmovdqa32 zmmword ptr [rsi + 1536], zmm0")
            epilogue.append("  vzeroupper")
        name = f"rand_{idx:02d}_{prof}"
        src = (
            f"target x86_64\nfn {name} as \"k_{name}\" {{\n"
            + "\n".join(setup) + "\n@lp:\n"
            + "\n".join(body) + "\n"
            + "  add rcx, 1\n  cmp rcx, rdi\n  jb @lp\n"
            + "\n".join(epilogue) + "\n  ret\n}\n"
        )
        out.append((name, f"rand:{prof}", src))
    return out


def extract_loop_seq(obj_path, symbol):
    """Decode `symbol` and extract its main backward-edge loop body as simulator instruction items."""
    _, decoded = estimate.decode_object(obj_path, symbol, "x86_64")
    _, heads = estimate.load_table("x86_64")
    parsed = []
    for pc, end_pc, text in decoded:
        row, raw_bind = table.find(heads, table.parse_row(text))
        bind = estimate._conc_bind(raw_bind)
        reads, writes, jtgt, is_call = estimate.row_rw(row, bind, "x86_64")
        cls = estimate.classify_row(row.name, "x86_64")
        parsed.append({
            "pc": pc, "end": end_pc, "len": end_pc - pc, "row": row.name,
            "class": cls, "reads": reads, "writes": writes, "jump": jtgt,
        })
    # Pick the largest backward-edge loop
    best = None
    for idx, it in enumerate(parsed):
        if it["jump"] is not None and it["jump"] <= it["pc"]:
            head = next((k for k, x in enumerate(parsed) if x["pc"] == it["jump"]), None)
            if head is not None:
                body = parsed[head:idx + 1]
                if best is None or len(body) > len(best):
                    best = body
    return decoded, (best or parsed)


def run_llvm_mca(asm_loop_lines, mcpu):
    """Run `llvm-mca` on Intel-syntax loop lines if installed; return cycles/iter or None."""
    if not mcpu:
        return None
    text = ".intel_syntax noprefix\n" + "\n".join(asm_loop_lines) + "\n"
    try:
        r = subprocess.run(["llvm-mca", f"-mcpu={mcpu}", "-iterations=100"],
                           input=text, capture_output=True, text=True, timeout=15)
        if r.returncode != 0:
            return None
        m = re.search(r"Total Cycles:\s+(\d+)", r.stdout)
        if m:
            return round(int(m.group(1)) / 100.0, 2)
    except Exception:
        return None
    return None


HARNESS_C = r"""
#define _GNU_SOURCE
#include <errno.h>
#include <linux/perf_event.h>
#include <sched.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/syscall.h>
#include <unistd.h>

typedef uint64_t (*kfn_t)(uint64_t iters, uint8_t *buf);

struct kentry {
    const char *name;
    kfn_t fn;
};

__DECLS__

static struct kentry KERNELS[] = {
__TABLE__
};

static long perf_open_ev(uint32_t type, uint64_t config, int group_fd) {
    struct perf_event_attr pe;
    memset(&pe, 0, sizeof(pe));
    pe.type = type;
    pe.size = sizeof(pe);
    pe.config = config;
    pe.disabled = (group_fd == -1) ? 1 : 0;
    pe.exclude_kernel = 1;
    pe.exclude_hv = 1;
    return syscall(__NR_perf_event_open, &pe, 0, -1, group_fd, 0);
}

static int cmp_dbl(const void *a, const void *b) {
    double da = *(const double *)a, db = *(const double *)b;
    return (da > db) - (da < db);
}

int main(int argc, char **argv) {
    int core = (argc > 1) ? atoi(argv[1]) : 2;
    int rounds = (argc > 2) ? atoi(argv[2]) : 11;
    uint64_t iters = (argc > 3) ? (uint64_t)strtoull(argv[3], NULL, 0) : 20000ULL;

    cpu_set_t set;
    CPU_ZERO(&set);
    CPU_SET(core, &set);
    sched_setaffinity(0, sizeof(set), &set);

    uint8_t *buf = NULL;
    if (posix_memalign((void **)&buf, 64, 4096) != 0) { perror("memalign"); return 2; }
    for (int i = 0; i < 4096; i++) buf[i] = (uint8_t)((i * 37 + 13) & 0xff);

    int fd_cyc = (int)perf_open_ev(PERF_TYPE_HARDWARE, PERF_COUNT_HW_CPU_CYCLES, -1);
    if (fd_cyc < 0) { perror("perf_event_open cycles"); return 2; }
    int fd_ins = (int)perf_open_ev(PERF_TYPE_HARDWARE, PERF_COUNT_HW_INSTRUCTIONS, fd_cyc);

    int n = (int)(sizeof(KERNELS) / sizeof(KERNELS[0]));
    printf("[\n");
    for (int k = 0; k < n; k++) {
        volatile uint64_t sink = 0;
        /* Warmup */
        sink += KERNELS[k].fn(iters / 4, buf);
        double cyc_s[64], ins_s[64];
        int nr = rounds > 64 ? 64 : rounds;
        for (int r = 0; r < nr; r++) {
            uint64_t c = 0, ins = 0;
            ioctl(fd_cyc, PERF_EVENT_IOC_RESET, PERF_IOC_FLAG_GROUP);
            ioctl(fd_cyc, PERF_EVENT_IOC_ENABLE, PERF_IOC_FLAG_GROUP);
            sink += KERNELS[k].fn(iters, buf);
            ioctl(fd_cyc, PERF_EVENT_IOC_DISABLE, PERF_IOC_FLAG_GROUP);
            if (read(fd_cyc, &c, sizeof(c)) != sizeof(c)) c = 0;
            if (fd_ins >= 0 && read(fd_ins, &ins, sizeof(ins)) != sizeof(ins)) ins = 0;
            cyc_s[r] = (double)c / (double)iters;
            ins_s[r] = (double)ins / (double)iters;
        }
        qsort(cyc_s, nr, sizeof(double), cmp_dbl);
        qsort(ins_s, nr, sizeof(double), cmp_dbl);
        printf("  {\"name\": \"%s\", \"cycles\": %.3f, \"insns\": %.3f, \"min_cycles\": %.3f, \"max_cycles\": %.3f}%s\n",
               KERNELS[k].name, cyc_s[nr / 2], ins_s[nr / 2], cyc_s[0], cyc_s[nr - 1],
               (k + 1 < n) ? "," : "");
    }
    printf("]\n");
    free(buf);
    return 0;
}
"""


def main():
    ap = argparse.ArgumentParser(description="Validate uica_sim vs old estimate.py vs llvm-mca against hardware PMU.")
    ap.add_argument("--arch", default="zen5", choices=("zen5", "zen4", "zen3", "icelake", "emr"))
    ap.add_argument("--run", action="store_true", help="Compile, link, and measure on Linux bare-metal perf_event_open")
    ap.add_argument("--no-avx512", action="store_true", help="Skip AVX-512 kernels (e.g. for Zen 3)")
    ap.add_argument("--core", type=int, default=2)
    ap.add_argument("--rounds", type=int, default=11)
    ap.add_argument("--iters", type=int, default=20000)
    ap.add_argument("--mcpu", default=None, help="Optional llvm-mca -mcpu name (e.g. znver5, znver4, znver3, icelake-server)")
    ap.add_argument("--json-out", default=None)
    args = ap.parse_args()

    has_512 = not args.no_avx512 and args.arch != "zen3"
    kernels = list(TARGETED_KERNELS) + (list(AVX512_KERNELS) if has_512 else []) + generate_random_kernels(has_avx512=has_512)

    mcpu_default = {"zen5": "znver5", "zen4": "znver4", "zen3": "znver3", "icelake": "icelake-server", "emr": "emerald-rapids"}
    mcpu = args.mcpu or mcpu_default.get(args.arch)

    records = []
    with tempfile.TemporaryDirectory(prefix="ode_pmu_") as td:
        objs = []
        decls, entries = [], []
        for name, kind, src in kernels:
            p = os.path.join(td, f"{name}.ode")
            with open(p, "w", encoding="utf-8") as f:
                f.write(src)
            info = odec.compile_info(p, name)
            obj_p = os.path.join(td, f"{name}.o")
            with open(obj_p, "wb") as f:
                f.write(info["elf"])
            objs.append(obj_p)
            sym = info["symbol"]
            decls.append(f"extern uint64_t {sym}(uint64_t, uint8_t *);")
            entries.append(f'    {{"{name}", {sym}}},')

            decoded, loop_seq = extract_loop_seq(obj_p, sym)
            st = estimate.static_analyze(decoded, "x86_64", arch_name=args.arch)
            old_cyc = st["loops"][0]["body"]["compute_lower_bound"] if st["loops"] else st["whole_function"]["compute_lower_bound"]
            sim = uica_sim.simulate_loop(loop_seq, args.arch, iterations=12)

            # Extract loop assembly lines for optional llvm-mca comparison
            in_lp = False
            lp_asm = []
            for ln in src.splitlines():
                s = ln.strip()
                if s == "@lp:":
                    in_lp = True
                    continue
                if in_lp:
                    if s.startswith("@") or s.startswith("jb ") or s.startswith("jmp ") or s.startswith("je "):
                        if s.startswith(("jb ", "jmp ", "je ")):
                            break
                        continue
                    if s and not s.startswith("//"):
                        lp_asm.append(s)
            mca_cyc = run_llvm_mca(lp_asm, mcpu)
            records.append({
                "name": name,
                "kind": kind,
                "loop_insns": len(loop_seq),
                "old_bound": old_cyc,
                "uica_sim": sim["cycles_per_iter"],
                "uica_bottleneck": sim["bottleneck"],
                "fused_pairs": sim["fused_pairs"],
                "elim_moves": sim["eliminated_moves"],
                "llvm_mca": mca_cyc,
                "measured": None,
                "measured_insns": None,
            })

        if args.run:
            c_path = os.path.join(td, "bench.c")
            exe_path = os.path.join(td, "bench")
            with open(c_path, "w", encoding="utf-8") as f:
                f.write(HARNESS_C.replace("__DECLS__", "\n".join(decls)).replace("__TABLE__", "\n".join(entries)))
            subprocess.run(["cc", "-O2", c_path] + objs + ["-o", exe_path], check=True)
            r = subprocess.run([exe_path, str(args.core), str(args.rounds), str(args.iters)],
                               capture_output=True, text=True, check=True)
            meas_by_name = {row["name"]: row for row in json.loads(r.stdout)}
            for rec in records:
                m = meas_by_name[rec["name"]]
                rec["measured"] = m["cycles"]
                rec["measured_insns"] = m["insns"]

    # Print summary table + accuracy metrics (% within 10% and median abs error!)
    print(f"=== PMU Validation ({args.arch}, {len(records)} kernels) ===")
    hdr = f"{'kernel':22s} {'kind':12s} {'ins':>3s} {'old':>6s} {'uica':>6s} {'mca':>6s} {'meas':>7s} {'old%':>7s} {'uica%':>7s} {'mca%':>7s}  bottleneck"
    print(hdr)
    print("-" * len(hdr))
    old_errs, uica_errs, mca_errs = [], [], []
    for r in records:
        meas = r["measured"]
        o_s = f"{r['old_bound']:6.2f}"
        u_s = f"{r['uica_sim']:6.2f}"
        m_s = f"{r['llvm_mca']:6.2f}" if r["llvm_mca"] is not None else "     -"
        if meas is not None and meas > 0:
            oe = 100.0 * (r["old_bound"] - meas) / meas
            ue = 100.0 * (r["uica_sim"] - meas) / meas
            old_errs.append(abs(oe))
            uica_errs.append(abs(ue))
            me_s = "      -"
            if r["llvm_mca"] is not None:
                me = 100.0 * (r["llvm_mca"] - meas) / meas
                mca_errs.append(abs(me))
                me_s = f"{me:+6.1f}%"
            print(f"{r['name']:22s} {r['kind']:12s} {r['loop_insns']:3d} {o_s} {u_s} {m_s} {meas:7.2f} {oe:+6.1f}% {ue:+6.1f}% {me_s}  {r['uica_bottleneck']}")
        else:
            print(f"{r['name']:22s} {r['kind']:12s} {r['loop_insns']:3d} {o_s} {u_s} {m_s}       -       -       -       -  {r['uica_bottleneck']}")

    summary = {"arch": args.arch, "count": len(records), "records": records}
    if old_errs:
        def _stats(errs):
            w10 = sum(1 for e in errs if e <= 10.0)
            w15 = sum(1 for e in errs if e <= 15.0)
            return {
                "n": len(errs),
                "within_10pct": w10,
                "within_10pct_rate": round(100.0 * w10 / len(errs), 1),
                "within_15pct": w15,
                "median_abs_err_pct": round(statistics.median(errs), 1),
                "mean_abs_err_pct": round(statistics.mean(errs), 1),
            }
        summary["old_bound_accuracy"] = _stats(old_errs)
        summary["uica_sim_accuracy"] = _stats(uica_errs)
        if mca_errs:
            summary["llvm_mca_accuracy"] = _stats(mca_errs)
        print("\n=== Accuracy Summary (% within 10% of bare-metal measured cycles) ===")
        for label, key in [("old estimate.py", "old_bound_accuracy"), ("uica_sim.py    ", "uica_sim_accuracy"), ("llvm-mca       ", "llvm_mca_accuracy")]:
            if key in summary:
                st = summary[key]
                print(f"  {label}: {st['within_10pct']}/{st['n']} ({st['within_10pct_rate']:.1f}%) within 10% | "
                      f"{st['within_15pct']}/{st['n']} within 15% | median abs err {st['median_abs_err_pct']:.1f}% | mean {st['mean_abs_err_pct']:.1f}%")

    if args.json_out:
        with open(args.json_out, "w", encoding="utf-8") as f:
            json.dump(summary, f, indent=2)
            f.write("\n")


if __name__ == "__main__":
    main()
