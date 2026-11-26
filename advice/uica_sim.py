#!/usr/bin/env python3
"""advice/uica_sim.py: uiCA-style cycle-accurate out-of-order pipeline simulator for Ode.

Unlike coarse static lower bounds or LLVM scheduling-table throughput sums, this simulator models:
  1. Front-end fetch / op-cache windows (64 B cache-line boundaries) and decode/issue width;
  2. Macro-op fusion (`cmp`/`test`/`add`/`sub`/`dec` + conditional branch -> 1 fused uop);
  3. Zero-latency rename-stage move and zero-idiom elimination (`xor r,r`, `mov r,r`, `vmovdqa`);
  4. Finite ROB, dispatch width, and split (Zen / Apple M) vs. unified (Intel) scheduler queues;
  5. Real per-instruction `uops.info` port bitmasks (`advice/uops_ports.json`) with dynamic
     earliest-free / least-loaded port selection and measured fractional port occupancy;
  6. Multi-iteration steady-state loop simulation capturing inter-iteration overlap and
     loop-carried dependency chains.

Strictly advisory — never imported or relied on by `proof-core/odeverify` or `lang/odec.py`.
"""
import collections, heapq, json, math, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for d in (os.path.join(ROOT, "core"), os.path.join(ROOT, "arm64"), os.path.join(ROOT, "kcheck")):
    if d not in sys.path:
        sys.path.insert(0, d)

with open(os.path.join(HERE, "uops_ports.json"), "r", encoding="utf-8") as _f:
    _UOPS_DB = json.load(_f)["rows"]

# Microarchitecture pipeline parameters (calibrated from published specs + bare-metal PMU counters).
PIPELINES = {
    "zen5": {
        "uops_arch": "ZEN5",
        "target": "x86_64",
        "fe_width": 8,              # 8-wide dispatch/rename (dual 4-wide decode / op-cache)
        "opcache_line_uops": 12,    # max uops delivered per 64B op-cache window per cycle
        "rob_size": 448,
        "retire_width": 8,
        "int_dispatch_width": 6,    # Zen 5 integer execution dispatch width (calibrated via PMU: 14 ALU -> 3.01 cyc, 14 mov -> 2.01 cyc)
        "fp_dispatch_width": 6,     # Zen 5 widened FP/Vec dispatch (6/cyc; calibrated via PMU)
        "fp_sched_size": 96,
        "int_sched_size": 96,
        "agu_sched_size": 72,       # Zen 5 has separate ALU & AGU schedulers
        "alu_ports": ["ALU0", "ALU1", "ALU2", "ALU3", "ALU4", "ALU5"],
        "branch_ports": ["ALU0", "ALU1", "ALU2"],
        "load_ports": ["AGU0", "AGU1", "AGU2", "AGU3"],  # Zen 5 has 4 L1D load AGUs (PMU: 8 loads = 2.20 cyc)
        "store_ports": ["AGU0", "AGU1", "AGU2", "AGU3"],
        "store_data_ports": ["FP4", "FP5"],
        "fp_ports": ["FP0", "FP1", "FP2", "FP3"],
        "macro_fusion": True,
        "fuse_alu_jcc": True,       # AMD Zen fuses cmp/test/add/sub/and/or/dec + jcc
        "micro_fusion_fe": True,    # load+alu is 1 macro-op in Zen dispatch/ROB
        "mov_elim_gpr": True,
        "mov_elim_vec": True,
        "self_mov_elim": True,      # PMU: Zen 5 eliminates `mov rdx, rdx` (rand_00_scalar: 3.02 cyc)
        "split_sched": True,
        "branch_ends_fetch": True,  # PMU: Zen 5 loop back-edge closes fetch/dispatch cycle (2.01, 3.01, 6.00)
        # Zen 5 has native 512-bit FP pipes (PMU: 16 vpaddd/vpxord zmm = 4.01 cyc = 4.0/cyc)
        # and 2.000-cycle latency on all 512-bit integer ALU/logic/rotate ops (PMU: g1_14ops = 28.002 cyc)
        "use_measured_tp_occ": False,
        "zmm_min_lat": 2.0,
        "zmm_double_pump": False,
        "fp_cross_bypass": 0.0,
        "fp_cross_pipe_lat": 0.0,
    },
    "zen4": {
        "uops_arch": "ZEN4",
        "target": "x86_64",
        "fe_width": 6,
        "opcache_line_uops": 9,
        "rob_size": 320,
        "retire_width": 8,
        "int_dispatch_width": 6,
        "fp_dispatch_width": 6,     # PMU: Zen 4 dispatches 6 128-bit SSE ops/cyc (rand_02_sse=3.51, rand_08_sse=5.61)
        "fp_sched_size": 64,
        "int_sched_size": 96,       # Zen 4: 4x24 ALU + separate 3x24=72 AGU scheduler
        "agu_sched_size": 72,
        "alu_ports": ["ALU0", "ALU1", "ALU2", "ALU3"],
        "branch_ports": ["ALU0", "ALU1"],
        "load_ports": ["AGU0", "AGU1", "AGU2"],
        "store_ports": ["AGU0", "AGU1", "AGU2"],
        "store_data_ports": ["FP4", "FP5"],
        "fp_ports": ["FP0", "FP1", "FP2", "FP3"],
        "macro_fusion": True,
        "fuse_alu_jcc": True,
        "micro_fusion_fe": True,
        "mov_elim_gpr": True,
        "mov_elim_vec": True,
        "self_mov_elim": False,     # PMU: Zen 4 does not eliminate `mov rdx, rdx` (rand_00_scalar: 4.00 cyc)
        "split_sched": True,
        "branch_ends_fetch": False, # PMU: Zen 4 op-cache streams across back-edges (2.34, 2.51, 3.17)
        "use_measured_tp_occ": True,
        "zmm_double_pump": True,    # PMU: Zen 4 double-pumps 512-bit ZMM as 2x256-bit micro-ops (lat 1/1/2, g4=36.92)
        "fp_cross_bypass": 0.0,
        "fp_cross_pipe_lat": 0.0,
    },
    "zen3": {
        "uops_arch": "ZEN3",
        "target": "x86_64",
        "fe_width": 6,
        "opcache_line_uops": 8,
        "rob_size": 256,
        "retire_width": 8,
        "int_dispatch_width": 6,
        "fp_dispatch_width": 6,
        "fp_sched_size": 64,
        "int_sched_size": 96,       # Zen 3: 4x24 ALU + separate 48-entry AGU scheduler
        "agu_sched_size": 48,
        "alu_ports": ["ALU0", "ALU1", "ALU2", "ALU3"],
        "branch_ports": ["ALU0", "ALU1"],
        "load_ports": ["AGU0", "AGU1", "AGU2"],
        "store_ports": ["AGU0", "AGU1"],
        "store_data_ports": ["FP4", "FP5"],
        "fp_ports": ["FP0", "FP1", "FP2", "FP3"],
        "macro_fusion": True,
        "fuse_alu_jcc": True,
        "micro_fusion_fe": True,
        "mov_elim_gpr": True,
        "mov_elim_vec": True,
        "self_mov_elim": False,
        "split_sched": True,
        "branch_ends_fetch": True,  # PMU: Zen 3 closes fetch/dispatch on loop back-edge (3.01, 2.01, 4.01)
        "use_measured_tp_occ": True,
        "zmm_double_pump": False,
        "fp_cross_bypass": 0.0,
        "fp_cross_pipe_lat": 0.0,
    },
    "icelake": {
        "uops_arch": "ICL",
        "target": "x86_64",
        "fe_width": 5,
        "opcache_line_uops": 6,
        "rob_size": 352,
        "retire_width": 5,
        "int_dispatch_width": 5,
        "fp_dispatch_width": 5,
        "fp_sched_size": 160,
        "int_sched_size": 160,
        "alu_ports": ["p0", "p1", "p5", "p6"],
        "branch_ports": ["p0", "p6"],
        "load_ports": ["p2", "p3"],
        "store_ports": ["p4", "p9"],
        "store_data_ports": ["p7", "p8"],
        "fp_ports": ["p0", "p1", "p5"],
        "macro_fusion": True,
        "fuse_alu_jcc": True,
        "micro_fusion_fe": True,    # Intel fused-domain micro-fusion (load+alu, store = 1 FE/ROB uop, 2 port uops)
        "mov_elim_gpr": True,
        "mov_elim_vec": True,
        "self_mov_elim": False,     # PMU: Ice Lake does not eliminate `mov rdx, rdx` (rand_00_scalar: 4.35 cyc)
        "split_sched": False,
        "branch_ends_fetch": False, # Ice Lake LSD/IDQ buffers across taken loop back-edges smoothly
        "use_measured_tp_occ": False,
        "zmm_double_pump": False,
        "fp_cross_bypass": 0.0,
        "fp_cross_pipe_lat": 0.0,
    },
    "emr": {
        "uops_arch": "EMR",
        "target": "x86_64",
        "fe_width": 6,
        "opcache_line_uops": 8,
        "rob_size": 512,
        "retire_width": 8,
        "int_dispatch_width": 6,
        "fp_dispatch_width": 6,
        "fp_sched_size": 192,
        "int_sched_size": 192,
        "alu_ports": ["p0", "p1", "p5", "p6", "p10"],
        "branch_ports": ["p0", "p6"],
        "load_ports": ["p2", "p3", "p10"],
        "store_ports": ["p4", "p9"],
        "store_data_ports": ["p7", "p8"],
        "fp_ports": ["p0", "p1", "p5"],
        "macro_fusion": True,
        "fuse_alu_jcc": True,
        "micro_fusion_fe": True,
        "mov_elim_gpr": True,
        "mov_elim_vec": True,
        "self_mov_elim": False,
        "split_sched": False,
        "branch_ends_fetch": False,
        "use_measured_tp_occ": False,
        "zmm_double_pump": False,
        "fp_cross_bypass": 0.0,
        "fp_cross_pipe_lat": 0.0,
    },
    "apple_m": {
        "uops_arch": None,
        "target": "arm64",
        "fe_width": 8,              # PMU: Apple M6 steady-state dispatch (probe_mov_elim=1.72, rand_08_mixed=3.35)
        "opcache_line_uops": 8,
        "rob_size": 630,
        "retire_width": 8,
        "int_dispatch_width": 8,
        "fp_dispatch_width": 4,     # PMU: 4-wide NEON vector dispatch (vec_*_32 = 8.00 cyc = 4.00/cyc)
        "fp_sched_size": 120,
        "int_sched_size": 160,
        "alu_ports": ["I0", "I1", "I2", "I3", "I4", "I5"],  # PMU: 6 integer ALU pipes (probe_alu_wide=2.53 cyc)
        "branch_ports": ["I4", "I5"],
        "load_ports": ["L0", "L1", "L2"],      # PMU: 3 load pipes shared by GPR & NEON loads (ld_x_12=3.96, ld_q_12=3.99)
        "store_ports": ["S0", "S1"],
        "store_data_ports": ["S0", "S1"],
        "fp_ports": ["V0", "V1", "V2", "V3"],  # PMU: 4 symmetric NEON pipes (all lat=2.000 cyc, 4.00/cyc at 16 chains)
        "macro_fusion": True,
        "fuse_alu_jcc": False,
        "micro_fusion_fe": False,
        "mov_elim_gpr": True,
        "mov_elim_vec": True,
        "self_mov_elim": True,
        "split_sched": True,
        "branch_ends_fetch": False,
        "use_measured_tp_occ": False,
        "zmm_double_pump": False,
        "fp_cross_bypass": 0.0,
        "fp_cross_pipe_lat": 0.0,
    },
    "ampere1": {
        "uops_arch": None,
        "target": "arm64",
        "fe_width": 4,
        "opcache_line_uops": 4,
        "rob_size": 256,
        "retire_width": 4,
        "int_dispatch_width": 4,
        "fp_dispatch_width": 2,
        "fp_sched_size": 64,
        "int_sched_size": 64,
        "alu_ports": ["I0", "I1", "I2", "I3"],
        "branch_ports": ["I2", "I3"],
        "load_ports": ["L0", "L1"],
        "store_ports": ["S0", "S1"],
        "store_data_ports": ["S0", "S1"],
        "fp_ports": ["V0", "V1"],
        "macro_fusion": True,       # PMU: AmpereOne macro-fuses cmp+b.lo (3.52, 4.54, 5.03, 6.52 cyc)
        "fuse_alu_jcc": False,
        "micro_fusion_fe": False,
        "mov_elim_gpr": True,
        "mov_elim_vec": False,
        "self_mov_elim": False,
        "split_sched": True,
        "branch_ends_fetch": False,
        "use_measured_tp_occ": False,
        "zmm_double_pump": False,
        "fp_cross_bypass": 0.0,
        "fp_cross_pipe_lat": 0.0,
    },
}

_X86_COND_JCC = {"je", "jne", "jae", "jb", "ja", "jbe"}
_X86_FUSE_CMP = {"cmp64_rr", "cmp64_ri", "cmp64_rm", "test64_same", "test32_same"}
_X86_FUSE_ALU = {"add64_rr", "add64_ri", "sub64_rr", "sub64_ri", "and64_rr", "and64_ri", "dec64", "dec32", "dec8_al"}
_ARM_COND_BR = {"b_eq", "b_ne", "b_hs", "b_lo", "b_hi", "b_ls"}
_ARM_FUSE_CMP = {"cmp_rr", "cmp_ri", "subs_rr", "subs_ri", "adds_rr", "adds_ri"}


def _uop_spec_for_row(row_name, cls, pipe):
    """Return (uop_groups, latency, is_fp, is_elim, fe_uops) for one instruction row.

    `uop_groups` is a list of `(port_list, port_occ_cycles)` — one entry per dispatched micro-op
    that actually needs an execution port. Move/zero-idiom eliminated ops return `uop_groups = []`
    with `fe_uops = 1` (they still occupy front-end decode/rename/ROB, just zero execution ports!).
    """
    uarch = pipe["uops_arch"]
    is_vec_cls = cls.startswith(("vec_", "wide_"))

    # Rename-stage zero-idiom and move elimination
    if row_name in ("xor64_same", "xor32_same", "pxord512_same"):
        return [], 0.0, is_vec_cls, True, 1
    if row_name in ("mov64_rr", "mov32_rr", "mov_rr") and pipe["mov_elim_gpr"]:
        return [], 0.0, False, True, 1
    if row_name in ("mov128", "mov512") and pipe["mov_elim_vec"]:
        return [], 0.0, True, True, 1
    if row_name in ("nop", "vzeroupper"):
        return [], 0.0, False, True, 1

    if uarch is not None and row_name in _UOPS_DB and uarch in _UOPS_DB[row_name]:
        rec = _UOPS_DB[row_name][uarch]
        lat = float(rec["lat"])
        if cls in ("wide_alu", "wide_xor", "wide_shift", "wide_unpck") and pipe.get("zmm_min_lat"):
            lat = max(lat, pipe["zmm_min_lat"])
        fe_uops = max(1, int(rec["uops"]))
        tp = rec.get("tp")
        ports_spec = rec.get("ports") or []

        # Micro-fusion in fused domain (front-end & ROB): load+alu and store fuse into 1 FE/ROB uop
        # while still dispatching 2 unfused uops to the scheduler & execution ports.
        if pipe.get("micro_fusion_fe") and cls in ("alu_mem", "store", "vec_store", "wide_store"):
            fe_uops = 1

        if ports_spec:
            # Explicit port masks directly from uops.info!
            groups = []
            is_fp = is_vec_cls or any(p.startswith("FP") for _, ps in ports_spec for p in ps)
            total_port_uops = sum(cnt for cnt, _ in ports_spec)
            for cnt, ps in ports_spec:
                occ = 1.0
                if pipe["use_measured_tp_occ"] and tp is not None and len(ports_spec) == 1 and cnt == 1:
                    ideal_tp = 1.0 / max(1, len(ps))
                    if tp > ideal_tp * 1.15:
                        occ = tp * len(ps)
                if pipe.get("zmm_double_pump") and cls.startswith("wide_") and occ >= 1.8:
                    # Zen 4 double-pumps 512-bit ZMM as 2 consecutive 256-bit micro-ops through FP dispatch!
                    for _ in range(cnt * 2):
                        groups.append((ps, 1.0))
                    fe_uops = max(fe_uops, cnt * 2)
                else:
                    for _ in range(cnt):
                        groups.append((ps, occ))
            if not (pipe.get("micro_fusion_fe") and cls in ("alu_mem", "store", "vec_store", "wide_store")):
                fe_uops = max(fe_uops, total_port_uops)
            return groups, lat, is_fp, False, fe_uops

        # AMD Zen integer / load / store rows (uops.info gives uops, tp, lat; map to Zen ALU/AGU ports)
        if cls in ("load", "vec_load", "wide_load", "wide_bcast"):
            lports = pipe["load_ports"]
            occ = max(1.0, (tp * len(lports)) if (tp and pipe["use_measured_tp_occ"]) else 1.0)
            return [(lports, occ)], lat, is_vec_cls, False, fe_uops
        if cls in ("store", "vec_store", "wide_store"):
            sports = pipe["store_ports"]
            occ = max(1.0, (tp * len(sports)) if (tp and pipe["use_measured_tp_occ"]) else 1.0)
            return [(sports, occ)], lat, is_vec_cls, False, fe_uops
        if cls == "alu_mem":
            return [(pipe["load_ports"], 1.0), (pipe["alu_ports"], 1.0)], lat, False, False, 1 if pipe.get("micro_fusion_fe") else max(2, fe_uops)
        if cls in ("branch", "call", "ret"):
            return [(pipe["branch_ports"], 1.0)], lat, False, False, fe_uops
        aports = pipe["alu_ports"]
        if tp is not None and tp >= 0.45 and len(aports) >= 4:
            k = max(1, min(len(aports), round(1.0 / tp)))
            aports = aports[:k]
        return [(aports, 1.0) for _ in range(fe_uops)], lat, False, False, fe_uops

    # Fallback / AArch64 (`apple_m`, `ampere1`)
    # Note: on AArch64, `ldr qN` and `str qN` execute on the load/store queue (`is_fp = False`),
    # NOT the NEON ALU dispatch queue (verified on Apple M6: ld_q_12=3.99 cyc, rand_09_neon_mem=2.99 cyc).
    if cls in ("load", "vec_load"):
        return [(pipe["load_ports"], 1.0)], (5.0 if cls == "vec_load" else 4.0), False, False, 1
    if cls in ("store", "vec_store"):
        return [(pipe["store_ports"], 1.0)], 1.0, False, False, 1
    if cls in ("vec_alu", "vec_shift", "vec_shuf"):
        return [(pipe["fp_ports"], 1.0)], 2.0, True, False, 1
    if cls == "vec_crypto":
        # Empirically calibrated on Apple M6 (4.786 GHz):
        # sha256h/h2: lat=4.00 cyc, rTP=2.00 cyc; sha256su0: lat=2.00 cyc, rTP=1.00 cyc (independent pipe);
        # sha256su1: lat=3.00 cyc, rTP=1.00 cyc (independent pipe).
        p0 = [pipe["fp_ports"][0]]
        p1 = [pipe["fp_ports"][1]] if len(pipe["fp_ports"]) > 1 else p0
        if row_name in ("sha256h", "sha256h2"):
            return [(p0, 2.0)], 4.0, True, False, 1
        if row_name == "sha256su0":
            return [(p1, 1.0)], 2.0, True, False, 1
        if row_name == "sha256su1":
            return [(p1, 1.0)], 3.0, True, False, 1
        return [(p0, 1.0)], 3.0, True, False, 1
    if cls in ("branch", "call", "ret"):
        return [(pipe["branch_ports"], 1.0)], 1.0, False, False, 1
    return [(pipe["alu_ports"], 1.0)], 1.0, False, False, 1


def _can_fuse(prev_item, cur_item, pipe):
    """Return True if `prev_item` + `cur_item` macro-op fuse into a single uop in the front end."""
    if not pipe["macro_fusion"]:
        return False
    pr, cr = prev_item["row"], cur_item["row"]
    if pipe["target"] == "x86_64":
        if cr not in _X86_COND_JCC:
            return False
        if pr in _X86_FUSE_CMP:
            return True
        if pipe["fuse_alu_jcc"] and pr in _X86_FUSE_ALU:
            # `dec` fuses with je/jne on Zen & Intel; add/sub fuse with all jcc
            if pr.startswith("dec") and cr not in ("je", "jne"):
                return False
            return True
        return False
    # arm64 (Apple M-series fuses cmp/subs/adds + b.cc)
    return cr in _ARM_COND_BR and pr in _ARM_FUSE_CMP


def simulate_loop(seq, arch_name, iterations=12, overrides=None):
    """Run a uiCA-style cycle-accurate out-of-order simulation over `iterations` steady-state
    iterations of decoded instruction list `seq` (each item has `pc`, `end`, `len`, `row`,
    `class`, `reads`, `writes`).

    Returns a dictionary with:
      - `cycles_per_iter`: steady-state measured cycles per iteration
      - `iter_deltas`: last 4 per-iteration cycle deltas (for convergence inspection)
      - `bottleneck`: primary limiting stage (`frontend`, `fp_dispatch`, `rob`, `ports:<p>`, `dependency`)
      - `fused_pairs`: number of macro-op fused pairs per iteration
      - `eliminated_moves`: number of rename-eliminated moves/zeros per iteration
      - `fe_uops`: total front-end uops per iteration (after macro-op fusion)
      - `port_utilization`: per-port steady-state busy fraction (0..1)
    """
    if not seq:
        return {"cycles_per_iter": 0.0, "bottleneck": "empty", "fe_uops": 0, "fused_pairs": 0, "eliminated_moves": 0}
    pipe = dict(PIPELINES[arch_name])
    if overrides:
        pipe.update(overrides)

    # Step 1: Preprocess one iteration — apply macro-op fusion & annotate uops/ports/64B fetch windows.
    micro_seq = []
    fused_pairs = 0
    elim_count = 0
    i = 0
    n = len(seq)
    while i < n:
        it = seq[i]
        if i + 1 < n and _can_fuse(it, seq[i + 1], pipe):
            nxt = seq[i + 1]
            # Fused cmp/alu + jcc: 1 front-end uop, executes on branch/alu port with alu latency
            groups, lat, is_fp, is_elim, _ = _uop_spec_for_row(it["row"], it["class"], pipe)
            # Restrict fused op to ports that support branches if Intel/AMD branch port subset
            fused_groups = [(pipe["branch_ports"], 1.0)] if groups else [(pipe["branch_ports"], 1.0)]
            micro_seq.append({
                "pc": it["pc"],
                "line64": it["pc"] // 64,
                "row": f"{it['row']}+{nxt['row']}",
                "reads": (it["reads"] | nxt["reads"]) - {"zf", "cf"},
                "writes": it["writes"] - {"zf", "cf"},
                "groups": fused_groups,
                "lat": max(1.0, lat),
                "is_fp": False,
                "is_elim": False,
                "fe_uops": 1,
            })
            fused_pairs += 1
            i += 2
            continue
        groups, lat, is_fp, is_elim, fe_uops = _uop_spec_for_row(it["row"], it["class"], pipe)
        # Self-moves (`mov rdx, rdx`): eliminated on Zen 5 & Apple M6, 1 ALU cycle on Zen 4 / Ice Lake.
        if it["row"] in ("mov64_rr", "mov32_rr", "mov_rr") and is_elim and it["reads"] == it["writes"] and not pipe.get("self_mov_elim", True):
            groups, lat, is_elim = [(pipe["alu_ports"], 1.0)], 1.0, False
        # AArch64 canonical NEON register move is encoded as `orr vD.16b, vS.16b, vS.16b` (1 distinct read).
        if it["row"] == "orr_v" and len(it["reads"]) == 1 and pipe["mov_elim_vec"]:
            groups, lat, is_elim, fe_uops = [], 0.0, True, 1
        # Same-register vector XOR zero-idiom (`vpxord xmmX, xmmY, xmmY` or `eor vX, vY, vY`)
        if it["row"] in ("pxor128", "pxord512", "eor_v") and len(it["reads"]) == 1:
            groups, lat, is_elim, fe_uops = [], 0.0, True, 1
            it = dict(it, reads=set())
        # Same-register integer SUB zero-idiom (`sub rax, rax` where both inputs match)
        if it["row"] == "sub64_rr" and len(it["reads"]) == 1:
            groups, lat, is_elim, fe_uops = [], 0.0, True, 1
            it = dict(it, reads=set())
        if is_elim:
            elim_count += 1
        micro_seq.append({
            "pc": it["pc"],
            "line64": it["pc"] // 64,
            "row": it["row"],
            "reads": set(it["reads"]),
            "writes": set(it["writes"]),
            "groups": groups,
            "lat": lat,
            "is_fp": is_fp,
            "is_mem": it["class"] in ("load", "store", "vec_load", "vec_store", "wide_load", "wide_store", "wide_bcast"),
            "is_elim": is_elim,
            "fe_uops": fe_uops,
            "is_branch": it["class"] == "branch",
        })
        i += 1

    fe_uops_iter = sum(m["fe_uops"] for m in micro_seq)

    # Step 2: Out-of-order cycle-accurate dispatch + dynamic least-loaded port scheduling.
    # Register readiness (rename handles WAR/WAW automatically; only true RAW dependencies tracked!).
    reg_ready = collections.defaultdict(float)
    # Track last producer class & pipe per register (for cross-pipe FP bypass delay on Zen 5 / Apple M)
    reg_fp_kind = {}
    reg_pipe = {}
    fp_port_set = set(pipe["fp_ports"])
    fp_cross_pipe_lat = pipe.get("fp_cross_pipe_lat", 0.0)
    # Per-port occupied cycle sets (true out-of-order reservation stations: a ready younger uop
    # can execute in an earlier free cycle `t < later_op_cycle`!) and cumulative port load.
    port_busy = collections.defaultdict(set)
    port_work = collections.defaultdict(float)

    def next_free_cycle(p, t0, occ_int):
        t = int(math.ceil(t0))
        b = port_busy[p]
        while any((t + j) in b for j in range(occ_int)):
            t += 1
        return t

    # Front-end / Dispatch state
    fe_width = pipe["fe_width"]
    int_disp_width = pipe.get("int_dispatch_width", fe_width)
    fp_disp_width = pipe["fp_dispatch_width"]
    opcache_win = pipe["opcache_line_uops"]
    rob_size = pipe["rob_size"]
    retire_width = pipe["retire_width"]
    fp_sched = pipe["fp_sched_size"]
    int_sched = pipe["int_sched_size"]
    agu_sched = pipe.get("agu_sched_size")
    fp_bypass = pipe.get("fp_cross_bypass", 0.0)
    branch_ends_fetch = pipe.get("branch_ends_fetch", False)

    # Track dispatch cycle and completion cycle of every in-flight uop in the ROB (in-order deque)
    # and issue-completion cycle of uops occupying scheduler queues (out-of-order min-heaps!).
    rob_complete = collections.deque()   # completion cycle of each uop in program order
    fp_inflight = []                     # min-heap of issue-free cycles for FP scheduler
    int_inflight = []                    # min-heap of issue-free cycles for Int ALU scheduler
    agu_inflight = []                    # min-heap of issue-free cycles for separate AGU scheduler (AMD Zen)

    disp_cyc = 0
    disp_used = 0
    disp_int_used = 0
    disp_fp_used = 0

    stall_fe = 0
    stall_fp_disp = 0
    stall_rob = 0
    stall_sched = 0

    iter_disp_ends = []
    iter_exec_ends = []

    def advance_disp_cycle(new_cyc):
        nonlocal disp_cyc, disp_used, disp_int_used, disp_fp_used
        if new_cyc > disp_cyc:
            disp_cyc = new_cyc
            disp_used = 0
            disp_int_used = 0
            disp_fp_used = 0

    # Retirement pointer: earliest cycle at which the head of ROB can retire
    retire_cyc = 0
    retired_in_cyc = 0

    def retire_up_to(now_cyc):
        nonlocal retire_cyc, retired_in_cyc
        while rob_complete and rob_complete[0] <= now_cyc:
            rc = int(math.ceil(rob_complete[0]))
            if rc > retire_cyc:
                retire_cyc = rc
                retired_in_cyc = 0
            if retire_cyc > now_cyc:
                break
            rob_complete.popleft()
            retired_in_cyc += 1
            if retired_in_cyc >= retire_width:
                retire_cyc += 1
                retired_in_cyc = 0

    for it_idx in range(iterations):
        iter_max_done = float(disp_cyc)
        for op in micro_seq:
            u = op["fe_uops"]
            # Front-end / Dispatch width / split Int & FP dispatch width
            if disp_used + u > fe_width:
                stall_fe += 1
                advance_disp_cycle(disp_cyc + 1)
            if op["is_fp"] and (disp_fp_used + u > fp_disp_width):
                stall_fp_disp += 1
                advance_disp_cycle(disp_cyc + 1)
            if (not op["is_fp"]) and (not op["is_elim"]) and (disp_int_used + u > int_disp_width):
                stall_fe += 1
                advance_disp_cycle(disp_cyc + 1)

            # ROB back-pressure: wait until head retires if ROB is full
            retire_up_to(disp_cyc)
            while len(rob_complete) + u > rob_size:
                need_cyc = max(disp_cyc + 1, int(math.ceil(rob_complete[0])))
                stall_rob += need_cyc - disp_cyc
                advance_disp_cycle(need_cyc)
                retire_up_to(disp_cyc)

            # Scheduler queue back-pressure (split Int ALU / AGU / FP on Zen; split Int/FP on Apple M; unified on Intel).
            # Out-of-order schedulers free entries as soon as any uop issues (min-heap, not FIFO!).
            if pipe["split_sched"] and op["is_fp"]:
                q_inflight, q_cap = fp_inflight, fp_sched
            elif agu_sched is not None and op.get("is_mem"):
                q_inflight, q_cap = agu_inflight, agu_sched
            else:
                q_inflight, q_cap = int_inflight, int_sched
            while q_inflight and q_inflight[0] <= disp_cyc:
                heapq.heappop(q_inflight)
            while len(q_inflight) + len(op["groups"]) > q_cap:
                need_cyc = max(disp_cyc + 1, int(math.ceil(q_inflight[0])))
                stall_sched += need_cyc - disp_cyc
                advance_disp_cycle(need_cyc)
                while q_inflight and q_inflight[0] <= disp_cyc:
                    heapq.heappop(q_inflight)

            # Charge front-end & dispatch slots
            disp_used += u
            if op["is_fp"]:
                disp_fp_used += u
            elif not op["is_elim"]:
                disp_int_used += u

            # Compute data-ready time from RAW operand dependencies (plus FP bypass if switching FP op class)
            cur_fp_kind = op["row"] if op["is_fp"] else None
            data_ready = 0.0
            for r in op["reads"]:
                rt = reg_ready[r]
                if fp_bypass > 0.0 and cur_fp_kind is not None:
                    prev_k = reg_fp_kind.get(r)
                    if prev_k is not None and prev_k != cur_fp_kind:
                        rt += fp_bypass
                if rt > data_ready:
                    data_ready = rt
            earliest = max(float(disp_cyc), data_ready)

            # Dynamic least-loaded earliest-free port selection (true out-of-order uiCA scheduler)
            chosen_fp_port = None
            if not op["groups"]:
                exec_start = earliest
                exec_done = earliest + op["lat"]
            else:
                exec_done = earliest
                exec_start = earliest
                for ps, occ in op["groups"]:
                    occ_i = max(1, int(round(occ)))
                    # Compute per-port ready time (accounting for cross-pipe NEON bypass on Apple M)
                    best_p, best_st, best_key = None, 0, None
                    for p in ps:
                        p_ready = earliest
                        if fp_cross_pipe_lat > 0.0 and p in fp_port_set:
                            for r in op["reads"]:
                                rp = reg_pipe.get(r)
                                if rp is not None and rp in fp_port_set and rp != p:
                                    rt = reg_ready[r] + fp_cross_pipe_lat
                                    if rt > p_ready:
                                        p_ready = rt
                        st = next_free_cycle(p, p_ready, occ_i)
                        key = (st, port_work[p])
                        if best_key is None or key < best_key:
                            best_p, best_st, best_key = p, st, key
                    chosen, st = best_p, best_st
                    if chosen in fp_port_set:
                        chosen_fp_port = chosen
                    b = port_busy[chosen]
                    for j in range(occ_i):
                        b.add(st + j)
                    port_work[chosen] += occ_i
                    if st > exec_start:
                        exec_start = float(st)
                    if st + op["lat"] > exec_done:
                        exec_done = st + op["lat"]
                    heapq.heappush(q_inflight, float(st + 1))

            for w in op["writes"]:
                reg_ready[w] = exec_done
                if cur_fp_kind is not None:
                    reg_fp_kind[w] = cur_fp_kind
                if chosen_fp_port is not None:
                    reg_pipe[w] = chosen_fp_port
                elif w in reg_pipe:
                    del reg_pipe[w]
            if exec_done > iter_max_done:
                iter_max_done = exec_done
            for _ in range(u):
                rob_complete.append(exec_done)

        if branch_ends_fetch and disp_used > 0:
            advance_disp_cycle(disp_cyc + 1)
        iter_disp_ends.append(float(disp_cyc))
        max_done = max((reg_ready[r] for r in reg_ready), default=float(disp_cyc))
        iter_exec_ends.append(max(float(disp_cyc), max_done, iter_max_done))

    # Measure steady-state throughput from the last 6 iterations (LCM(2,3)=6 eliminates
    # period-2 and period-3 aliasing from overlapping OOO iterations after warm-up).
    disp_rate = 0.0
    if iterations >= 10:
        win = 6
        deltas = [iter_exec_ends[k] - iter_exec_ends[k - 1] for k in range(iterations - win, iterations)]
        cyc_per_iter = sum(deltas) / len(deltas)
        disp_deltas = [iter_disp_ends[k] - iter_disp_ends[k - 1] for k in range(iterations - win, iterations)]
        disp_rate = sum(disp_deltas) / len(disp_deltas)
        cyc_per_iter = max(cyc_per_iter, disp_rate)
    elif iterations >= 6:
        deltas = [iter_exec_ends[k] - iter_exec_ends[k - 1] for k in range(iterations - 4, iterations)]
        cyc_per_iter = sum(deltas) / len(deltas)
        disp_deltas = [iter_disp_ends[k] - iter_disp_ends[k - 1] for k in range(iterations - 4, iterations)]
        disp_rate = sum(disp_deltas) / len(disp_deltas)
        cyc_per_iter = max(cyc_per_iter, disp_rate)
    else:
        deltas = [iter_exec_ends[-1] / max(1, iterations)]
        cyc_per_iter = deltas[0]

    total_cyc = max(1.0, iter_exec_ends[-1])
    port_util = {p: round(w / total_cyc, 3) for p, w in sorted(port_work.items())}
    top_port, top_util = max(port_util.items(), key=lambda kv: kv[1], default=(None, 0.0))

    # Determine dominant bottleneck
    fe_bound = fe_uops_iter / fe_width
    fp_uops_iter = sum(m["fe_uops"] for m in micro_seq if m["is_fp"])
    fp_bound = fp_uops_iter / fp_disp_width
    if top_util >= 0.88:
        bottleneck = f"ports:{top_port}"
    elif stall_rob > 0 and stall_rob >= stall_fe and stall_rob >= stall_fp_disp:
        bottleneck = "rob"
    elif fp_bound >= cyc_per_iter * 0.88 and fp_uops_iter > 0:
        bottleneck = "fp_dispatch"
    elif fe_bound >= cyc_per_iter * 0.82 or (disp_rate >= cyc_per_iter * 0.95 and fe_bound >= cyc_per_iter * 0.65):
        bottleneck = "frontend"
    else:
        bottleneck = "dependency"

    return {
        "arch": arch_name,
        "cycles_per_iter": round(cyc_per_iter, 2),
        "iter_deltas": [round(d, 2) for d in deltas],
        "bottleneck": bottleneck,
        "fe_uops": fe_uops_iter,
        "fused_pairs": fused_pairs,
        "eliminated_moves": elim_count,
        "port_utilization": port_util,
        "stalls": {
            "fe": stall_fe,
            "fp_dispatch": stall_fp_disp,
            "rob": stall_rob,
            "sched": stall_sched,
        },
    }


def _line_for_pc(line_map, pc):
    if not line_map:
        return None
    for e in line_map:
        if e["pc"] == pc:
            return e["line"]
    return None


def critical_path_chain(seq, arch_name, line_map=None):
    """Purely static O(N) DAG longest-path backtrack over `seq` using calibrated per-CPU latencies.
    Returns `{"total_cycles": float, "steps": [{"pc", "line", "row", "lat"}, ...]}`."""
    if not seq or arch_name not in PIPELINES:
        return {"total_cycles": 0.0, "steps": []}
    pipe = PIPELINES[arch_name]
    reg_best = {}   # reg -> (ready_cyc, producer_idx)
    node_pred = {}
    node_info = {}
    best_end = (0.0, -1)
    for idx, it in enumerate(seq):
        _, lat, _, is_elim, _ = _uop_spec_for_row(it["row"], it["class"], pipe)
        if it["row"] in ("mov64_rr", "mov32_rr", "mov_rr") and is_elim and it["reads"] == it["writes"] and not pipe.get("self_mov_elim", True):
            lat = 1.0
        if it["row"] == "orr_v" and len(it["reads"]) == 1 and pipe["mov_elim_vec"]:
            lat = 0.0
        if it["row"] in ("pxor128", "pxord512", "eor_v", "sub64_rr") and len(it["reads"]) == 1:
            lat = 0.0
            reads = set()
        else:
            reads = set(it["reads"])
        start = 0.0
        pred = -1
        for r in reads:
            if r in reg_best and reg_best[r][0] > start:
                start, pred = reg_best[r]
        done = start + lat
        node_pred[idx] = pred
        node_info[idx] = {"pc": it["pc"], "line": _line_for_pc(line_map, it["pc"]), "row": it["row"], "lat": round(lat, 2)}
        for w in it["writes"]:
            if w not in ("zf", "cf") or len(it["writes"]) <= 2:
                reg_best[w] = (done, idx)
        if done > best_end[0]:
            best_end = (done, idx)
    chain = []
    cur = best_end[1]
    seen = set()
    while cur >= 0 and cur not in seen:
        seen.add(cur)
        chain.append(node_info[cur])
        cur = node_pred.get(cur, -1)
    chain.reverse()
    return {"total_cycles": round(best_end[0], 2), "steps": chain}


def static_lint_loop(seq, arch_name, line_map=None, sim_rep=None):
    """Purely static microarchitectural lint pass grounded in our 7-processor hardware findings.
    Returns a list of `{"kind": str, "line": int|None, "message": str}` dicts."""
    if not seq or arch_name not in PIPELINES:
        return []
    pipe = PIPELINES[arch_name]
    lints = []
    conds = _X86_COND_JCC if pipe["target"] == "x86_64" else _ARM_COND_BR
    fusers = (_X86_FUSE_CMP | (_X86_FUSE_ALU if pipe["fuse_alu_jcc"] else set())) if pipe["target"] == "x86_64" else _ARM_FUSE_CMP

    # 1. Broken macro-op fusion: flag-setter separated from conditional branch by 1-2 non-flag-writing ops
    if pipe["macro_fusion"]:
        for i, it in enumerate(seq):
            if it["row"] in conds and i >= 2:
                prev1 = seq[i - 1]
                if not _can_fuse(prev1, it, pipe) and not ({"zf", "cf"} & prev1["writes"]):
                    for gap in (2, 3):
                        if i - gap >= 0:
                            cand = seq[i - gap]
                            inter = seq[i - gap + 1:i]
                            if _can_fuse(cand, it, pipe) and all(not ({"zf", "cf"} & x["writes"]) for x in inter):
                                l1 = _line_for_pc(line_map, cand["pc"])
                                l2 = _line_for_pc(line_map, it["pc"])
                                loc = f"lines {l1}..{l2}" if (l1 and l2) else f"+0x{cand['pc']:x}..+0x{it['pc']:x}"
                                lints.append({
                                    "kind": "broken_macro_fusion",
                                    "line": l1,
                                    "message": (
                                        f"{loc}: `{cand['row']}` separated from `{it['row']}` by "
                                        f"`{', '.join(x['row'] for x in inter)}` prevents macro-op fusion "
                                        f"(moving `{cand['row']}` directly before `{it['row']}` saves 1 uop/iter)"
                                    ),
                                })
                                break

    # 2. Non-eliminated self-moves (`mov rdx, rdx` on Zen 4 / Zen 3 / Ice Lake)
    if not pipe.get("self_mov_elim", True):
        for it in seq:
            if it["row"] in ("mov64_rr", "mov32_rr", "mov_rr") and it["reads"] == it["writes"] and it["reads"]:
                ln = _line_for_pc(line_map, it["pc"])
                reg = next(iter(it["writes"]))
                loc = f"line {ln}" if ln else f"+0x{it['pc']:x}"
                lints.append({
                    "kind": "non_eliminated_self_move",
                    "line": ln,
                    "message": (
                        f"{loc}: self-move `{it['row']}` on `{reg}` is not rename-eliminated on "
                        f"{arch_name} (costs 1 ALU cycle and extends the dependency chain)"
                    ),
                })

    # 3. Apple Silicon NEON independent-chain saturation threshold (<12 live vector chains -> 3.0 vs 4.0 ops/cyc)
    if arch_name == "apple_m":
        vec_ops = [it for it in seq if it["class"] in ("vec_alu", "vec_shift", "vec_shuf")]
        if len(vec_ops) >= 12:
            vec_dsts = {w for it in vec_ops for w in it["writes"] if w.startswith("v")}
            bn = (sim_rep or {}).get("bottleneck", "")
            if 4 <= len(vec_dsts) < 12 and (bn.startswith("ports:V") or bn == "fp_dispatch"):
                ln = _line_for_pc(line_map, vec_ops[0]["pc"])
                lints.append({
                    "kind": "apple_neon_under_unrolled",
                    "line": ln,
                    "message": (
                        f"NEON loop writes only {len(vec_dsts)} distinct vector registers; Apple Silicon "
                        f"reaches ~3.0 ops/cyc at 8 independent chains and full 4.0 ops/cyc (+33%) at >=12 chains"
                    ),
                })

    return lints


TARGET_ARCHS = {
    "x86_64": ["zen5", "zen4", "zen3", "icelake"],
    "arm64": ["apple_m", "ampere1"],
}


def compare_all_archs(seq, target, line_map=None, iterations=12):
    """Run purely static pipeline analysis across all calibrated CPUs for `target` (<5 ms total)."""
    out = []
    for arch in TARGET_ARCHS.get(target, []):
        sim = simulate_loop(seq, arch, iterations=iterations)
        lints = static_lint_loop(seq, arch, line_map=line_map, sim_rep=sim)
        out.append({
            "arch": arch,
            "cycles_per_iter": sim["cycles_per_iter"],
            "bottleneck": sim["bottleneck"],
            "fused_pairs": sim["fused_pairs"],
            "eliminated_moves": sim["eliminated_moves"],
            "lint_count": len(lints),
        })
    return out

