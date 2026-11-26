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
import collections, json, math, os, sys

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
        "fp_dispatch_width": 4,     # Zen 5 FP/Vec dispatch bottleneck (4/cyc; calibrated via PMU)
        "fp_sched_size": 96,
        "int_sched_size": 144,
        "alu_ports": ["ALU0", "ALU1", "ALU2", "ALU3", "ALU4", "ALU5"],
        "branch_ports": ["ALU0", "ALU1", "ALU2"],
        "load_ports": ["AGU0", "AGU1", "AGU2"],
        "store_ports": ["AGU0", "AGU1", "AGU2", "AGU3"],
        "store_data_ports": ["FP4", "FP5"],
        "fp_ports": ["FP0", "FP1", "FP2", "FP3"],
        "macro_fusion": True,
        "fuse_alu_jcc": True,       # AMD Zen fuses cmp/test/add/sub/and/or/dec + jcc
        "mov_elim_gpr": True,
        "mov_elim_vec": True,
        "split_sched": True,
        # Calibrated fractional port occupancy scale for 512-bit FP ops when uops.info TP > 1/|ports|
        "use_measured_tp_occ": True,
    },
    "zen4": {
        "uops_arch": "ZEN4",
        "target": "x86_64",
        "fe_width": 6,
        "opcache_line_uops": 9,
        "rob_size": 320,
        "retire_width": 8,
        "fp_dispatch_width": 4,
        "fp_sched_size": 64,
        "int_sched_size": 96,
        "alu_ports": ["ALU0", "ALU1", "ALU2", "ALU3"],
        "branch_ports": ["ALU0", "ALU1"],
        "load_ports": ["AGU0", "AGU1", "AGU2"],
        "store_ports": ["AGU0", "AGU1", "AGU2"],
        "store_data_ports": ["FP4", "FP5"],
        "fp_ports": ["FP0", "FP1", "FP2", "FP3"],
        "macro_fusion": True,
        "fuse_alu_jcc": True,
        "mov_elim_gpr": True,
        "mov_elim_vec": True,
        "split_sched": True,
        "use_measured_tp_occ": True,
    },
    "zen3": {
        "uops_arch": "ZEN3",
        "target": "x86_64",
        "fe_width": 6,
        "opcache_line_uops": 8,
        "rob_size": 256,
        "retire_width": 8,
        "fp_dispatch_width": 4,
        "fp_sched_size": 64,
        "int_sched_size": 96,
        "alu_ports": ["ALU0", "ALU1", "ALU2", "ALU3"],
        "branch_ports": ["ALU0", "ALU1"],
        "load_ports": ["AGU0", "AGU1", "AGU2"],
        "store_ports": ["AGU0", "AGU1"],
        "store_data_ports": ["FP4", "FP5"],
        "fp_ports": ["FP0", "FP1", "FP2", "FP3"],
        "macro_fusion": True,
        "fuse_alu_jcc": True,
        "mov_elim_gpr": True,
        "mov_elim_vec": True,
        "split_sched": True,
        "use_measured_tp_occ": True,
    },
    "icelake": {
        "uops_arch": "ICL",
        "target": "x86_64",
        "fe_width": 5,
        "opcache_line_uops": 6,
        "rob_size": 352,
        "retire_width": 5,
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
        "mov_elim_gpr": True,
        "mov_elim_vec": True,
        "split_sched": False,
        "use_measured_tp_occ": True,
    },
    "emr": {
        "uops_arch": "EMR",
        "target": "x86_64",
        "fe_width": 6,
        "opcache_line_uops": 8,
        "rob_size": 512,
        "retire_width": 8,
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
        "mov_elim_gpr": True,
        "mov_elim_vec": True,
        "split_sched": False,
        "use_measured_tp_occ": True,
    },
    "apple_m": {
        "uops_arch": None,
        "target": "arm64",
        "fe_width": 8,
        "opcache_line_uops": 8,
        "rob_size": 630,
        "retire_width": 8,
        "fp_dispatch_width": 4,
        "fp_sched_size": 120,
        "int_sched_size": 160,
        "alu_ports": ["I0", "I1", "I2", "I3", "I4", "I5"],
        "branch_ports": ["I4", "I5"],
        "load_ports": ["L0", "L1", "L2"],
        "store_ports": ["S0", "S1"],
        "store_data_ports": ["S0", "S1"],
        "fp_ports": ["V0", "V1", "V2", "V3"],
        "macro_fusion": True,
        "fuse_alu_jcc": False,
        "mov_elim_gpr": True,
        "mov_elim_vec": True,
        "split_sched": True,
        "use_measured_tp_occ": False,
    },
    "ampere1": {
        "uops_arch": None,
        "target": "arm64",
        "fe_width": 4,
        "opcache_line_uops": 4,
        "rob_size": 256,
        "retire_width": 4,
        "fp_dispatch_width": 2,
        "fp_sched_size": 64,
        "int_sched_size": 64,
        "alu_ports": ["I0", "I1", "I2", "I3"],
        "branch_ports": ["I2", "I3"],
        "load_ports": ["L0", "L1"],
        "store_ports": ["S0", "S1"],
        "store_data_ports": ["S0", "S1"],
        "fp_ports": ["V0", "V1"],
        "macro_fusion": False,
        "fuse_alu_jcc": False,
        "mov_elim_gpr": True,
        "mov_elim_vec": False,
        "split_sched": True,
        "use_measured_tp_occ": False,
    },
}

_X86_COND_JCC = {"je", "jne", "jae", "jb", "ja", "jbe"}
_X86_FUSE_CMP = {"cmp64_rr", "cmp64_ri", "cmp64_rm", "test64_same", "test32_same"}
_X86_FUSE_ALU = {"add64_rr", "add64_ri", "sub64_rr", "sub64_ri", "and64_rr", "and64_ri", "dec64", "dec32", "dec8_al"}
_ARM_COND_BR = {"b_eq", "b_ne", "b_hs", "b_lo"}
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
        fe_uops = max(1, int(rec["uops"]))
        tp = rec.get("tp")
        ports_spec = rec.get("ports") or []

        if ports_spec:
            # Explicit port masks directly from uops.info!
            groups = []
            is_fp = is_vec_cls or any(p.startswith("FP") for _, ps in ports_spec for p in ps)
            total_port_uops = sum(cnt for cnt, _ in ports_spec)
            for cnt, ps in ports_spec:
                # Fractional port occupancy when measured TP > cnt / len(ps) (e.g. Zen 4 double-pumped
                # 512-bit ops or Zen 5 512-bit VPADDD with TP=0.37 on 4 FP pipes!).
                occ = 1.0
                if pipe["use_measured_tp_occ"] and tp is not None and len(ports_spec) == 1 and cnt == 1:
                    ideal_tp = 1.0 / max(1, len(ps))
                    if tp > ideal_tp * 1.15:
                        occ = tp * len(ps)
                for _ in range(cnt):
                    groups.append((ps, occ))
            return groups, lat, is_fp, False, max(fe_uops, total_port_uops)

        # AMD Zen integer / load / store rows (uops.info gives uops, tp, lat; map to Zen ALU/AGU ports)
        if cls in ("load", "vec_load", "wide_load", "wide_bcast"):
            # Wide 512-bit load on Zen 4/5: 1 load uop (double-pumped on Zen 4 via tp)
            lports = pipe["load_ports"]
            occ = max(1.0, (tp * len(lports)) if (tp and pipe["use_measured_tp_occ"]) else 1.0)
            return [(lports, occ)], lat, is_vec_cls, False, fe_uops
        if cls in ("store", "vec_store", "wide_store"):
            sports = pipe["store_ports"]
            occ = max(1.0, (tp * len(sports)) if (tp and pipe["use_measured_tp_occ"]) else 1.0)
            return [(sports, occ)], lat, is_vec_cls, False, fe_uops
        if cls == "alu_mem":
            return [(pipe["load_ports"], 1.0), (pipe["alu_ports"], 1.0)], lat, False, False, max(2, fe_uops)
        if cls in ("branch", "call", "ret"):
            return [(pipe["branch_ports"], 1.0)], lat, False, False, fe_uops
        # Pure integer ALU / LEA / shift
        aports = pipe["alu_ports"]
        if tp is not None and tp >= 0.45 and len(aports) >= 4:
            # Restricted ALU ops (e.g. complex LEA or shifts on fewer pipes)
            k = max(1, min(len(aports), round(1.0 / tp)))
            aports = aports[:k]
        return [(aports, 1.0) for _ in range(fe_uops)], lat, False, False, fe_uops

    # Fallback / AArch64 (`apple_m`, `ampere1`)
    if cls in ("load", "vec_load"):
        return [(pipe["load_ports"], 1.0)], (5.0 if cls == "vec_load" else 4.0), (cls == "vec_load"), False, 1
    if cls in ("store", "vec_store"):
        return [(pipe["store_ports"], 1.0)], 1.0, (cls == "vec_store"), False, 1
    if cls in ("vec_alu", "vec_shift", "vec_shuf"):
        return [(pipe["fp_ports"], 1.0)], 2.0, True, False, 1
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
            "is_elim": is_elim,
            "fe_uops": fe_uops,
        })
        i += 1

    fe_uops_iter = sum(m["fe_uops"] for m in micro_seq)

    # Step 2: Out-of-order cycle-accurate dispatch + dynamic least-loaded port scheduling.
    # Register readiness (rename handles WAR/WAW automatically; only true RAW dependencies tracked!).
    reg_ready = collections.defaultdict(float)
    # Port next-free fractional cycle (`port_free[p]`) and cumulative port work (`port_work[p]`)
    port_free = collections.defaultdict(float)
    port_work = collections.defaultdict(float)

    # Front-end / Dispatch state
    fe_width = pipe["fe_width"]
    fp_disp_width = pipe["fp_dispatch_width"]
    opcache_win = pipe["opcache_line_uops"]
    rob_size = pipe["rob_size"]
    retire_width = pipe["retire_width"]
    fp_sched = pipe["fp_sched_size"]
    int_sched = pipe["int_sched_size"]

    # Track dispatch cycle and completion cycle of every in-flight uop in the ROB (ring/deque).
    rob_complete = collections.deque()   # completion cycle of each uop in program order
    fp_inflight = collections.deque()    # execution-start cycle of in-flight FP uops (freed on issue)
    int_inflight = collections.deque()

    disp_cyc = 0
    disp_used = 0
    disp_fp_used = 0
    disp_line64 = None
    disp_line_uops = 0

    stall_fe = 0
    stall_fp_disp = 0
    stall_rob = 0
    stall_sched = 0

    iter_disp_ends = []
    iter_exec_ends = []

    def advance_disp_cycle(new_cyc):
        nonlocal disp_cyc, disp_used, disp_fp_used, disp_line64, disp_line_uops
        if new_cyc > disp_cyc:
            disp_cyc = new_cyc
            disp_used = 0
            disp_fp_used = 0
            disp_line64 = None
            disp_line_uops = 0

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
        for op in micro_seq:
            u = op["fe_uops"]
            # Front-end / Op-Cache / Dispatch width / FP dispatch width
            if disp_used + u > fe_width:
                stall_fe += 1
                advance_disp_cycle(disp_cyc + 1)
            if op["is_fp"] and (disp_fp_used + u > fp_disp_width):
                stall_fp_disp += 1
                advance_disp_cycle(disp_cyc + 1)
            if disp_line64 is not None and op["line64"] != disp_line64 and disp_line_uops >= opcache_win // 2:
                # Switching 64B op-cache line after consuming a half-window ends the fetch cycle
                stall_fe += 1
                advance_disp_cycle(disp_cyc + 1)
            elif disp_line64 == op["line64"] and disp_line_uops + u > opcache_win:
                stall_fe += 1
                advance_disp_cycle(disp_cyc + 1)

            # ROB back-pressure: wait until head retires if ROB is full
            retire_up_to(disp_cyc)
            while len(rob_complete) + u > rob_size:
                need_cyc = max(disp_cyc + 1, int(math.ceil(rob_complete[0])))
                stall_rob += need_cyc - disp_cyc
                advance_disp_cycle(need_cyc)
                retire_up_to(disp_cyc)

            # Scheduler queue back-pressure (split Int vs FP on Zen/Apple M; unified on Intel)
            q_inflight = fp_inflight if (pipe["split_sched"] and op["is_fp"]) else int_inflight
            q_cap = fp_sched if (pipe["split_sched"] and op["is_fp"]) else int_sched
            while q_inflight and q_inflight[0] <= disp_cyc:
                q_inflight.popleft()
            while len(q_inflight) + len(op["groups"]) > q_cap:
                need_cyc = max(disp_cyc + 1, int(math.ceil(q_inflight[0])))
                stall_sched += need_cyc - disp_cyc
                advance_disp_cycle(need_cyc)
                while q_inflight and q_inflight[0] <= disp_cyc:
                    q_inflight.popleft()

            # Charge front-end & dispatch slots
            disp_used += u
            if op["is_fp"]:
                disp_fp_used += u
            if disp_line64 != op["line64"]:
                disp_line64 = op["line64"]
                disp_line_uops = u
            else:
                disp_line_uops += u

            # Compute data-ready time from RAW operand dependencies
            data_ready = max((reg_ready[r] for r in op["reads"]), default=0.0)
            earliest = max(float(disp_cyc), data_ready)

            # Dynamic least-loaded earliest-free port selection (uiCA scheduler model)
            if not op["groups"]:
                exec_start = earliest
                exec_done = earliest + op["lat"]
            else:
                exec_done = earliest
                exec_start = earliest
                for ps, occ in op["groups"]:
                    # Pick port minimizing `max(earliest, port_free[p])`, tie-break by least total work!
                    chosen = min(ps, key=lambda p: (max(earliest, port_free[p]), port_work[p]))
                    st = max(earliest, port_free[chosen])
                    port_free[chosen] = st + occ
                    port_work[chosen] += occ
                    if st > exec_start:
                        exec_start = st
                    if st + op["lat"] > exec_done:
                        exec_done = st + op["lat"]
                    # Keep scheduler occupancy sorted approximately by issue cycle
                    q_inflight.append(st + 1.0)

            for w in op["writes"]:
                reg_ready[w] = exec_done
            for _ in range(u):
                rob_complete.append(exec_done)

        iter_disp_ends.append(float(disp_cyc))
        max_done = max((reg_ready[r] for r in reg_ready), default=float(disp_cyc))
        iter_exec_ends.append(max(float(disp_cyc), max_done))

    # Measure steady-state throughput from the last half of iterations (after pipeline warm-up)
    if iterations >= 6:
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
    elif fp_bound >= cyc_per_iter * 0.90 and fp_uops_iter > 0:
        bottleneck = "fp_dispatch"
    elif fe_bound >= cyc_per_iter * 0.90 or stall_fe > stall_fp_disp * 2:
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
