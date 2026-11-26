#!/usr/bin/env python3
"""estimate: static compute bounds and exact memory-access analysis for compiled Ode functions
(both x86-64 and AArch64). Strictly advisory — relied on for nothing by the verifier.

Static analysis reads the instruction table (`core/x86.tab` or `arm64/arm64.tab`) directly for operand
reads/writes and combines them with per-microarchitecture parameters (`advice/arch.json`).
Memory analysis runs the concrete table interpreter (`core/conc.py`) on stated starting register values
and buffer alignments to record every memory read and write, then computes exact architectural hazards
(cache-line splits, page crossings, store-to-load forwarding stalls, 4K aliasing, and L1D cache-set
pressure), pinned to source lines when a source map is provided."""
import collections, json, math, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for d in (HERE, os.path.join(ROOT, "core"), os.path.join(ROOT, "arm64"), os.path.join(ROOT, "kcheck")):
    if d not in sys.path:
        sys.path.insert(0, d)
import conc, table, uica_sim

with open(os.path.join(HERE, "arch.json")) as _f:
    ARCHS = {k: v for k, v in json.load(_f).items() if not k.startswith("_")}

DEFAULT_ARCH = {"x86_64": "zen5", "arm64": "apple_m"}

_TABLES = {}


def load_table(target):
    if target not in _TABLES:
        path = os.path.join(ROOT, "arm64", "arm64.tab") if target == "arm64" else os.path.join(ROOT, "core", "x86.tab")
        rows = table.read(path)
        _TABLES[target] = (rows, table.by_head(rows))
    return _TABLES[target]


def decode_object(obj_path, symbol, target=None):
    """Decode one function from an ELF object into (target, [(pc, end_pc, row_text)])."""
    import obj as aobj
    mach = aobj.machine(obj_path)
    if target is None:
        target = "arm64" if mach == "arm64" else "x86_64"
    if target == "arm64":
        return "arm64", aobj.read(obj_path, symbol)
    import kdecode
    rows, _ = kdecode.read(obj_path, symbol, 0, 0)
    return "x86_64", rows


def classify_row(row_name, target):
    """Map an instruction row name from x86.tab or arm64.tab to its microarchitecture cost class."""
    if target == "arm64":
        if row_name == "nop": return "nop"
        if row_name == "mov_rr": return "mov_rr"
        if row_name == "bl": return "call"
        if row_name == "ret": return "ret"
        if row_name in ("b", "b_eq", "b_ne", "b_hs", "b_lo", "b_hi", "b_ls"): return "branch"
        if row_name in ("ld1_4s", "ldr128", "ldr128_sp"): return "vec_load"
        if row_name in ("st1_4s", "str128", "str128_sp"): return "vec_store"
        if row_name.startswith("ldr"): return "load"
        if row_name.startswith("str"): return "store"
        if row_name in ("eor_v", "orr_v", "and_v", "add_4s"): return "vec_alu"
        if row_name in ("ushr_4s", "shl_4s"): return "vec_shift"
        if row_name in ("rev32_8h", "uzp1_4s", "uzp2_4s", "zip1_4s", "zip2_4s", "zip1_2d", "zip2_2d", "ext_4", "ext_8", "ext_12"): return "vec_shuf"
        return "alu"
    # x86_64
    if row_name == "nop": return "nop"
    if row_name in ("xor64_same", "xor32_same", "pxord512_same"): return "zero"
    if row_name in ("mov64_rr", "mov32_rr", "movzx8_rr"): return "mov_rr"
    if row_name in ("lea", "lea_data"): return "lea"
    if row_name in ("jmp", "je", "jne", "jae", "jb", "ja", "jbe"): return "branch"
    if row_name == "call": return "call"
    if row_name == "ret": return "ret"
    if row_name == "vzeroupper": return "nop"
    if row_name in ("mov64_rm", "mov32_rm", "movzx8_rm", "pop"): return "load"
    if row_name in ("mov64_mr", "mov8_m_al", "mov8_mi", "push"): return "store"
    if row_name.endswith("_rm"): return "alu_mem"
    if row_name in ("loadu128", "const128"): return "vec_load"
    if row_name == "storeu128": return "vec_store"
    if row_name in ("mov128", "movq128", "paddd128", "pxor128", "pand128", "por128"): return "vec_alu"
    if row_name in ("prord128", "pslld128", "psrld128"): return "vec_shift"
    if row_name in ("pshufb128", "pshufd128", "shufps128", "unpckldq", "unpckhdq", "unpcklqdq", "pblendd128", "pblendw128"): return "vec_shuf"
    if row_name == "mov512": return "wide_mov"
    if row_name in ("load512a", "load512", "load512i"): return "wide_load"
    if row_name in ("store512a", "store512"): return "wide_store"
    if row_name.startswith("broadcast"): return "wide_bcast"
    if row_name in ("pxord512",): return "wide_xor"
    if row_name in ("paddd512", "paddd512m", "paddd512c", "paddd512k", "pcmpud512"): return "wide_alu"
    if row_name == "prord512": return "wide_shift"
    if row_name in ("unpckldq512", "unpckhdq512", "unpcklqdq512", "unpckhqdq512"): return "wide_unpck"
    if row_name == "shufi32x4": return "wide_shuf"
    return "alu"


def _conc_bind(bind):
    """Convert string bindings from table.find into the typed bindings conc.run expects."""
    out = {}
    for k, v in bind.items():
        if not isinstance(v, str):
            out[k] = v
        elif k in table.REGISTERS:
            out[k] = v[1:] if v.startswith(".") else v
        elif k in table.VECTORS or k in table.WIDE or k in table.MASKS:
            out[k] = int(v, 0)
        elif k in table.NUMBERS:
            try:
                out[k] = int(v, 0)
            except ValueError:
                out[k] = v   # symbolic call target name (e.g. "arm_mix16_3")
        else:
            out[k] = v
    return out


def _expr_reads(e, bind, out):
    if e[0] == "number":
        return
    if e[0] == "lane":
        out.add(f"v{bind[e[1]]}")
        return
    if e[0] == "name":
        n = e[1]
        if n in table.REGISTERS: out.add(bind[n])
        elif n in table.VECTORS: out.add(f"v{bind[n]}")
        elif n in table.WIDE: out.add(f"v{bind[table.WIDE[n]]}")
        elif n in table.MASKS: out.add(f"k{bind[n]}")
        elif n in ("zf", "cf"): out.add(n)
        elif n not in table.NUMBERS and n != table.UNKNOWN and n not in conc.CONC:
            out.add(n)
        return
    if e[0] == "call":
        for a in e[2]:
            _expr_reads(a, bind, out)


def _frame_slot(e, bind, sp_name):
    """If memory expression `memK(sp_or_on16(sp), const)` refers to a static frame slot, return its key."""
    if e[0] != "call" or e[1] not in table.SIZES:
        return None
    args = e[2]
    if len(args) != 2:
        return None
    base, off = args
    is_sp = (base[0] == "name" and (base[1] == sp_name or (base[1] in table.REGISTERS and bind.get(base[1]) == sp_name)))
    if not is_sp and base[0] == "call" and base[1] == "on16" and len(base[2]) == 1:
        inner = base[2][0]
        is_sp = inner[0] == "name" and inner[1] == sp_name
    if not is_sp:
        return None
    if off[0] == "number":
        val = off[1]
    elif off[0] == "name" and off[1] in table.NUMBERS:
        val = bind[off[1]]
    else:
        return None
    return f"frame:{val}:{table.SIZES[e[1]]}"


def row_rw(row, bind, target):
    """Return (reads: set[str], writes: set[str], jump_target: int|None, is_call: bool) from row.effect."""
    sp_name = "sp" if target == "arm64" else "rsp"
    reads, writes = set(), set()
    jump_target, is_call = None, False
    for st in row.effect:
        if st[0] == "nothing":
            continue
        if st[0] == "jump":
            if st[2] is not None:
                reads.add(st[2][0])
            t = st[1]
            if t[0] == "name" and t[1] in table.NUMBERS and isinstance(bind.get(t[1]), int):
                jump_target = bind[t[1]]
            elif t[0] == "number":
                jump_target = t[1]
            continue
        if st[0] == "call":
            is_call = True
            if len(st) == 3:
                writes.add(st[2])
            continue
        if st[0] == "return":
            if len(st) == 2:
                reads.add(st[1])
            continue
        if st[0] == "set":
            _, lhs, rhs = st
            _expr_reads(rhs, bind, reads)
            if rhs[0] == "call":
                slot = _frame_slot(rhs, bind, sp_name)
                if slot:
                    reads.add(slot)
            if lhs[0] == "call":
                for a in lhs[2]:
                    _expr_reads(a, bind, reads)
                slot = _frame_slot(lhs, bind, sp_name)
                if slot:
                    writes.add(slot)
            elif lhs[0] == "name":
                p = lhs[1]
                if p in table.REGISTERS: writes.add(bind[p])
                elif p in table.VECTORS: writes.add(f"v{bind[p]}")
                elif p in table.WIDE: writes.add(f"v{bind[table.WIDE[p]]}")
                elif p in table.MASKS: writes.add(f"k{bind[p]}")
                elif p in ("zf", "cf"): writes.add(p)
                elif p != "above128": writes.add(p)
    # Zeroing idioms break false self-dependencies
    if row.name in ("xor64_same", "xor32_same", "pxord512_same"):
        reads -= writes
    return reads, writes, jump_target, is_call


def _source_lookup(line_map, pc):
    if not line_map:
        return None
    for row in line_map:
        if row["pc"] == pc:
            return row
    return None


def _frame_field_for(frame, sp_entry, addr):
    """Map an address relative to a function's stack frame back to the declared frame field name."""
    if not frame or sp_entry is None:
        return None
    off = addr - (sp_entry - frame["size"])
    if not 0 <= off < frame["size"]:
        return None
    for fld in frame["fields"]:
        if fld["offset"] <= off < fld["offset"] + fld["bytes"]:
            slot = (off - fld["offset"]) // fld["elem"]
            return f"{fld['name']}[{slot}] (sp+{off})"
    return f"frame (sp+{off})"


def _insn_load_bytes(it):
    """Exact byte width read by a single decoded memory-load instruction, or 0."""
    r = it["row"]
    t = it["text"]
    if r == "ldp" or r == "ldp_sp":
        return 16
    if r.startswith("vmov") and "_rm" in r:
        return 64 if "zmm" in t else (32 if "ymm" in t else 16)
    if r in ("movdqu_rm", "movdqa_rm", "ldr_q", "ldr_q_sp"):
        return 16
    if r in ("mov64_rm", "mov_rm", "ldr_x", "ldr_sp", "ldr", "pop") or (r.startswith("ldr") and ("x" in t or "sp" in t) and "q" not in r and "b" not in r and "h" not in r and "w" not in r):
        return 8
    if r in ("mov32_rm", "ldr_w", "ldr_w_sp"):
        return 4
    if r in ("movzx16_rm", "ldrh"):
        return 2
    if r in ("movzx8_rm", "ldrb"):
        return 1
    if "byte ptr" in t and not t.startswith("mov byte ptr"):
        return 1
    if "dword ptr" in t and not t.startswith("mov dword ptr"):
        return 4
    if "qword ptr" in t and not t.startswith("mov qword ptr"):
        return 8
    if it["class"] in ("load", "vec_load"):
        return 16 if it["class"] == "vec_load" else 8
    return 0


def static_analyze(decoded, target, arch_name=None, line_map=None, frame=None, all_archs=False):
    """Compute static code-size, loop i-cache layout, dependency critical path, and throughput bounds."""
    arch_key = arch_name or DEFAULT_ARCH[target]
    arch = ARCHS[arch_key]
    if arch["target"] != target:
        raise ValueError(f"arch {arch_key} is for {arch['target']}, not {target}")
    _, heads = load_table(target)
    line_bytes = arch["line_bytes"]
    classes = arch["classes"]

    parsed = []
    for pc, end_pc, text in decoded:
        row, raw_bind = table.find(heads, table.parse_row(text))
        bind = _conc_bind(raw_bind)
        reads, writes, jtgt, is_call = row_rw(row, bind, target)
        cls = classify_row(row.name, target)
        cost = classes[cls]
        is_uncond = row.name in ("jmp", "b")
        is_cond = cls == "branch" and not is_uncond
        is_ret = cls == "ret"
        parsed.append({
            "pc": pc, "end": end_pc, "len": end_pc - pc, "text": text,
            "row": row.name, "class": cls, "cost": cost,
            "reads": reads, "writes": writes, "jump": jtgt, "call": is_call,
            "uncond": is_uncond, "cond": is_cond, "ret": is_ret,
        })

    code_bytes = parsed[-1]["end"] if parsed else 0
    icache_lines = math.ceil(code_bytes / line_bytes) if code_bytes else 0

    def analyze_seq(seq):
        ready = collections.defaultdict(float)
        uops = 0.0
        unit_rtp = collections.defaultdict(float)
        live_g, live_v = set(), set()
        peak_g, peak_v = 0, 0
        for it in seq:
            c = it["cost"]
            uops += c["uops"]
            unit_rtp[c["unit"]] += c["rtp"]
            start = max((ready[r] for r in it["reads"]), default=0.0)
            finish = start + c["lat"]
            for w in it["writes"]:
                ready[w] = finish
            for reg in it["reads"] | it["writes"]:
                if reg.startswith("v"): live_v.add(reg)
                elif reg not in ("zf", "cf") and not reg.startswith("frame:") and not reg.startswith("k"):
                    live_g.add(reg)
            peak_g = max(peak_g, len(live_g))
            peak_v = max(peak_v, len(live_v))
        crit = max(ready.values(), default=0.0)
        fe = uops / arch["issue_width"]
        bounds = {"critical_path": crit, "frontend_issue": fe}
        for u, v in unit_rtp.items():
            if u != "fe":
                bounds[f"{u}_throughput"] = v
        limiting, best = max(bounds.items(), key=lambda kv: kv[1])
        return {
            "instructions": len(seq),
            "bytes": sum(it["len"] for it in seq),
            "uops": round(uops, 2),
            "critical_path": round(crit, 2),
            "frontend_issue": round(fe, 2),
            "unit_throughput": {k: round(v, 2) for k, v in sorted(unit_rtp.items()) if k != "fe"},
            "compute_lower_bound": round(best, 2),
            "limiting": limiting,
            "distinct_gpr": peak_g,
            "distinct_vec": peak_v,
        }

    # Detect backward-edge loops
    loops = []
    for idx, it in enumerate(parsed):
        if it["jump"] is not None and it["jump"] <= it["pc"]:
            head_idx = next((k for k, x in enumerate(parsed) if x["pc"] == it["jump"]), None)
            if head_idx is None:
                continue
            body = parsed[head_idx:idx + 1]
            start_pc, end_pc = body[0]["pc"], body[-1]["end"]
            first_line = start_pc // line_bytes
            last_line = (end_pc - 1) // line_bytes
            touched_lines = last_line - first_line + 1
            min_lines = math.ceil((end_pc - start_pc) / line_bytes)
            src_start = _source_lookup(line_map, start_pc)
            src_end = _source_lookup(line_map, body[-1]["pc"])
            sim_rep = uica_sim.simulate_loop(body, arch_key, iterations=12) if arch_key in uica_sim.PIPELINES else None
            lints = uica_sim.static_lint_loop(body, arch_key, line_map=line_map, sim_rep=sim_rep) if arch_key in uica_sim.PIPELINES else []
            crit_chain = uica_sim.critical_path_chain(body, arch_key, line_map=line_map) if arch_key in uica_sim.PIPELINES else None
            arch_table = uica_sim.compare_all_archs(body, target, line_map=line_map) if all_archs else None
            load_widths = [_insn_load_bytes(x) for x in body]
            load_count = sum(1 for w in load_widths if w > 0)
            load_bytes = sum(load_widths)
            loops.append({
                "start_pc": start_pc,
                "end_pc": end_pc,
                "bytes": end_pc - start_pc,
                "icache_lines": touched_lines,
                "min_icache_lines": min_lines,
                "align_saves_line": touched_lines > min_lines,
                "source_lines": [src_start["line"], src_end["line"]] if (src_start and src_end) else None,
                "load_count": load_count,
                "load_bytes": load_bytes,
                "body": analyze_seq(body),
                "pipeline_sim": sim_rep,
                "critical_chain": crit_chain,
                "lints": lints,
                "all_archs": arch_table,
            })

    # Build basic-block DAG (ignoring loop back-edges, which `loops` analyzes separately)
    # so branching functions never chain register dependencies across `ret` boundaries or sum
    # mutually exclusive early-return blocks into one fake straight-line trace.
    paths_summary = None
    if parsed:
        pc_to_idx = {it["pc"]: i for i, it in enumerate(parsed)}
        leaders = {0}
        for i, it in enumerate(parsed):
            if it["jump"] is not None and it["jump"] in pc_to_idx:
                leaders.add(pc_to_idx[it["jump"]])
            if (it["cond"] or it["uncond"] or it["ret"]) and i + 1 < len(parsed):
                leaders.add(i + 1)
        ls = sorted(leaders)
        blocks = []
        idx_to_blk = {}
        for bi, s in enumerate(ls):
            e = ls[bi + 1] if bi + 1 < len(ls) else len(parsed)
            blocks.append(parsed[s:e])
            idx_to_blk[s] = bi
        succs = [[] for _ in blocks]
        for bi, blk in enumerate(blocks):
            last = blk[-1]
            if last["ret"]:
                continue
            if last["uncond"]:
                if last["jump"] in pc_to_idx and last["jump"] > last["pc"]:
                    succs[bi].append(idx_to_blk[pc_to_idx[last["jump"]]])
            elif last["cond"]:
                if bi + 1 < len(blocks):
                    succs[bi].append(bi + 1)
                if last["jump"] in pc_to_idx and last["jump"] > last["pc"]:
                    tbi = idx_to_blk[pc_to_idx[last["jump"]]]
                    if tbi not in succs[bi]:
                        succs[bi].append(tbi)
            elif bi + 1 < len(blocks):
                succs[bi].append(bi + 1)
        dag_paths = []
        def _walk_dag(bi, acc, prob):
            if len(dag_paths) >= 512:
                return
            acc2 = acc + blocks[bi]
            if not succs[bi]:
                dag_paths.append((prob, acc2))
                return
            p2 = prob / len(succs[bi])
            for nb in succs[bi]:
                _walk_dag(nb, acc2, p2)
        _walk_dag(0, [], 1.0)
    else:
        dag_paths = []

    flat = analyze_seq(parsed)
    if len(dag_paths) > 1:
        tot_p = sum(p for p, _ in dag_paths)
        path_reps = [(p / tot_p, analyze_seq(seq)) for p, seq in dag_paths]
        worst = max((r for _, r in path_reps), key=lambda r: (r["compute_lower_bound"], r["critical_path"], r["uops"]))
        exp_lb = sum(w * r["compute_lower_bound"] for w, r in path_reps)
        mean_lb = sum(r["compute_lower_bound"] for _, r in path_reps) / len(path_reps)
        min_lb = min(r["compute_lower_bound"] for _, r in path_reps)
        whole = dict(flat)
        for k in ("uops", "critical_path", "frontend_issue", "unit_throughput", "compute_lower_bound", "limiting"):
            whole[k] = worst[k]
        paths_summary = {
            "count": len(path_reps),
            "min_lower_bound": round(min_lb, 2),
            "expected_lower_bound": round(exp_lb, 2),
            "mean_lower_bound": round(mean_lb, 2),
            "worst_lower_bound": worst["compute_lower_bound"],
        }
    else:
        whole = flat
    return {
        "target": target,
        "arch": arch_key,
        "arch_name": arch["name"],
        "line_bytes": line_bytes,
        "page_bytes": arch["page_bytes"],
        "code_bytes": code_bytes,
        "icache_lines": icache_lines,
        "frame_bytes": frame["size"] if frame else 0,
        "whole": whole,
        "paths": paths_summary,
        "loops": loops,
    }


def trace_memory(programs, entry, target, init_regs=None, init_mem=None, max_steps=200000, line_maps=None):
    """Execute compiled function(s) concretely using core/conc.py and record every memory read/write.
    `programs`: {symbol: [(pc, end_pc, row_text), ...]}
    `init_regs`: {reg_name: int} (defaults: sp/rsp at 0x70000000 aligned to 64 B, arg pointers at distinct
                 4 KiB-separated 64 B-aligned buffers unless specified).
    Returns {"steps", "returned", "fault", "accesses", "final_regs", "sp_entry"}."""
    _, heads = load_table(target)
    sp_name = "sp" if target == "arm64" else "rsp"
    g_names = ([f"x{i}" for i in range(31)] + ["sp"]) if target == "arm64" else (
        "rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15".split()
    )
    sp_entry = (init_regs or {}).get(sp_name, 0x70000000)
    g = {r: 0 for r in g_names}
    g[sp_name] = sp_entry
    if init_regs:
        g.update(init_regs)
    x = {i: (0,) * 16 for i in range(32)}
    k = {i: (0,) * 16 for i in range(8)}
    st = conc.State(g, x, {}, 0, 0, k)
    mem = collections.defaultdict(int)
    if init_mem:
        mem.update(init_mem)
    st.mem = mem

    # Pre-parse all instructions by symbol and pc
    parsed_prog = {}
    for sym, decoded in programs.items():
        by_pc = {}
        for pc, end_pc, text in decoded:
            row, raw_bind = table.find(heads, table.parse_row(text))
            by_pc[pc] = (end_pc, row, _conc_bind(raw_bind), text)
        parsed_prog[sym] = by_pc

    # Sentinel return address for top-level entry
    SENTINEL = 0xDEADBEEF00000000
    if target == "arm64":
        st.g["x30"] = SENTINEL
    else:
        st.g["rsp"] = (st.g["rsp"] - 8) & table.M64
        for i in range(8):
            st.mem[st.g["rsp"] + i] = (SENTINEL >> (8 * i)) & 0xFF

    call_stack = []
    cur_sym, pc = entry, 0
    accesses = []
    dyn_ops = []
    steps = 0
    returned = False
    fault = None

    while steps < max_steps:
        by_pc = parsed_prog.get(cur_sym)
        if by_pc is None or pc not in by_pc:
            fault = f"no instruction at {cur_sym}+{pc:#x}"
            break
        end_pc, row, bind, text = by_pc[pc]
        st.to, st.called, st.returned = None, None, False
        local_trace = []
        try:
            conc.run(row, bind, st, trace=local_trace)
        except conc.Fault as e:
            fault = f"{cur_sym}+{pc:#x}: {e}"
            break
        reads_s, writes_s, _, _ = row_rw(row, bind, target)
        dyn_ops.append((row.name, reads_s, writes_s))
        src_row = _source_lookup((line_maps or {}).get(cur_sym), pc)
        for kind, addr, size in local_trace:
            accesses.append({
                "step": steps,
                "fn": cur_sym,
                "pc": pc,
                "kind": kind,
                "addr": addr,
                "size": size,
                "file": src_row["file"] if src_row else None,
                "line": src_row["line"] if src_row else None,
                "typed": src_row["typed"] if src_row else text,
            })
        steps += 1
        if st.returned:
            if target == "x86_64":
                st.g["rsp"] = (st.g["rsp"] + 8) & table.M64
            if not call_stack:
                returned = True
                break
            cur_sym, pc = call_stack.pop()
            continue
        if st.called is not None:
            callee = st.called
            if target == "arm64":
                # Link register holds return address; emulate call into callee if present
                if callee in parsed_prog:
                    call_stack.append((cur_sym, end_pc))
                    st.g["x30"] = end_pc
                    cur_sym, pc = callee, 0
                    continue
                else:
                    # Unknown external callee: skip over it
                    pc = end_pc
                    continue
            else:
                if callee in parsed_prog:
                    # x86 call pushes 8-byte return address
                    st.g["rsp"] = (st.g["rsp"] - 8) & table.M64
                    accesses.append({
                        "step": steps - 1, "fn": cur_sym, "pc": pc, "kind": "W",
                        "addr": st.g["rsp"], "size": 8,
                        "file": src_row["file"] if src_row else None,
                        "line": src_row["line"] if src_row else None,
                        "typed": src_row["typed"] if src_row else text,
                    })
                    call_stack.append((cur_sym, end_pc))
                    cur_sym, pc = callee, 0
                    continue
                else:
                    pc = end_pc
                    continue
        if st.to is not None:
            pc = st.to
        else:
            pc = end_pc
    else:
        fault = f"hit max_steps ({max_steps})"

    return {
        "steps": steps,
        "returned": returned,
        "fault": fault,
        "accesses": accesses,
        "dyn_ops": dyn_ops,
        "final_regs": dict(st.g),
        "final_mem": dict(st.mem),
        "sp_entry": sp_entry,
    }


def _sim_l1d(accesses, l1d_cfg, warm=False):
    """Exact LRU set-associative L1D cache simulation over an access trace."""
    line = l1d_cfg["line"]
    ways = l1d_cfg["ways"]
    sets = l1d_cfg["bytes"] // (line * ways)
    cache = [collections.OrderedDict() for _ in range(sets)]
    set_lines = collections.defaultdict(set)
    misses = 0

    def touch_line(line_addr, count_miss):
        nonlocal misses
        idx = line_addr % sets
        set_lines[idx].add(line_addr)
        od = cache[idx]
        if line_addr in od:
            od.move_to_end(line_addr)
            return
        if count_miss:
            misses += 1
        if len(od) >= ways:
            od.popitem(last=False)
        od[line_addr] = True

    if warm:
        # Pre-populate each set with the first `ways` distinct lines touched (models hot-cache entry)
        seen = set()
        for a in accesses:
            lo = a["addr"] // line
            hi = (a["addr"] + a["size"] - 1) // line
            for la in range(lo, hi + 1):
                if la not in seen:
                    seen.add(la)
                    idx = la % sets
                    if len(cache[idx]) < ways:
                        cache[idx][la] = True

    for a in accesses:
        lo = a["addr"] // line
        hi = (a["addr"] + a["size"] - 1) // line
        for la in range(lo, hi + 1):
            touch_line(la, True)

    max_set_depth = max((len(v) for v in set_lines.values()), default=0)
    return misses, max_set_depth, sets


def analyze_memory(trace_result, target, arch_name=None, frame=None, store_window=32):
    """Layer 1 exact memory hazards + Layer 2 L1D cache summary from a concrete access trace."""
    arch_key = arch_name or DEFAULT_ARCH[target]
    arch = ARCHS[arch_key]
    line_bytes = arch["line_bytes"]
    page_bytes = arch["page_bytes"]
    hz = arch["hazards"]
    accesses = trace_result["accesses"]
    sp_entry = trace_result["sp_entry"]

    reads = writes = bytes_read = bytes_written = 0
    lines_read, lines_written, pages = set(), set(), set()
    line_splits, page_crossings = [], []
    stlf_clean = 0
    stlf_partial = []
    alias_4k = []
    recent_stores = collections.deque(maxlen=store_window)

    for a in accesses:
        addr, size, kind = a["addr"], a["size"], a["kind"]
        lo_line = addr // line_bytes
        hi_line = (addr + size - 1) // line_bytes
        lo_page = addr // page_bytes
        hi_page = (addr + size - 1) // page_bytes
        for p in range(lo_page, hi_page + 1):
            pages.add(p)
        if kind == "R":
            reads += 1
            bytes_read += size
            for l in range(lo_line, hi_line + 1):
                lines_read.add(l)
        else:
            writes += 1
            bytes_written += size
            for l in range(lo_line, hi_line + 1):
                lines_written.add(l)

        fld = _frame_field_for(frame, sp_entry, addr)
        if hi_line > lo_line:
            line_splits.append({
                "fn": a["fn"], "pc": a["pc"], "line": a["line"], "typed": a["typed"],
                "kind": kind, "addr": addr, "size": size, "field": fld,
            })
        if hi_page > lo_page:
            page_crossings.append({
                "fn": a["fn"], "pc": a["pc"], "line": a["line"], "typed": a["typed"],
                "kind": kind, "addr": addr, "size": size, "field": fld,
            })

        if kind == "R":
            # Check against recent stores (newest first) for STLF & 4K aliasing
            matched_overlap = False
            matched_alias = False
            for st in reversed(recent_stores):
                s_lo, s_hi = st["addr"], st["addr"] + st["size"]
                l_lo, l_hi = addr, addr + size
                if max(s_lo, l_lo) < min(s_hi, l_hi):
                    if not matched_overlap:
                        matched_overlap = True
                        if s_lo <= l_lo and l_hi <= s_hi and s_lo == l_lo:
                            stlf_clean += 1
                        else:
                            stlf_partial.append({
                                "load_fn": a["fn"], "load_pc": a["pc"], "load_line": a["line"], "load_typed": a["typed"],
                                "store_fn": st["fn"], "store_pc": st["pc"], "store_line": st["line"], "store_typed": st["typed"],
                                "load_addr": addr, "load_size": size, "store_addr": st["addr"], "store_size": st["size"],
                                "field": fld,
                            })
                elif hz["alias_4k"] > 0 and not matched_alias:
                    # 4K aliasing: different 4 KiB pages (non-overlapping), overlapping low 12 bits
                    sl12, sh12 = st["addr"] & 0xFFF, (st["addr"] & 0xFFF) + st["size"]
                    ll12, lh12 = addr & 0xFFF, (addr & 0xFFF) + size
                    if max(sl12, ll12) < min(sh12, lh12):
                        matched_alias = True
                        alias_4k.append({
                            "load_fn": a["fn"], "load_pc": a["pc"], "load_line": a["line"], "load_typed": a["typed"],
                            "store_fn": st["fn"], "store_pc": st["pc"], "store_line": st["line"], "store_typed": st["typed"],
                            "low12": ll12, "load_addr": addr, "store_addr": st["addr"],
                        })
        else:
            recent_stores.append(a)

    warm_misses, max_set_depth, num_sets = _sim_l1d(accesses, arch["l1d"], warm=True)
    cold_misses, _, _ = _sim_l1d(accesses, arch["l1d"], warm=False)
    hazard_cycles = (
        len(line_splits) * hz["line_split"]
        + len(page_crossings) * hz["page_cross"]
        + len(stlf_partial) * hz["stlf_partial"]
        + len(alias_4k) * hz["alias_4k"]
    )
    # Dynamic compute lower bound across the actual executed trace (including loops, callees,
    # and concrete memory store-to-load dependency chains on matching byte addresses).
    acc_by_step = collections.defaultdict(list)
    for a in accesses:
        acc_by_step[a["step"]].append(a)
    classes = arch["classes"]
    d_ready = collections.defaultdict(float)
    mem_ready = {}
    d_uops = 0.0
    d_unit = collections.defaultdict(float)
    for step_idx, (rname, rset, wset) in enumerate(trace_result.get("dyn_ops", ())):
        c = classes[classify_row(rname, target)]
        d_uops += c["uops"]
        d_unit[c["unit"]] += c["rtp"]
        start = max((d_ready[r] for r in rset if not r.startswith("frame:")), default=0.0)
        step_accs = acc_by_step.get(step_idx)
        if step_accs:
            for a in step_accs:
                if a["kind"] == "R":
                    for b in range(a["addr"], a["addr"] + a["size"]):
                        t_w = mem_ready.get(b)
                        if t_w is not None and t_w > start:
                            start = t_w
        fin = start + c["lat"]
        for w in wset:
            if not w.startswith("frame:"):
                d_ready[w] = fin
        if step_accs:
            for a in step_accs:
                if a["kind"] == "W":
                    for b in range(a["addr"], a["addr"] + a["size"]):
                        mem_ready[b] = fin
    d_crit = max(d_ready.values(), default=0.0)
    d_fe = d_uops / arch["issue_width"]
    d_bounds = {"critical_path": d_crit, "frontend_issue": d_fe}
    for u, v in d_unit.items():
        if u != "fe":
            d_bounds[f"{u}_throughput"] = v
    d_limiting, d_compute = max(d_bounds.items(), key=lambda kv: kv[1])
    warm_miss_cyc = warm_misses * hz["l1_miss"]
    cold_miss_cyc = cold_misses * hz["l1_miss"]
    return {
        "steps": trace_result["steps"],
        "returned": trace_result["returned"],
        "fault": trace_result["fault"],
        "dyn_compute_cycles": round(d_compute, 2),
        "dyn_limiting": d_limiting,
        "reads": reads,
        "writes": writes,
        "bytes_read": bytes_read,
        "bytes_written": bytes_written,
        "unique_lines_read": len(lines_read),
        "unique_lines_written": len(lines_written),
        "unique_lines_total": len(lines_read | lines_written),
        "unique_pages": len(pages),
        "line_splits": len(line_splits),
        "page_crossings": len(page_crossings),
        "stlf_clean": stlf_clean,
        "stlf_partial": len(stlf_partial),
        "alias_4k": len(alias_4k),
        "l1d_sets": num_sets,
        "l1d_ways": arch["l1d"]["ways"],
        "l1d_max_set_depth": max_set_depth,
        "l1d_set_conflict": max_set_depth > arch["l1d"]["ways"],
        "l1d_warm_misses": warm_misses,
        "l1d_cold_misses": cold_misses,
        "hazard_cycles": round(hazard_cycles, 2),
        "warm_miss_cycles": round(warm_miss_cyc, 2),
        "cold_miss_cycles": round(cold_miss_cyc, 2),
        "est_warm_cycles": round(d_compute + hazard_cycles + warm_miss_cyc, 2),
        "est_cold_cycles": round(d_compute + hazard_cycles + cold_miss_cyc, 2),
        "details": {
            "line_splits": line_splits[:20],
            "page_crossings": page_crossings[:20],
            "stlf_partial": stlf_partial[:20],
            "alias_4k": alias_4k[:20],
        },
    }


def check_budgets(static_rep, mem_rep, budgets):
    """Check explicit coder budgets; returns list of human-readable violation strings."""
    errs = []
    if not budgets:
        return errs
    checks = [
        ("max_bytes", static_rep["code_bytes"], "code bytes"),
        ("max_icache_lines", static_rep["icache_lines"], "instruction-cache lines"),
        ("max_frame_bytes", static_rep["frame_bytes"], "frame bytes"),
    ]
    if static_rep.get("loops") and budgets.get("max_loop_cycles") is not None:
        max_sim = max(
            (lp["pipeline_sim"]["cycles_per_iter"] for lp in static_rep["loops"] if lp.get("pipeline_sim")),
            default=0.0,
        )
        checks.append(("max_loop_cycles", max_sim, "static loop pipeline cycles/iter"))
    if mem_rep is not None:
        checks += [
            ("max_line_splits", mem_rep["line_splits"], "cache-line splits"),
            ("max_page_crossings", mem_rep["page_crossings"], "page crossings"),
            ("max_stlf_partial", mem_rep["stlf_partial"], "partial store-to-load stalls"),
            ("max_alias_4k", mem_rep["alias_4k"], "4K aliasing hazards"),
        ]
    for key, actual, label in checks:
        limit = budgets.get(key)
        if limit is not None and actual > limit:
            errs.append(f"budget exceeded: {label} is {actual}, limit {key}={limit}")
    return errs


def format_report(symbol, static_rep, mem_rep=None):
    """Format a plain-English performance and memory advice report."""
    lines = []
    w = static_rep["whole"]
    lines.append(f"advice for {symbol} ({static_rep['arch_name']}, target {static_rep['target']}):")
    lines.append(
        f"  code:   {w['instructions']} instructions, {static_rep['code_bytes']} bytes, "
        f"{static_rep['icache_lines']} i-cache line(s) ({static_rep['line_bytes']} B/line)"
        + (f", frame {static_rep['frame_bytes']} B" if static_rep["frame_bytes"] else "")
    )
    lines.append(
        f"  static: compute lower bound >= {w['compute_lower_bound']:.1f} cyc "
        f"(limiting: {w['limiting']}; crit={w['critical_path']:.1f}, fe={w['frontend_issue']:.1f}, "
        f"uops={w['uops']:.1f}, gpr={w['distinct_gpr']}, vec={w['distinct_vec']})"
    )
    ps = static_rep.get("paths")
    if ps and ps["count"] > 1:
        lines.append(
            f"  paths:  {ps['count']} acyclic entry-to-exit path(s) — "
            f"min {ps['min_lower_bound']:.1f}, expected {ps['expected_lower_bound']:.2f}, "
            f"mean {ps['mean_lower_bound']:.2f}, worst {ps['worst_lower_bound']:.1f} cyc"
        )
    for idx, lp in enumerate(static_rep["loops"]):
        lb = lp["body"]
        src_note = f" lines {lp['source_lines'][0]}..{lp['source_lines'][1]}" if lp["source_lines"] else ""
        al_note = f" [aligning loop top saves {lp['icache_lines'] - lp['min_icache_lines']} i-cache line(s)]" if lp["align_saves_line"] else ""
        sim_rep = lp.get("pipeline_sim")
        lb_bytes = lp.get("load_bytes") or 0
        lb_cnt = lp.get("load_count") or 0
        tp_note = f", {sim_rep['cycles_per_iter'] / lb_bytes:.2f} cyc/B across {lb_cnt} load(s)/{lb_bytes} B" if (sim_rep is not None and lb_bytes > 0) else ""
        sim_note = (
            f" | pipeline sim ~{sim_rep['cycles_per_iter']:.2f} cyc/iter"
            f" ({sim_rep['bottleneck']}, {sim_rep['fused_pairs']} fused{tp_note})"
            if sim_rep is not None else ""
        )
        lines.append(
            f"  loop {idx}: +0x{lp['start_pc']:x}..+0x{lp['end_pc']:x}{src_note} — "
            f"{lb['instructions']} ins, {lp['bytes']} B, {lp['icache_lines']} i-cache line(s), "
            f">= {lb['compute_lower_bound']:.1f} cyc/iter ({lb['limiting']}){sim_note}{al_note}"
        )
        cc = lp.get("critical_chain")
        if cc and cc["steps"] and sim_rep and sim_rep["bottleneck"] == "dependency":
            steps = cc["steps"]
            def _fmt_step(st):
                loc = f"L{st['line']}" if st["line"] else f"+0x{st['pc']:x}"
                return f"{loc}({st['row']})"
            if len(steps) > 8:
                chain_s = " -> ".join(_fmt_step(s) for s in steps[:5]) + f" -> ... ({len(steps)-7} more) -> " + " -> ".join(_fmt_step(s) for s in steps[-2:])
            else:
                chain_s = " -> ".join(_fmt_step(s) for s in steps)
            lines.append(f"    crit path ({cc['total_cycles']:.1f} cyc, {len(steps)} ops): {chain_s}")
        for lt in lp.get("lints") or []:
            lines.append(f"    hint [{lt['kind']}]: {lt['message']}")
        aa = lp.get("all_archs")
        if aa:
            lines.append("    cross-CPU static estimate (no execution):")
            for row in aa:
                cpb = f", {row['cycles_per_iter'] / lb_bytes:4.2f} cyc/B" if lb_bytes > 0 else ""
                lines.append(
                    f"      {row['arch']:8s}: ~{row['cycles_per_iter']:5.2f} cyc/iter{cpb} "
                    f"[{row['bottleneck']:12s}] ({row['fused_pairs']} fused, {row['eliminated_moves']} elim"
                    + (f", {row['lint_count']} hint(s)" if row["lint_count"] else "")
                    + ")"
                )
    if mem_rep is not None:
        lines.append(
            f"  memory ({mem_rep['steps']} dynamic steps, returned={mem_rep['returned']}): "
            f"{mem_rep['reads']} loads ({mem_rep['bytes_read']} B), {mem_rep['writes']} stores ({mem_rep['bytes_written']} B)"
        )
        lines.append(
            f"    working set: {mem_rep['unique_lines_total']} cache line(s) "
            f"({mem_rep['unique_lines_read']} R / {mem_rep['unique_lines_written']} W), "
            f"{mem_rep['unique_pages']} page(s); L1D max set depth {mem_rep['l1d_max_set_depth']}/{mem_rep['l1d_ways']} ways"
            + (" [SET CONFLICT]" if mem_rep["l1d_set_conflict"] else "")
        )
        lines.append(
            f"    hazards: {mem_rep['line_splits']} line split(s), {mem_rep['page_crossings']} page crossing(s), "
            f"{mem_rep['stlf_partial']} partial STLF stall(s) ({mem_rep['stlf_clean']} clean forward(s)), "
            f"{mem_rep['alias_4k']} 4K alias(es)"
        )
        lines.append(
            f"    cache & total (estimate): dyn compute >= {mem_rep['dyn_compute_cycles']:.1f} cyc ({mem_rep['dyn_limiting']}), "
            f"hazards ~{mem_rep['hazard_cycles']:.1f} cyc, "
            f"warm-L1 total ~{mem_rep['est_warm_cycles']:.1f} cyc (misses={mem_rep['l1d_warm_misses']}), "
            f"cold-L1 total ~{mem_rep['est_cold_cycles']:.1f} cyc (misses={mem_rep['l1d_cold_misses']})"
        )
        # Show top concrete hazard sites pinned to source lines
        for label, key in [("line split", "line_splits"), ("partial STLF", "stlf_partial"), ("4K alias", "alias_4k")]:
            items = mem_rep["details"][key]
            if not items:
                continue
            by_site = collections.Counter()
            for it in items:
                if key == "line_splits":
                    loc = f"{it['fn']}:{it['line']}" if it["line"] else f"{it['fn']}+0x{it['pc']:x}"
                    by_site[(loc, it["typed"])] += 1
                else:
                    loc = f"{it['load_fn']}:{it['load_line']}" if it["load_line"] else f"{it['load_fn']}+0x{it['load_pc']:x}"
                    sloc = f"{it['store_fn']}:{it['store_line']}" if it["store_line"] else f"{it['store_fn']}+0x{it['store_pc']:x}"
                    by_site[(f"store {sloc} -> load {loc}", it["load_typed"])] += 1
            for (loc, typed), cnt in by_site.most_common(4):
                lines.append(f"      - {label} (x{cnt}): {loc}  `{typed}`")
    return "\n".join(lines)


def compare_reports(label_a, static_a, mem_a, label_b, static_b, mem_b):
    """Side-by-side comparison of two variants (A vs B)."""
    rows = [
        ("instructions", static_a["whole"]["instructions"], static_b["whole"]["instructions"]),
        ("code bytes", static_a["code_bytes"], static_b["code_bytes"]),
        ("i-cache lines", static_a["icache_lines"], static_b["icache_lines"]),
        ("compute lower bound (cyc)", static_a["whole"]["compute_lower_bound"], static_b["whole"]["compute_lower_bound"]),
        ("critical path (cyc)", static_a["whole"]["critical_path"], static_b["whole"]["critical_path"]),
    ]
    if mem_a is not None and mem_b is not None:
        rows += [
            ("dynamic steps", mem_a["steps"], mem_b["steps"]),
            ("dyn compute bound (cyc)", mem_a["dyn_compute_cycles"], mem_b["dyn_compute_cycles"]),
            ("cache-line splits", mem_a["line_splits"], mem_b["line_splits"]),
            ("partial STLF stalls", mem_a["stlf_partial"], mem_b["stlf_partial"]),
            ("4K aliases", mem_a["alias_4k"], mem_b["alias_4k"]),
            ("unique cache lines", mem_a["unique_lines_total"], mem_b["unique_lines_total"]),
            ("warm-L1 misses", mem_a["l1d_warm_misses"], mem_b["l1d_warm_misses"]),
            ("cold-L1 misses", mem_a["l1d_cold_misses"], mem_b["l1d_cold_misses"]),
            ("hazard penalty (cyc)", mem_a["hazard_cycles"], mem_b["hazard_cycles"]),
            ("est warm-L1 total (cyc)", mem_a["est_warm_cycles"], mem_b["est_warm_cycles"]),
            ("est cold-L1 total (cyc)", mem_a["est_cold_cycles"], mem_b["est_cold_cycles"]),
        ]
    out = [f"compare: A={label_a} vs B={label_b} ({static_a['arch_name']})"]
    out.append(f"  {'metric':<28s} {'A':>10s} {'B':>10s} {'B - A':>10s}")
    for name, va, vb in rows:
        diff = vb - va
        if isinstance(va, float) or isinstance(vb, float):
            out.append(f"  {name:<28s} {va:10.1f} {vb:10.1f} {diff:+10.1f}")
        else:
            out.append(f"  {name:<28s} {va:10d} {vb:10d} {diff:+10d}")
    return "\n".join(out)
