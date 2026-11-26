#!/usr/bin/env python3
"""ode_tool: integrated compiler, prover, verifier runner, and performance/memory advisor for Ode.
Works on both x86-64 and AArch64. Relied on for nothing by the verifier: the final verdict of `check`
is always the Lean verifier binary `odeverify` run on the generated object, statement, and proof.

Commands:
    python3 lang/ode_tool.py check   SOURCE.ode SPEC.spec [--fn NAME ...] [--arch ARCH] [--out DIR]
                                     [--trace] [--align N] [--arg REG=VAL ...] [--max-* N]
    python3 lang/ode_tool.py advise  SOURCE.ode [--fn NAME] [--spec SPEC.spec] [--arch ARCH]
                                     [--trace] [--align N] [--arg REG=VAL ...] [--max-* N]
    python3 lang/ode_tool.py compare A.ode B.ode [--fn NAME] [--spec SPEC.spec] [--arch ARCH]
                                     [--trace] [--align N] [--arg REG=VAL ...]
    python3 lang/ode_tool.py canon   SPEC.ocl [--contract NAME] [--glossary-out FILE.json] [--json]
    python3 lang/ode_tool.py pack    SOURCE.ode SPEC.ocl --out BIN.o --proof BIN.proof
                                     [--fn NAME] [--glossary-out FILE.json] [--json]
    python3 lang/ode_tool.py audit   BINARY --proof FILE.proof [--expect-contract B32]
                                     [--contract FILE.ocl] [--glossary FILE.json] [--show-contract] [--json]
    python3 lang/ode_tool.py spec-test FILE.ocl --call FN [--arg JSON ...] [--glossary FILE.json]
"""
import argparse, json, os, re, shutil, subprocess, sys, tempfile, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for d in (HERE, os.path.join(ROOT, "advice"), os.path.join(ROOT, "proof-core"),
          os.path.join(ROOT, "kcheck"), os.path.join(ROOT, "arm64"), os.path.join(ROOT, "core")):
    if d not in sys.path:
        sys.path.insert(0, d)
import estimate, odec, refute_conc

ARG_REGS_X86 = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"]
ARG_REGS_ARM = ["x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7"]
# Exact variable numbering matching proof-core/Machine.lean (note AArch64: sp is 4, x4 is 31).
REG_NAMES_X86 = ["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi",
                 "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"]
REG_NAMES_ARM = ["x0", "x1", "x2", "x3", "sp", "x5", "x6", "x7", "x8", "x9", "x10", "x11", "x12", "x13", "x14", "x15",
                 "x16", "x17", "x18", "x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26", "x27", "x28", "x29", "x30", "x4"]
CALLEE_SAVED_X86 = {"rbx", "rbp", "r12", "r13", "r14", "r15"}
CALLEE_SAVED_ARM = {f"x{i}" for i in range(19, 31)}
M64 = 1 << 64


def compile_source(src_path, fn_names=None, target=None):
    """Compile selected (or all) functions of an Ode source file via odec.compile_info."""
    text = odec.read_source(src_path)
    arch, _, _, fns = odec.source(text, src_path, target=target)
    want = fn_names if fn_names else [name for name, _, _, _ in fns]
    if not want:
        raise ValueError(f"{src_path}: source contains no `fn` definitions")
    compiled = []
    for name in want:
        compiled.append(odec.compile_info(src_path, name, target=target))
    return arch, compiled


def load_spec_text(spec_path, includes=None):
    """Read optional included .spec files followed by the main .spec file."""
    parts = []
    for p in (includes or ()):
        with open(p) as f:
            parts.append(f.read())
    with open(spec_path) as f:
        parts.append(f.read())
    return "\n".join(parts)


def _fmt_const(n):
    """Format large 2^64-adjacent integers cleanly for human/AI readers."""
    if n == M64: return "2^64"
    if n == M64 - 1: return "2^64 - 1"
    if n == -M64: return "-2^64"
    if n == -(M64 - 1): return "-(2^64 - 1)"
    if abs(n - M64) <= 65536: return f"2^64 {'+' if n > M64 else '-'} {abs(n - M64)}"
    if abs(n + M64) <= 65536: return f"-2^64 {'+' if n > -M64 else '-'} {abs(n + M64)}"
    return str(n)


def _var_labels(target, info=None, contract=None):
    """Map variable index i -> readable label like `rdx(len)` or `v17`."""
    base = REG_NAMES_ARM if target == "arm64" else REG_NAMES_X86
    arg_regs = ARG_REGS_ARM if target == "arm64" else ARG_REGS_X86
    param_by_reg = {}
    if contract is not None:
        calling = contract.get("calling") if isinstance(contract, dict) else getattr(contract, "calling", None)
        if calling and calling.get("in"):
            for pname, rname in calling["in"].items():
                param_by_reg[rname] = pname
        else:
            params = contract["args"] if isinstance(contract, dict) else getattr(contract, "args", [])
            for idx, (pname, _) in enumerate(params):
                if idx < len(arg_regs):
                    param_by_reg[arg_regs[idx]] = pname
    alias_by_reg = {}
    if info and info.get("regs"):
        for alias, reg in info["regs"].items():
            alias_by_reg.setdefault(reg, alias)
    labels = []
    for r in base:
        tag = param_by_reg.get(r) or alias_by_reg.get(r)
        labels.append(f"{r}({tag})" if tag and tag != r else r)
    labels.append("rodata")
    return labels


def _infer_anon_var_bounds(facts, base_len):
    """Infer readable bounds tags like `v69 (byte 0..255)` for anonymous symbolic variables from `facts`."""
    lo, hi = {}, {}
    for row in facts:
        if not row:
            continue
        c = row[0]
        nz = [(i, a) for i, a in enumerate(row[1:]) if a != 0]
        if len(nz) != 1:
            continue
        idx, a = nz[0]
        if idx < base_len:
            continue
        if a == 1:
            lo[idx] = max(lo.get(idx, -10**30), -c)
        elif a == -1:
            hi[idx] = min(hi.get(idx, 10**30), c)
    tags = {}
    for idx in set(lo) & set(hi):
        l, h = lo[idx], hi[idx]
        if l == 0 and h == 1:
            tags[idx] = f"v{idx} (bit 0..1)"
        elif l == 0 and h == 255:
            tags[idx] = f"v{idx} (byte 0..255)"
        elif l == 0 and h == 65535:
            tags[idx] = f"v{idx} (u16 0..65535)"
        elif l == 0 and h == (1 << 32) - 1:
            tags[idx] = f"v{idx} (u32 0..2^32-1)"
        elif 0 <= l <= h <= 1000000:
            tags[idx] = f"v{idx} ({l}..{h})"
    return tags


def _matching_spec_comparisons(spec_text, raw_goals):
    """Find up to 3 `def` comparisons in `spec_text` testing the same integer constant as a `need compare` goal."""
    if not spec_text or not raw_goals:
        return []
    consts = set()
    for row in raw_goals:
        if not row:
            continue
        nz = [a for a in row[1:] if a != 0]
        if len(nz) == 1 and abs(nz[0]) == 1:
            consts.add(abs(row[0]))
    if not consts:
        return []
    matches = []
    cur_def = None
    for raw_line in spec_text.splitlines():
        s = raw_line.split("//")[0].strip()
        if not s:
            continue
        dm = re.match(r"def\s+(\w+)\s*\(", s)
        if dm:
            cur_def = dm.group(1)
        if cur_def is None:
            continue
        for k in sorted(consts):
            if re.search(rf"(?:==|!=|<=|>=|<|>)\s*{k}\b|\b{k}\s*(?:==|!=|<=|>=|<|>)", s):
                entry = f"def {cur_def}: {s}"
                if entry not in matches:
                    matches.append(entry)
                if len(matches) >= 3:
                    return matches
                break
    return matches


def format_inequality(nums, labels):
    """Format a verifier row `[c, a0, a1, ...]` representing `c + sum a_i*v_i >= 0` cleanly."""
    if not nums:
        return "0 >= 0"
    c = nums[0]
    pos, neg = [], []
    for i, a in enumerate(nums[1:]):
        if a == 0:
            continue
        name = labels[i] if i < len(labels) else f"v{i}"
        term = name if abs(a) == 1 else f"{abs(a)}*{name}"
        (pos if a > 0 else neg).append(term)
    if not pos and not neg:
        return f"{_fmt_const(c)} >= 0"
    if pos and neg and c == 0:
        return f"{' + '.join(pos)} >= {' + '.join(neg)}"
    if neg and not pos:
        return f"{' + '.join(neg)} <= {_fmt_const(c)}"
    if pos and not neg:
        return f"{' + '.join(pos)} >= {_fmt_const(-c)}"
    lhs = " + ".join(pos)
    rhs_terms = list(neg)
    if c > 0:
        lhs = f"{lhs} + {_fmt_const(c)}"
    elif c < 0:
        rhs_terms.append(_fmt_const(-c))
    return f"{lhs} >= {' + '.join(rhs_terms)}"


def parse_arithmetic_need(reason, target, info=None, contract=None):
    """Parse `need entail` / `need know` rows into structured readable goals and relevant facts."""
    raw_lines = reason.strip().splitlines()
    if not raw_lines or not raw_lines[0].startswith("need "):
        return None
    kind = raw_lines[0][5:].strip()
    facts, goals = [], []
    for l in raw_lines[1:]:
        parts = l.split()
        if len(parts) >= 2 and parts[0] in ("f", "g"):
            try:
                nums = [int(x) for x in parts[1:]]
            except ValueError:
                continue
            (facts if parts[0] == "f" else goals).append(nums)
    if not facts and not goals:
        return None
    labels = _var_labels(target, info, contract)
    anon_tags = _infer_anon_var_bounds(facts, len(labels))
    max_idx = max([len(labels) - 1] + list(anon_tags.keys()))
    goal_labels = [
        labels[i] if i < len(labels) else anon_tags.get(i, f"v{i}")
        for i in range(max_idx + 1)
    ]
    goal_vars = set()
    for g in goals:
        for i, a in enumerate(g[1:]):
            if a != 0:
                goal_vars.add(i)
    fmt_goals = [format_inequality(g, goal_labels) for g in goals[:4]]
    scored = []
    for f in facts:
        fvars = {i for i, a in enumerate(f[1:]) if a != 0}
        overlap = len(fvars & goal_vars) if goal_vars else 1
        if overlap > 0:
            scored.append((-overlap, len(fvars), format_inequality(f, labels)))
    scored.sort()
    seen, rel_facts = set(), []
    for _, _, txt in scored:
        if txt not in seen:
            seen.add(txt)
            rel_facts.append(txt)
        if len(rel_facts) >= 6:
            break
    return {"kind": kind, "goals": fmt_goals, "raw_goals": goals[:4], "relevant_facts": rel_facts, "total_facts": len(facts)}


def _diagnostic_hint(reason, target, info=None, contract=None, row=None):
    """Produce one concrete, actionable hint tailored to the refusal reason."""
    if "with no place" in reason:
        line_note = f" (right above line {row['line']})" if row else ""
        return f"hint: add a `place {{ ... }}` loop invariant at the loop head{line_note} stating bounds on loop counters and pointers"
    if "values kept out of the trace" in reason:
        td = []
        if contract is not None:
            td = contract.get("trace", []) if isinstance(contract, dict) else getattr(contract, "trace", [])
        listed = ", ".join(str(x) for x in td) if td else "(none)"
        return f"hint: contract `trace depends on` lists {listed}; avoid branching/indexing on other inputs or use branchless instructions"
    if "register a callee keeps" in reason:
        saved = CALLEE_SAVED_ARM if target == "arm64" else CALLEE_SAVED_X86
        touched = []
        if info and info.get("line_map"):
            asm_all = "\n".join(r["asm"] for r in info["line_map"])
            touched = sorted(r for r in saved if re.search(rf"\b{r}\b", asm_all))
        if touched:
            return f"hint: check save/restore symmetry for callee-saved register(s) referenced in function: {', '.join(touched)}"
        return "hint: save every modified callee-saved register on entry and restore it before `ret`"
    if "more stack than this function's contract allows" in reason:
        fsz = info["frame"]["size"] if info and info.get("frame") else 0
        slot_note = "8 B return address + " if target != "arm64" else ""
        return (
            f"hint: local frame is {fsz} B; a `call`/`bl` also needs the call slot ({slot_note}callee stack) — "
            f"raise `stack N` in the contract or tail-call a `stack 0` helper with `jmp`/`b`"
        )
    if "need entail" in reason:
        if row and re.match(r"^\s*sub\b", row.get("asm", "")):
            return (
                "hint: unsigned `sub` requires operand >= subtrahend (no underflow); guard before subtracting or, "
                "in branchless `cmov*`/`csel` code, shift intermediate values up by a positive constant +K and subtract K at the end"
            )
        return "hint: check off-by-one bounds, guard before memory access/shift, or strengthen the loop `place { ... }` invariant"
    if "need below" in reason:
        return (
            "hint: if a specification `if` condition tests this inequality, test it with a branch or conditional select "
            "(`cmov*`/`csel`), using a join-point `place { ... }` (without `decreases`) to merge sequential paths, "
            "or strengthen the loop `place { ... }` invariant"
        )
    if "need know" in reason:
        return "hint: split on the missing comparison or add an explicit branch/invariant establishing the condition"
    if "need compare" in reason:
        return "hint: the specification tests these two for equality (`==`/`!=`) at this point; make the code compare them and branch first (so each path knows the answer), merge branches with a `place { ... }` join point, or state the relation in `place { ... }`"
    if "reached 14 specification definition opens" in reason or (
        "need spec" in reason and re.search(r"(?m)^o\s+(1[2-9]|[2-9]\d)\b", reason)
    ):
        return (
            "hint: reached the verifier's unfolding depth limit for a single step — "
            "for >12x unrolled loops, insert a zero-instruction mid-loop join point `place { ... }` "
            "(without `decreases`) every 8 steps to split the unfolding into 8 + 8"
        )
    if "need spec" in reason:
        return "hint: the prover could not match symbolic register/memory values to the specification formula here; check the loop `place { ... }` invariant, guard bounds, or split multi-way dispatch into small `calling` helper functions"
    if "is not one expression" in reason and "wrote" in reason:
        return "hint: `wrote` syntax is `wrote out[.. i] = expr` (forward) or `wrote out[i ..] = expr` (countdown), naming the full output value"
    return None


def _compile_error_hint(err):
    """Produce a concise, table-driven fix hint for Ode compile / place-syntax errors (zero drift)."""
    if "no `fn` definitions" in err:
        return "hint: return a complete `.ode` file containing `fn NAME(...) ... { for x86_64 { ... } }` or `{ for arm64 { ... } }`"
    if "not a number: &" in err:
        return "hint: use `REG := &field` (or `frame.<field>` for the byte offset) to reference a stack-frame field"
    if "a contract says `stack` once" in err:
        return "hint: declare `stack N` in only one place — either on the `fn` contract header or on the `for <target>` header, not both"
    if "is not one expression" in err:
        return "hint: in `place { ... }`, write `wrote out[.. i] = spec_expr` or `wrote out[i ..] = spec_expr` (e.g. `wrote out[.. i] = pad16(src)`)"
    # Live table lookup directly from x86.tab / arm64.tab whenever an instruction fails to match.
    if "no way in x86.tab writes" in err:
        mi = re.search(r"'I':\s*(-?\d+)", err)
        if mi:
            ival = int(mi.group(1))
            if ival < -(1 << 31) or ival >= (1 << 31):
                return (f"hint: x86-64 immediate {ival} exceeds signed 32-bit range (-2^31..2^31-1); "
                        f"load large 64-bit constants into a register with `mov r, K` (or shift + add) before comparing/adding")
    target = "arm64" if "arm64.tab" in err else ("x86_64" if "x86.tab" in err else None)
    if target is not None:
        m = re.search(r"`([A-Za-z][A-Za-z0-9.]*)\b[^`]*`:", err)
        if m:
            mn = m.group(1)
            asm_mod = odec._asm_mod(target)
            forms = asm_mod.forms_for(mn)
            tab_name = "arm64.tab" if target == "arm64" else "x86.tab"
            if forms:
                return f"hint: supported `{mn}` forms in {tab_name}: " + "; ".join(forms[:8])
            avail = sorted({r.asm.split()[0] for r in (asm_mod.ROWS if target == "arm64" else [v[0] for v in asm_mod.ROWS.values()]) if r.asm != "-"})
            return f"hint: `{mn}` is not in {tab_name} (available mnemonics: {', '.join(avail[:24])})"
    return None


def format_source_diagnostic(compiled_by_sym, pc, fn_sym, reason, target="x86-64", contract=None, spec_text=None):
    """Translate a verifier refusal `(fn_sym, pc, reason)` into source file, line, reg names, frame fields,
    decoded arithmetic inequalities, and an actionable hint."""
    out = []
    info = compiled_by_sym.get(fn_sym) if fn_sym else None
    row = None
    if info is not None and pc is not None:
        row = next((r for r in info["line_map"] if r["pc"] == pc), None)
        if row is None:
            before = [r for r in info["line_map"] if r["pc"] <= pc]
            row = before[-1] if before else None
        if row is not None:
            rel = os.path.relpath(row["file"], ROOT) if row["file"].startswith(ROOT) else row["file"]
            out.append(f"refused in {fn_sym} ({rel}:{row['line']}, pc +0x{pc:x}):")
            out.append(f"  {row['line']:4d} | {row['typed']}")
            if row["asm"] != row["typed"]:
                out.append(f"       | expanded: {row['asm']}")
            if info["regs"]:
                inv = ", ".join(f"{reg}={name}" for name, reg in info["regs"].items())
                out.append(f"  regs:  {inv}")
            if info["frame"]:
                flds = ", ".join(f"{f['name']}@sp+{f['offset']}({f['bytes']}B)" for f in info["frame"]["fields"])
                out.append(f"  frame: {info['frame']['size']} B ({flds})")
        else:
            out.append(f"refused in {fn_sym} (pc +0x{pc:x}):")
    elif fn_sym:
        out.append(f"refused in {fn_sym}:")
    else:
        out.append("refused:")
    arith = parse_arithmetic_need(reason, target, info, contract)
    raw_lines = reason.strip().splitlines()
    if arith is not None:
        if arith["kind"] == "compare":
            # The row is a difference A - B that the specification tests for equality: what is missing is
            # which of the three cases holds, not the inequality the row happens to print as.
            out.append(f"  need compare (the facts in context, {arith['total_facts']} inequalities, do not settle a comparison the specification makes)")
            for g in arith["goals"]:
                m = re.match(r"^(.*?) (>=|<=) (.*)$", g)
                a, b = (m.group(1), m.group(3)) if m else (g, "0")
                out.append(f"  cannot decide: is {a} equal to {b}, below it, or above it? (the proof needs one of the three to follow from the facts)")
            spec_hits = _matching_spec_comparisons(spec_text, arith.get("raw_goals"))
            if spec_hits:
                out.append("  matching spec comparison(s):")
                for sh in spec_hits:
                    out.append(f"    {sh}")
        else:
            out.append(f"  need {arith['kind']} (arithmetic fact not shown from {arith['total_facts']} inequalities in context)")
            for g in arith["goals"]:
                out.append(f"  cannot show: {g}")
            if arith["kind"] == "below":
                spec_hits = _matching_spec_comparisons(spec_text, arith.get("raw_goals"))
                if spec_hits:
                    out.append("  matching spec condition(s):")
                    for sh in spec_hits:
                        out.append(f"    {sh}")
        if arith["relevant_facts"]:
            out.append("  relevant facts:")
            for f in arith["relevant_facts"]:
                out.append(f"    {f}")
    else:
        for line in raw_lines:
            out.append(f"  {line}")
    hint = _diagnostic_hint(reason, target, info, contract, row)
    if hint:
        out.append(f"  {hint}")
    return "\n".join(out), arith


def default_args_from_spec(spec_text, symbol, target, align=0):
    """Derive clean non-overlapping buffer addresses and sample lengths from a function's contract."""
    import ode as kspec_ode
    spec = kspec_ode.Spec(spec_text)
    if symbol not in spec.contracts:
        return {}, {}
    arg_regs = ARG_REGS_ARM if target == "arm64" else ARG_REGS_X86
    init_regs = {}
    init_mem = {}
    base = 0x100000
    step = 0x10000
    c = spec.contracts[symbol]
    # Distinct pages + distinct low-12-bit offsets (+0x400 per arg) so default aligned buffers have no artificial 4K aliasing.
    base = 0x100000
    step = 0x10400
    params = c["args"] if isinstance(c, dict) else getattr(c, "args", [])
    for idx, (pname, ptype) in enumerate(params):
        if idx >= len(arg_regs):
            break
        reg = arg_regs[idx]
        t = str(ptype).strip()
        if t in ("number", "u64", "u32", "byte", "any"):
            init_regs[reg] = 64
        else:
            addr = base + idx * step + align
            init_regs[reg] = addr
            for k in range(256):
                init_mem[addr + k] = (k * 17 + 1) & 0xFF
    return init_regs, init_mem


def parse_arg_overrides(items):
    out = {}
    for item in items or ():
        if "=" not in item:
            raise SystemExit(f"ode_tool: --arg expects REG=VALUE, not {item!r}")
        k, v = item.split("=", 1)
        out[k.strip()] = int(v.strip(), 0)
    return out


def parse_budgets(args):
    out = {}
    for key in ("max_bytes", "max_icache_lines", "max_frame_bytes", "max_loop_cycles",
                "max_line_splits", "max_page_crossings", "max_stlf_partial", "max_alias_4k"):
        val = getattr(args, key, None)
        if val is not None:
            out[key] = val
    return out


def _contracts_map(spec_text):
    try:
        import ode as kspec_ode
        return kspec_ode.Spec(spec_text).contracts
    except Exception:
        return {}


def run_check(src_path, spec_path=None, fn_names=None, out_dir=None, arch=None,
              do_trace=False, align=0, arg_overrides=None, budgets=None, includes=None, target=None):
    """Compile -> prove -> verify via `odeverify` -> optional performance & memory advice.
    Returns a structured dict with verdict (`shown`, `refused`, `no proof found`, or `FALSE`),
    timings, diagnostics mapped to source lines, decoded arithmetic goals, and advice."""
    import built, ode_unified, prove, statement
    t0 = time.time()
    src_text = odec.read_source(src_path)
    unified = ode_unified.is_unified(src_text)
    resolved_target, compiled = compile_source(src_path, fn_names, target=target)
    t_compile = time.time() - t0
    by_sym = {info["symbol"]: info for info in compiled}

    if unified and spec_path is None:
        parsed = ode_unified.parse_unified(src_text, src_path)
        spec_text, _ = ode_unified.extract_spec(parsed, target_key=target or resolved_target, include_calling=True, src=src_path)
    elif spec_path is None:
        raise SystemExit(
            f"ode_tool: {src_path}: every Ode function must have a contract "
            f"(use unified `.ode` syntax with contract clauses on `fn`, or pass a contract file)"
        )
    else:
        spec_text = load_spec_text(spec_path, includes)
    target = resolved_target
    contracts = _contracts_map(spec_text)

    tmp_obj = None
    work_dir = out_dir
    if work_dir is None:
        tmp_obj = tempfile.TemporaryDirectory()
        work_dir = tmp_obj.name
    else:
        os.makedirs(work_dir, exist_ok=True)

    try:
        targets = []
        progs, lmaps = {}, {}
        for info in compiled:
            sym = info["symbol"]
            obj_path = os.path.join(work_dir, f"{sym}.o")
            with open(obj_path, "wb") as f:
                f.write(info["elf"])
            pl_text = info["places"].get(sym, "")
            targets.append((obj_path, sym, pl_text))
            _, dec = estimate.decode_object(obj_path, sym, target)
            progs[sym] = dec
            lmaps[sym] = info["line_map"]

        st_path = os.path.join(work_dir, "out.statement")
        pf_path = os.path.join(work_dir, "out.proof")

        # Ensure Lean binaries are built
        built.built("odeverify")
        verify_exe = prove.EXE
        t1 = time.time()
        try:
            numbers = prove.prove(spec_text, targets, st_path, pf_path)
            t_prove = time.time() - t1
        except SystemExit as exc:
            t_prove = time.time() - t1
            pc, fn_sym, loc_msg = prove.locate(st_path, pf_path)
            raw = loc_msg or str(exc)
            if fn_sym is None:
                m = re.search(r"in (\S+)", str(exc))
                if m: fn_sym = m.group(1)
            if fn_sym is None:
                m = re.search(r"no proof of (\S+) found", str(exc))
                if m: fn_sym = m.group(1)
            if pc is None:
                m = re.search(r"at \+(\d+)", str(exc))
                if m: pc = int(m.group(1))
            diag, arith = format_source_diagnostic(
                by_sym, pc, fn_sym, raw, target=target, contract=contracts.get(fn_sym), spec_text=spec_text,
            )
            ref = None
            probe_sym = fn_sym if fn_sym in progs else compiled[-1]["symbol"]
            if probe_sym in progs:
                ref = refute_conc.refute_function(progs, probe_sym, spec_text, target)
                diag = diag + "\n" + refute_conc.format_refutation(ref, probe_sym)
            verdict = "FALSE" if (ref and ref["status"] == "FALSE") else "no proof found"
            return {
                "verdict": verdict,
                "target": target,
                "compile_s": round(t_compile, 3),
                "prove_s": round(t_prove, 3),
                "verify_s": 0.0,
                "pc": pc,
                "fn": fn_sym,
                "arithmetic": arith,
                "refutation": ref,
                "diagnostic": diag,
                "raw": str(exc),
            }

        # Run the independent Lean verifier binary `odeverify` directly as the final arbiter
        t2 = time.time()
        tab = statement.table_for(st_path)
        vr = subprocess.run([verify_exe, tab, st_path, pf_path], capture_output=True, text=True)
        t_verify = time.time() - t2
        if vr.returncode != 0 or not vr.stdout.startswith("shown"):
            pc, fn_sym, loc_msg = prove.locate(st_path, pf_path)
            diag, arith = format_source_diagnostic(by_sym, pc, fn_sym, loc_msg or vr.stdout, target=target, contract=contracts.get(fn_sym))
            probe_sym = fn_sym if fn_sym in progs else compiled[-1]["symbol"]
            ref = refute_conc.refute_function(progs, probe_sym, spec_text, target) if probe_sym in progs else None
            if ref is not None:
                diag = diag + "\n" + refute_conc.format_refutation(ref, probe_sym)
            verdict = "FALSE" if (ref and ref["status"] == "FALSE") else "refused"
            return {
                "verdict": verdict,
                "target": target,
                "compile_s": round(t_compile, 3),
                "prove_s": round(t_prove, 3),
                "verify_s": round(t_verify, 3),
                "pc": pc,
                "fn": fn_sym,
                "arithmetic": arith,
                "refutation": ref,
                "diagnostic": diag,
                "raw": vr.stdout,
            }

        # Collect static + optional memory advice for the top/last compiled function
        top = compiled[-1]
        top_sym = top["symbol"]
        static_rep = estimate.static_analyze(progs[top_sym], target, arch, lmaps[top_sym], top["frame"])
        mem_rep = None
        if do_trace or arg_overrides:
            init_r, init_m = default_args_from_spec(spec_text, top_sym, target, align=align)
            if arg_overrides:
                init_r.update(arg_overrides)
            tr = estimate.trace_memory(progs, top_sym, target, init_regs=init_r, init_mem=init_m, line_maps=lmaps)
            mem_rep = estimate.analyze_memory(tr, target, arch, top["frame"])
        eff_budgets = dict(top.get("budget") or {})
        if budgets:
            eff_budgets.update(budgets)
        budget_errs = estimate.check_budgets(static_rep, mem_rep, eff_budgets)

        return {
            "verdict": "shown",
            "target": target,
            "functions": [info["symbol"] for info in compiled],
            "code_bytes": {info["symbol"]: info["code_bytes"] for info in compiled},
            "proof_bytes": os.path.getsize(pf_path),
            "proof_runs": numbers,
            "compile_s": round(t_compile, 3),
            "prove_s": round(t_prove, 3),
            "verify_s": round(t_verify, 3),
            "top_symbol": top_sym,
            "static": static_rep,
            "memory": mem_rep,
            "budgets": eff_budgets,
            "budget_errors": budget_errs,
            "advice_text": estimate.format_report(top_sym, static_rep, mem_rep),
        }
    finally:
        if tmp_obj is not None:
            tmp_obj.cleanup()


def run_advise(src_path, fn_name=None, spec_path=None, arch=None, do_trace=False,
               align=0, arg_overrides=None, budgets=None, includes=None, target=None, all_archs=False):
    """Compile and run static + optional memory advice without invoking Lean."""
    target, compiled = compile_source(src_path, None, target=target)
    by_name = {info["name"]: info for info in compiled}
    by_sym = {info["symbol"]: info for info in compiled}
    if fn_name is None:
        top = compiled[-1]
    elif fn_name in by_name:
        top = by_name[fn_name]
    elif fn_name in by_sym:
        top = by_sym[fn_name]
    else:
        raise SystemExit(f"ode_tool: {src_path}: no function {fn_name}")
    top_sym = top["symbol"]
    spec_text = load_spec_text(spec_path, includes) if spec_path else None
    with tempfile.TemporaryDirectory() as td:
        progs, lmaps = {}, {}
        for info in compiled:
            sym = info["symbol"]
            op = os.path.join(td, f"{sym}.o")
            with open(op, "wb") as f:
                f.write(info["elf"])
            _, dec = estimate.decode_object(op, sym, target)
            progs[sym] = dec
            lmaps[sym] = info["line_map"]
        static_rep = estimate.static_analyze(
            progs[top_sym], target, arch, lmaps[top_sym], top["frame"], all_archs=all_archs
        )
        mem_rep = None
        if do_trace or arg_overrides:
            init_r, init_m = default_args_from_spec(spec_text, top_sym, target, align=align) if spec_text else ({}, {})
            if arg_overrides:
                init_r.update(arg_overrides)
            tr = estimate.trace_memory(progs, top_sym, target, init_regs=init_r, init_mem=init_m, line_maps=lmaps)
            mem_rep = estimate.analyze_memory(tr, target, arch, top["frame"])
        eff_budgets = dict(top.get("budget") or {})
        if budgets:
            eff_budgets.update(budgets)
        budget_errs = estimate.check_budgets(static_rep, mem_rep, eff_budgets)
        return {
            "target": target,
            "symbol": top_sym,
            "static": static_rep,
            "memory": mem_rep,
            "budgets": eff_budgets,
            "budget_errors": budget_errs,
            "advice_text": estimate.format_report(top_sym, static_rep, mem_rep),
        }


def run_refute(src_path, spec_path, fn_names=None, cases=16, seed=1, includes=None):
    """Compile and run table-driven concrete counterexample probes (no Lean needed)."""
    target, compiled = compile_source(src_path, fn_names)
    spec_text = load_spec_text(spec_path, includes)
    with tempfile.TemporaryDirectory() as td:
        progs = {}
        for info in compiled:
            sym = info["symbol"]
            op = os.path.join(td, f"{sym}.o")
            with open(op, "wb") as f:
                f.write(info["elf"])
            _, dec = estimate.decode_object(op, sym, target)
            progs[sym] = dec
        results = {}
        for info in compiled:
            sym = info["symbol"]
            results[sym] = refute_conc.refute_function(progs, sym, spec_text, target, cases=cases, seed=seed)
        return target, results


def _add_common_flags(p):
    p.add_argument("--include", action="append", default=[], help="additional .spec file(s) prepended before spec (repeatable)")
    p.add_argument("--json", action="store_true", help="emit machine-readable JSON output")
    p.add_argument("--arch", choices=sorted(estimate.ARCHS), default=None, help="microarchitecture profile")
    p.add_argument("--all-archs", action="store_true", help="print static pipeline estimates across all calibrated CPUs for this target")
    p.add_argument("--trace", action="store_true", help="run concrete memory-access trace via core/conc.py")
    p.add_argument("--align", type=int, default=0, help="byte misalignment added to default buffer addresses")
    p.add_argument("--arg", action="append", default=[], help="initial register value REG=VAL (repeatable)")
    p.add_argument("--max-bytes", type=int, default=None)
    p.add_argument("--max-icache-lines", type=int, default=None)
    p.add_argument("--max-frame-bytes", type=int, default=None)
    p.add_argument("--max-loop-cycles", type=int, default=None)
    p.add_argument("--max-line-splits", type=int, default=None)
    p.add_argument("--max-page-crossings", type=int, default=None)
    p.add_argument("--max-stlf-partial", type=int, default=None)
    p.add_argument("--max-alias-4k", type=int, default=None)


def _json_safe(obj):
    if isinstance(obj, (str, int, float, bool)) or obj is None:
        return obj
    if isinstance(obj, bytes):
        return obj.hex()
    if isinstance(obj, dict):
        return {str(k): _json_safe(v) for k, v in obj.items()}
    if isinstance(obj, (list, tuple)):
        return [_json_safe(x) for x in obj]
    return str(obj)


def handle_request(req):
    """Handle one JSON-lines request for `ode_tool.py serve`; returns a JSON-safe response dict."""
    cmd = req.get("cmd")
    try:
        if cmd == "check":
            res = run_check(req["source"], req["spec"], fn_names=req.get("fn"), out_dir=req.get("out"),
                            arch=req.get("arch"), do_trace=bool(req.get("trace", False)),
                            align=int(req.get("align", 0)), arg_overrides=req.get("args") or None,
                            budgets=req.get("budgets") or None, includes=req.get("include") or None)
            return {"ok": res["verdict"] == "shown" and not res.get("budget_errors"), "result": _json_safe(res)}
        if cmd == "advise":
            res = run_advise(req["source"], fn_name=req.get("fn"), spec_path=req.get("spec"),
                             arch=req.get("arch"), do_trace=bool(req.get("trace", False)),
                             align=int(req.get("align", 0)), arg_overrides=req.get("args") or None,
                             budgets=req.get("budgets") or None, includes=req.get("include") or None)
            return {"ok": not res.get("budget_errors"), "result": _json_safe(res)}
        if cmd == "refute":
            target, res = run_refute(req["source"], req["spec"], fn_names=req.get("fn"),
                                     cases=int(req.get("cases", 16)), seed=int(req.get("seed", 1)),
                                     includes=req.get("include") or None)
            any_false = any(v["status"] == "FALSE" for v in res.values())
            return {"ok": not any_false, "target": target, "results": _json_safe(res)}
        return {"ok": False, "error": f"unknown cmd: {cmd!r}"}
    except BaseException as exc:
        if isinstance(exc, KeyboardInterrupt):
            raise
        err = str(exc)
        out = {"ok": False, "error": err}
        hint = _compile_error_hint(err)
        if hint:
            out["hint"] = hint
        return out


def main(argv=None):
    ap = argparse.ArgumentParser(prog="ode_tool.py", description="Integrated Ode compiler, prover, verifier runner, and advisor.")
    sub = ap.add_subparsers(dest="cmd", required=True)

    p_chk = sub.add_parser("check", help="compile, prove, verify via odeverify, and print advice")
    p_chk.add_argument("source", help=".ode source file (unified or legacy)")
    p_chk.add_argument("spec", nargs="?", default=None, help="optional legacy .spec contract file (omit for unified .ode)")
    p_chk.add_argument("--fn", action="append", default=None, help="function name(s) in source (default: all)")
    p_chk.add_argument("--target", default=None, help="target architecture (e.g. x86_64, arm64) for multi-target .ode")
    p_chk.add_argument("--out", default=None, help="directory to write .o, .statement, and .proof")
    _add_common_flags(p_chk)

    p_adv = sub.add_parser("advise", help="compile and print static + optional memory advice (no Lean)")
    p_adv.add_argument("source", help=".ode source file")
    p_adv.add_argument("--fn", default=None, help="function name or symbol (default: last in source)")
    p_adv.add_argument("--spec", default=None, help="optional .spec file for default --trace argument layout")
    p_adv.add_argument("--target", default=None, help="target architecture (e.g. x86_64, arm64) for multi-target .ode")
    _add_common_flags(p_adv)

    p_cmp = sub.add_parser("compare", help="compare two Ode variants side by side (with optional verification)")
    p_cmp.add_argument("source_a", help="first .ode variant (A)")
    p_cmp.add_argument("source_b", help="second .ode variant (B)")
    p_cmp.add_argument("--fn", default=None, help="function name or symbol to compare")
    p_cmp.add_argument("--spec", default=None, help="optional .spec file (verifies both variants via odeverify)")
    _add_common_flags(p_cmp)

    p_ref = sub.add_parser("refute", help="run concrete counterexample probes via core/conc.py (no Lean)")
    p_ref.add_argument("source", help=".ode source file")
    p_ref.add_argument("spec", help=".spec contract file")
    p_ref.add_argument("--include", action="append", default=[], help="additional .spec file(s) prepended before spec")
    p_ref.add_argument("--json", action="store_true", help="emit machine-readable JSON output")
    p_ref.add_argument("--fn", action="append", default=None, help="function name(s) in source (default: all)")
    p_ref.add_argument("--cases", type=int, default=16, help="number of concrete probe cases per function")
    p_ref.add_argument("--seed", type=int, default=1)

    sub.add_parser("serve", help="persistent JSON-lines worker on stdin/stdout (keeps tables and Python warm)")

    p_can = sub.add_parser("canon", help="extract/canonicalize a contract to nameless .ocl and print its 52-char BLAKE3 ID")
    p_can.add_argument("spec", help="unified .ode source file, or .ocl/.spec contract file")
    p_can.add_argument("--contract", "--fn", dest="contract", default=None, help="function/contract name (required if file defines multiple)")
    p_can.add_argument("--target", default=None, help="target architecture (x86_64, arm64) for multi-target .ode")
    p_can.add_argument("--out-dir", default=None, help="write hash-named <52-char-b32>.ocl file into this directory")
    p_can.add_argument("--glossary-out", default=None, help="write author-name glossary JSON to this path")
    p_can.add_argument("--json", action="store_true", help="emit machine-readable JSON output")

    p_pck = sub.add_parser("pack", help="compile .ode, bind symbol to ode_<52-char-b32>, embed .ode.ocl, prove, and audit")
    p_pck.add_argument("source", help=".ode source file (unified or legacy)")
    p_pck.add_argument("spec", nargs="?", default=None, help="optional legacy .ocl/.spec contract file (omit for unified .ode)")
    p_pck.add_argument("--out", required=True, help="output ELF .o path (carries embedded .ode.ocl)")
    p_pck.add_argument("--proof", required=True, help="output separate .proof file path")
    p_pck.add_argument("--fn", default=None, help="function name in source (default: last in source)")
    p_pck.add_argument("--target", default=None, help="target architecture (x86_64, arm64) for multi-target .ode")
    p_pck.add_argument("--glossary-out", default=None, help="write separate author glossary JSON")
    p_pck.add_argument("--include", action="append", default=[], help="additional .ocl/.spec file(s) prepended before spec")
    p_pck.add_argument("--json", action="store_true", help="emit machine-readable JSON output")

    p_aud = sub.add_parser("audit", help="binary-first auditor: check coverage, .ode.ocl, BLAKE3 hashes, and odeverify")
    p_aud.add_argument("binary", help="compiled ELF binary (.o) to audit")
    p_aud.add_argument("--proof", default=None, help="separate .proof file (optional for loop-free single-function .o)")
    p_aud.add_argument("--expect-contract", default=None, help="full 52-char lowercase base-32 BLAKE3 contract ID")
    p_aud.add_argument("--contract", default=None, help="optional external .ocl/.spec file (must match embedded .ode.ocl if present)")
    p_aud.add_argument("--glossary", default=None, help="optional local glossary JSON for --show-contract rendering")
    p_aud.add_argument("--show-contract", action="store_true", help="print the verified canonical contract")
    p_aud.add_argument("--json", action="store_true", help="emit machine-readable JSON output")

    p_st = sub.add_parser("spec-test", help="evaluate a definition in a .ocl/.spec contract on concrete JSON inputs")
    p_st.add_argument("spec", help=".ocl or .spec contract file")
    p_st.add_argument("--call", required=True, help="definition name (canonical e.g. f0, or glossary name with --glossary)")
    p_st.add_argument("--arg", action="append", default=[], help="JSON-encoded argument (repeat for each parameter)")
    p_st.add_argument("--glossary", default=None, help="optional glossary JSON mapping canonical names to human names")

    args = ap.parse_args(argv)
    if args.cmd == "serve":
        for line in sys.stdin:
            line = line.strip()
            if not line:
                continue
            try:
                req = json.loads(line)
            except json.JSONDecodeError as exc:
                resp = {"ok": False, "error": f"bad json: {exc}"}
            else:
                resp = handle_request(req)
            sys.stdout.write(json.dumps(resp) + "\n")
            sys.stdout.flush()
        return 0

    overrides = parse_arg_overrides(getattr(args, "arg", None)) if args.cmd in ("check", "advise", "compare") else {}
    budgets = parse_budgets(args) if args.cmd in ("check", "advise", "compare") else {}

    if args.cmd == "check":
        res = run_check(args.source, args.spec, fn_names=args.fn, out_dir=args.out, arch=args.arch,
                        do_trace=args.trace, align=args.align, arg_overrides=overrides,
                        budgets=budgets, includes=args.include, target=args.target)
        if args.json:
            print(json.dumps(_json_safe(res)))
            if res["verdict"] != "shown": return 1
            return 2 if res["budget_errors"] else 0
        if res["verdict"] != "shown":
            print(res["diagnostic"])
            return 1
        syms = ", ".join(res["functions"])
        print(f"shown: {syms} (target {res['target']}, proof {res['proof_bytes']} B; "
              f"compile {res['compile_s']:.2f}s, prove {res['prove_s']:.2f}s, verify {res['verify_s']:.2f}s)")
        print(res["advice_text"])
        if res["budget_errors"]:
            for e in res["budget_errors"]:
                print("FAIL:", e)
            return 2
        return 0

    if args.cmd == "advise":
        res = run_advise(args.source, fn_name=args.fn, spec_path=args.spec, arch=args.arch,
                         do_trace=args.trace, align=args.align, arg_overrides=overrides,
                         budgets=budgets, includes=args.include, target=args.target,
                         all_archs=args.all_archs)
        if args.json:
            print(json.dumps(_json_safe(res)))
            return 2 if res["budget_errors"] else 0
        print(res["advice_text"])
        if res["budget_errors"]:
            for e in res["budget_errors"]:
                print("FAIL:", e)
            return 2
        return 0

    if args.cmd == "compare":
        if args.spec:
            ra = run_check(args.source_a, args.spec, fn_names=[args.fn] if args.fn else None, arch=args.arch,
                           do_trace=args.trace, align=args.align, arg_overrides=overrides, includes=args.include)
            rb = run_check(args.source_b, args.spec, fn_names=[args.fn] if args.fn else None, arch=args.arch,
                           do_trace=args.trace, align=args.align, arg_overrides=overrides, includes=args.include)
            if args.json:
                print(json.dumps(_json_safe({"a": ra, "b": rb})))
                return 0 if (ra["verdict"] == "shown" and rb["verdict"] == "shown") else 1
            print(f"verdicts: A={ra['verdict']}, B={rb['verdict']}")
            if ra["verdict"] != "shown": print("A:\n" + ra["diagnostic"])
            if rb["verdict"] != "shown": print("B:\n" + rb["diagnostic"])
            if ra["verdict"] != "shown" or rb["verdict"] != "shown":
                return 1
            print(estimate.compare_reports(os.path.basename(args.source_a), ra["static"], ra["memory"],
                                           os.path.basename(args.source_b), rb["static"], rb["memory"]))
            return 0
        ra = run_advise(args.source_a, fn_name=args.fn, arch=args.arch, do_trace=args.trace,
                        align=args.align, arg_overrides=overrides, includes=args.include)
        rb = run_advise(args.source_b, fn_name=args.fn, arch=args.arch, do_trace=args.trace,
                        align=args.align, arg_overrides=overrides, includes=args.include)
        if args.json:
            print(json.dumps(_json_safe({"a": ra, "b": rb})))
            return 0
        print(estimate.compare_reports(os.path.basename(args.source_a), ra["static"], ra["memory"],
                                       os.path.basename(args.source_b), rb["static"], rb["memory"]))
        return 0

    if args.cmd == "refute":
        target, results = run_refute(args.source, args.spec, fn_names=args.fn, cases=args.cases,
                                     seed=args.seed, includes=args.include)
        any_false = any(res["status"] == "FALSE" for res in results.values())
        if args.json:
            print(json.dumps(_json_safe({"target": target, "results": results})))
            return 1 if any_false else 0
        for sym, res in results.items():
            print(refute_conc.format_refutation(res, sym))
        return 1 if any_false else 0

    if args.cmd == "canon":
        import ode_canon
        res = ode_canon.canonicalize_file(args.spec, contract_name=args.contract, target=args.target)
        out_path = None
        if args.out_dir:
            os.makedirs(args.out_dir, exist_ok=True)
            out_path = os.path.join(args.out_dir, ode_canon.ocl_filename(res["contract_id"]))
            with open(out_path, "w", encoding="utf-8") as of:
                of.write(res["canonical"])
        if args.glossary_out:
            with open(args.glossary_out, "w", encoding="utf-8") as gf:
                json.dump({"contract_id": res["contract_id"], "glossary": res["glossary"]}, gf, indent=2, sort_keys=True)
                gf.write("\n")
        if args.json:
            payload = dict(res)
            if out_path is not None:
                payload["ocl_path"] = out_path
            print(json.dumps(payload, indent=2, sort_keys=True))
            return 0
        print(f"BLAKE3(contract): {res['contract_id']}")
        print(f"SYMBOL:           {res['symbol']}")
        if out_path is not None:
            print(f"WROTE:            {out_path}")
        print("")
        print(res["canonical"].rstrip())
        return 0

    if args.cmd == "pack":
        import ode_audit
        try:
            res = ode_audit.pack_verified(
                args.source, args.spec, args.out, args.proof,
                fn_name=args.fn, target=args.target, glossary_out=args.glossary_out, includes=args.include,
            )
        except ode_audit.PackProofError as exc:
            by_sym = {exc.fn_sym: exc.info} if (exc.fn_sym and exc.info) else {}
            diag, _ = format_source_diagnostic(
                by_sym, exc.pc, exc.fn_sym, exc.reason,
                target=exc.target, contract=exc.contract, spec_text=exc.spec_text,
            )
            print(diag)
            return 1
        except SystemExit as exc:
            msg = str(exc)
            marker = "The verifier's last word:\n"
            body = msg.split(marker, 1)[1] if marker in msg else msg
            if body.lstrip().startswith("need "):
                tgt = args.target or "x86_64"
                diag, _ = format_source_diagnostic({}, None, None, body, target=tgt)
                print(diag)
                return 1
            raise
        if args.json:
            print(json.dumps(_json_safe(res), indent=2, sort_keys=True))
            return 0 if res["verdict"] == "shown" else 1
        print(ode_audit.format_audit_report(res))
        return 0 if res["verdict"] == "shown" else 1

    if args.cmd == "audit":
        import ode_audit
        res = ode_audit.audit_binary(
            args.binary, args.proof,
            expect_contract=args.expect_contract,
            contract_path=args.contract,
        )
        glossary = None
        if args.glossary:
            with open(args.glossary, "r", encoding="utf-8") as gf:
                gdata = json.load(gf)
            glossary = gdata.get("glossary", gdata)
        if args.json:
            print(json.dumps(_json_safe(res), indent=2, sort_keys=True))
            return 0 if res["verdict"] == "shown" else 1
        print(ode_audit.format_audit_report(res, show_contract=args.show_contract, glossary=glossary))
        return 0 if res["verdict"] == "shown" else 1

    if args.cmd == "spec-test":
        import ode_audit
        val = ode_audit.run_spec_test(args.spec, args.call, args.arg, glossary_path=args.glossary)
        print(json.dumps(val))
        return 0


def _cli():
    """`main`, with what the source or the command line got wrong said in one line (exit 2), no traceback.
    Any other exception is a fault of the tool and keeps its traceback."""
    try:
        return main()
    except SystemExit as exc:
        if isinstance(exc.code, str) and exc.code:
            print(exc.code, file=sys.stderr)
            hint = _compile_error_hint(exc.code)
            if hint:
                print(f"  {hint}", file=sys.stderr)
            return 2
        raise
    except Exception as exc:
        if type(exc).__name__ in ("UnifiedErr", "Err", "ValueError"):
            print(f"ode: {exc}", file=sys.stderr)
            hint = _compile_error_hint(str(exc))
            if hint:
                print(f"  {hint}", file=sys.stderr)
            return 2
        raise


if __name__ == "__main__":
    sys.exit(_cli())
