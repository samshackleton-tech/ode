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
"""
import argparse, os, re, shutil, subprocess, sys, tempfile, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for d in (HERE, os.path.join(ROOT, "advice"), os.path.join(ROOT, "proof-core"),
          os.path.join(ROOT, "kcheck"), os.path.join(ROOT, "arm64"), os.path.join(ROOT, "core")):
    if d not in sys.path:
        sys.path.insert(0, d)
import estimate, odec

ARG_REGS_X86 = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"]
ARG_REGS_ARM = ["x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7"]


def compile_source(src_path, fn_names=None):
    """Compile selected (or all) functions of an Ode source file via odec.compile_info."""
    text = odec.read_source(src_path)
    target, _, _, fns = odec.source(text, src_path)
    want = fn_names if fn_names else [name for name, _, _, _ in fns]
    compiled = []
    for name in want:
        compiled.append(odec.compile_info(src_path, name))
    return target, compiled


def format_source_diagnostic(compiled_by_sym, pc, fn_sym, reason):
    """Translate a verifier refusal `(fn_sym, pc, reason)` into source file, line, reg names, and frame fields."""
    out = []
    info = compiled_by_sym.get(fn_sym) if fn_sym else None
    if info is not None and pc is not None:
        row = next((r for r in info["line_map"] if r["pc"] == pc), None)
        if row is None:
            # Closest instruction at or before pc
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
    for line in reason.strip().splitlines():
        out.append(f"  {line}")
    return "\n".join(out)


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
    for key in ("max_bytes", "max_icache_lines", "max_frame_bytes",
                "max_line_splits", "max_page_crossings", "max_stlf_partial", "max_alias_4k"):
        val = getattr(args, key, None)
        if val is not None:
            out[key] = val
    return out


def run_check(src_path, spec_path, fn_names=None, out_dir=None, arch=None,
              do_trace=False, align=0, arg_overrides=None, budgets=None):
    """Compile -> prove -> verify via `odeverify` -> optional performance & memory advice.
    Returns a structured dict with verdict (`shown`, `refused`, or `no proof found`), timings,
    diagnostics mapped to source lines, and advice."""
    import built, prove, statement
    t0 = time.time()
    target, compiled = compile_source(src_path, fn_names)
    t_compile = time.time() - t0
    by_sym = {info["symbol"]: info for info in compiled}

    with open(spec_path) as f:
        spec_text = f.read()

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
            if pc is None:
                m = re.search(r"at \+(\d+)", str(exc))
                if m: pc = int(m.group(1))
            diag = format_source_diagnostic(by_sym, pc, fn_sym, raw)
            return {
                "verdict": "no proof found",
                "target": target,
                "compile_s": round(t_compile, 3),
                "prove_s": round(t_prove, 3),
                "verify_s": 0.0,
                "pc": pc,
                "fn": fn_sym,
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
            diag = format_source_diagnostic(by_sym, pc, fn_sym, loc_msg or vr.stdout)
            return {
                "verdict": "refused",
                "target": target,
                "compile_s": round(t_compile, 3),
                "prove_s": round(t_prove, 3),
                "verify_s": round(t_verify, 3),
                "pc": pc,
                "fn": fn_sym,
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
        budget_errs = estimate.check_budgets(static_rep, mem_rep, budgets)

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
            "budget_errors": budget_errs,
            "advice_text": estimate.format_report(top_sym, static_rep, mem_rep),
        }
    finally:
        if tmp_obj is not None:
            tmp_obj.cleanup()


def run_advise(src_path, fn_name=None, spec_path=None, arch=None, do_trace=False,
               align=0, arg_overrides=None, budgets=None):
    """Compile and run static + optional memory advice without invoking Lean."""
    target, compiled = compile_source(src_path, None)
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
    spec_text = None
    if spec_path:
        with open(spec_path) as f:
            spec_text = f.read()
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
        static_rep = estimate.static_analyze(progs[top_sym], target, arch, lmaps[top_sym], top["frame"])
        mem_rep = None
        if do_trace or arg_overrides:
            init_r, init_m = default_args_from_spec(spec_text, top_sym, target, align=align) if spec_text else ({}, {})
            if arg_overrides:
                init_r.update(arg_overrides)
            tr = estimate.trace_memory(progs, top_sym, target, init_regs=init_r, init_mem=init_m, line_maps=lmaps)
            mem_rep = estimate.analyze_memory(tr, target, arch, top["frame"])
        budget_errs = estimate.check_budgets(static_rep, mem_rep, budgets)
        return {
            "target": target,
            "symbol": top_sym,
            "static": static_rep,
            "memory": mem_rep,
            "budget_errors": budget_errs,
            "advice_text": estimate.format_report(top_sym, static_rep, mem_rep),
        }


def _add_common_flags(p):
    p.add_argument("--arch", choices=sorted(estimate.ARCHS), default=None, help="microarchitecture profile")
    p.add_argument("--trace", action="store_true", help="run concrete memory-access trace via core/conc.py")
    p.add_argument("--align", type=int, default=0, help="byte misalignment added to default buffer addresses")
    p.add_argument("--arg", action="append", default=[], help="initial register value REG=VAL (repeatable)")
    p.add_argument("--max-bytes", type=int, default=None)
    p.add_argument("--max-icache-lines", type=int, default=None)
    p.add_argument("--max-frame-bytes", type=int, default=None)
    p.add_argument("--max-line-splits", type=int, default=None)
    p.add_argument("--max-page-crossings", type=int, default=None)
    p.add_argument("--max-stlf-partial", type=int, default=None)
    p.add_argument("--max-alias-4k", type=int, default=None)


def main(argv=None):
    ap = argparse.ArgumentParser(prog="ode_tool.py", description="Integrated Ode compiler, prover, verifier runner, and advisor.")
    sub = ap.add_subparsers(dest="cmd", required=True)

    p_chk = sub.add_parser("check", help="compile, prove, verify via odeverify, and print advice")
    p_chk.add_argument("source", help=".ode source file")
    p_chk.add_argument("spec", help=".spec contract file")
    p_chk.add_argument("--fn", action="append", default=None, help="function name(s) in source (default: all)")
    p_chk.add_argument("--out", default=None, help="directory to write .o, .statement, and .proof")
    _add_common_flags(p_chk)

    p_adv = sub.add_parser("advise", help="compile and print static + optional memory advice (no Lean)")
    p_adv.add_argument("source", help=".ode source file")
    p_adv.add_argument("--fn", default=None, help="function name or symbol (default: last in source)")
    p_adv.add_argument("--spec", default=None, help="optional .spec file for default --trace argument layout")
    _add_common_flags(p_adv)

    p_cmp = sub.add_parser("compare", help="compare two Ode variants side by side (with optional verification)")
    p_cmp.add_argument("source_a", help="first .ode variant (A)")
    p_cmp.add_argument("source_b", help="second .ode variant (B)")
    p_cmp.add_argument("--fn", default=None, help="function name or symbol to compare")
    p_cmp.add_argument("--spec", default=None, help="optional .spec file (verifies both variants via odeverify)")
    _add_common_flags(p_cmp)

    args = ap.parse_args(argv)
    overrides = parse_arg_overrides(args.arg)
    budgets = parse_budgets(args)

    if args.cmd == "check":
        res = run_check(args.source, args.spec, fn_names=args.fn, out_dir=args.out, arch=args.arch,
                        do_trace=args.trace, align=args.align, arg_overrides=overrides, budgets=budgets)
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
                         do_trace=args.trace, align=args.align, arg_overrides=overrides, budgets=budgets)
        print(res["advice_text"])
        if res["budget_errors"]:
            for e in res["budget_errors"]:
                print("FAIL:", e)
            return 2
        return 0

    if args.cmd == "compare":
        if args.spec:
            ra = run_check(args.source_a, args.spec, fn_names=[args.fn] if args.fn else None, arch=args.arch,
                           do_trace=args.trace, align=args.align, arg_overrides=overrides)
            rb = run_check(args.source_b, args.spec, fn_names=[args.fn] if args.fn else None, arch=args.arch,
                           do_trace=args.trace, align=args.align, arg_overrides=overrides)
            print(f"verdicts: A={ra['verdict']}, B={rb['verdict']}")
            if ra["verdict"] != "shown": print("A:\n" + ra["diagnostic"])
            if rb["verdict"] != "shown": print("B:\n" + rb["diagnostic"])
            if ra["verdict"] != "shown" or rb["verdict"] != "shown":
                return 1
            print(estimate.compare_reports(os.path.basename(args.source_a), ra["static"], ra["memory"],
                                           os.path.basename(args.source_b), rb["static"], rb["memory"]))
            return 0
        ra = run_advise(args.source_a, fn_name=args.fn, arch=args.arch, do_trace=args.trace,
                        align=args.align, arg_overrides=overrides)
        rb = run_advise(args.source_b, fn_name=args.fn, arch=args.arch, do_trace=args.trace,
                        align=args.align, arg_overrides=overrides)
        print(estimate.compare_reports(os.path.basename(args.source_a), ra["static"], ra["memory"],
                                       os.path.basename(args.source_b), rb["static"], rb["memory"]))
        return 0


if __name__ == "__main__":
    sys.exit(main())
