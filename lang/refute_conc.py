#!/usr/bin/env python3
"""refute_conc: table-driven concrete counterexample finder ("FALSE, and here is the input")
for Ode functions on BOTH x86-64 and AArch64, running through core/conc.py on any host.

Relied on for nothing by the verifier (`odeverify`). When a proof fails, this tool quickly tests
edge-case and random concrete inputs against the specification to separate:
  - FALSE (concrete counterexample found: code or contract is wrong), from
  - not refuted (all probe inputs matched: likely a missing loop place, trace clause, or proof step).
"""
import os, random, re, struct, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for d in (HERE, os.path.join(ROOT, "advice"), os.path.join(ROOT, "kcheck"),
          os.path.join(ROOT, "arm64"), os.path.join(ROOT, "core")):
    if d not in sys.path:
        sys.path.insert(0, d)
import estimate, ode

ARG_REGS_X86 = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"]
ARG_REGS_ARM = ["x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7"]
CALLEE_SAVED_X86 = ["rbx", "rbp", "r12", "r13", "r14", "r15"]
CALLEE_SAVED_ARM = ["x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26", "x27", "x28", "x29"]
FIXED_WORDS = {"block": 16, "cv": 8}


def _to_int(v):
    if isinstance(v, ode.Word):
        return v.v & 0xFFFFFFFF
    if isinstance(v, bool):
        return 1 if v else 0
    return int(v)


def _to_int_list(v):
    return [_to_int(x) for x in v]


def _parse_arg_kind(ptype):
    """Classify a contract parameter type string into ('number',), ('words', n), or ('bytes', len_name_or_int)."""
    t = str(ptype).strip()
    if t in ("number", "u64", "u32", "byte"):
        return ("number",)
    if t in FIXED_WORDS:
        return ("words", FIXED_WORDS[t])
    m = re.fullmatch(r"(\w+)\s+bytes", t)
    if m:
        s = m.group(1)
        return ("bytes", int(s) if s.isdigit() else s)
    return ("unsupported", t)


def _eval_requires(spec, contract, env):
    N = ode.Numbers()
    for cond in contract.get("asks", ()) or ():
        try:
            v = spec.eval(N, cond, env)
        except Exception:
            return False
        if not v:
            return False
    return True


def _make_cases(contract, n_cases=16, seed=1):
    """Generate edge-case and random concrete inputs for a contract's arguments."""
    args = contract.get("args", ())
    kinds = [(name, _parse_arg_kind(ptype)) for name, ptype in args]
    if any(k[0] == "unsupported" for _, k in kinds):
        return None, kinds

    out_names = {lv["name"] for lv in contract.get("leaves", ()) or ()}
    len_vars = {k[1] for _, k in kinds if k[0] == "bytes" and isinstance(k[1], str)}
    rng = random.Random(seed)

    # Structured edge patterns first (catches off-by-one, empty, zero/nonzero, equal/differing)
    edge_lens = [0, 1, 2, 3, 4, 8, 16, 32]
    patterns = ["zero", "first_nz", "last_nz", "all_ff", "ramp", "same_a", "diff_first", "diff_last"]
    cases = []

    for ci in range(max(n_cases * 3, 24)):
        if len(cases) >= n_cases:
            break
        env = {}
        # 1. Assign numbers (especially slice lengths) first
        for name, k in kinds:
            if k[0] == "number":
                if name in len_vars:
                    env[name] = edge_lens[ci] if ci < len(edge_lens) else rng.randint(0, 48)
                else:
                    env[name] = [0, 1, 2, 7, 16, 64][ci] if ci < 6 else rng.randint(0, 1000)

        # 2. Assign byte slices and word blocks
        pat = patterns[ci] if ci < len(patterns) else "rand"
        prev_bytes = None
        prev_words = None
        for name, k in kinds:
            if k[0] == "bytes":
                ln = k[1] if isinstance(k[1], int) else env[k[1]]
                if name in out_names:
                    bs = [0xAA] * ln
                elif pat == "zero":
                    bs = [0] * ln
                elif pat == "first_nz":
                    bs = [0] * ln
                    if ln > 0: bs[0] = 1
                elif pat == "last_nz":
                    bs = [0] * ln
                    if ln > 0: bs[-1] = 1
                elif pat == "all_ff":
                    bs = [0xFF] * ln
                elif pat == "ramp":
                    bs = [(i * 17 + 1) & 0xFF for i in range(ln)]
                elif pat == "same_a" and prev_bytes is not None and len(prev_bytes) == ln:
                    bs = list(prev_bytes)
                elif pat == "diff_first" and prev_bytes is not None and len(prev_bytes) == ln:
                    bs = list(prev_bytes)
                    if ln > 0: bs[0] ^= 1
                elif pat == "diff_last" and prev_bytes is not None and len(prev_bytes) == ln:
                    bs = list(prev_bytes)
                    if ln > 0: bs[-1] ^= 1
                else:
                    bs = [rng.randint(0, 255) for _ in range(ln)]
                env[name] = bs
                if name not in out_names and prev_bytes is None:
                    prev_bytes = bs
            elif k[0] == "words":
                nw = k[1]
                if name in out_names:
                    ws = [ode.Word(0xAAAAAAAA)] * nw
                elif pat == "zero":
                    ws = [ode.Word(0)] * nw
                elif pat == "first_nz":
                    ws = [ode.Word(1 if i == 0 else 0) for i in range(nw)]
                elif pat == "last_nz":
                    ws = [ode.Word(1 if i == nw - 1 else 0) for i in range(nw)]
                elif pat == "all_ff":
                    ws = [ode.Word(0xFFFFFFFF)] * nw
                elif pat == "same_a" and prev_words is not None and len(prev_words) == nw:
                    ws = list(prev_words)
                elif pat == "diff_last" and prev_words is not None and len(prev_words) == nw:
                    ws = list(prev_words)
                    ws[-1] = ode.Word(ws[-1].v ^ 1)
                else:
                    ws = [ode.Word(rng.getrandbits(32)) for _ in range(nw)]
                env[name] = ws
                if name not in out_names and prev_words is None:
                    prev_words = ws
        cases.append(env)
    return cases, kinds


def _fmt_env(env, kinds):
    parts = []
    for name, k in kinds:
        v = env[name]
        if k[0] == "number":
            parts.append(f"{name}={v}")
        elif k[0] == "bytes":
            s = repr(v[:8])[:-1] + ", ...]" if len(v) > 8 else repr(v)
            parts.append(f"{name}={s}")
        elif k[0] == "words":
            ws = [f"0x{_to_int(x):08x}" for x in v[:4]]
            s = "[" + ", ".join(ws) + (", ...]" if len(v) > 4 else "]")
            parts.append(f"{name}={s}")
    return ", ".join(parts)


def refute_function(programs, symbol, spec_text, target, cases=16, seed=1, max_steps=50000):
    """Run concrete probe inputs on `symbol` through core/conc.py and compare against `spec_text`.
    Returns dict with status in {'FALSE', 'not refuted', 'skipped'}."""
    spec = ode.Spec(spec_text)
    if symbol not in spec.contracts:
        return {"status": "skipped", "reason": f"no contract for {symbol}", "cases_run": 0}
    contract = spec.contracts[symbol]
    # Only handle simple unconditional returns / whole-output leaves cleanly
    leaves = contract.get("leaves", ()) or ()
    if any(lv.get("each") or lv.get("part") or lv.get("cond") or lv.get("index") is not None for lv in leaves):
        return {"status": "skipped", "reason": "indexed/conditional ensures not supported by quick refuter", "cases_run": 0}

    generated, kinds = _make_cases(contract, n_cases=cases, seed=seed)
    if generated is None:
        return {"status": "skipped", "reason": "contract argument kind not supported by quick refuter", "cases_run": 0}

    arg_regs = ARG_REGS_ARM if target == "arm64" else ARG_REGS_X86
    callee_saved = CALLEE_SAVED_ARM if target == "arm64" else CALLEE_SAVED_X86
    ret_reg = "x0" if target == "arm64" else "rax"
    sp_name = "sp" if target == "arm64" else "rsp"
    out_names = {lv["name"] for lv in leaves} | set(contract.get("spoils", ()) or ())
    stack_lim = contract.get("stack") or 0
    N = ode.Numbers()
    ran = 0

    for env in generated:
        if not _eval_requires(spec, contract, env):
            continue
        ran += 1
        init_regs = {}
        init_mem = {}
        buf_info = {}  # name -> (addr, byte_len, kind)
        for ci, r in enumerate(callee_saved):
            init_regs[r] = 0x5500000000000000 + ci * 0x10101
        sp_entry = 0x70000000
        init_regs[sp_name] = sp_entry

        base = 0x100000
        step = 0x10400
        for idx, (name, k) in enumerate(kinds):
            reg = arg_regs[idx]
            if k[0] == "number":
                init_regs[reg] = env[name]
            elif k[0] == "bytes":
                addr = base + idx * step
                init_regs[reg] = addr
                bs = env[name]
                for i, b in enumerate(bs):
                    init_mem[addr + i] = b & 0xFF
                buf_info[name] = (addr, len(bs), "bytes")
            elif k[0] == "words":
                addr = base + idx * step
                init_regs[reg] = addr
                ws = env[name]
                for i, w in enumerate(ws):
                    raw = struct.pack("<I", _to_int(w))
                    for j in range(4):
                        init_mem[addr + i * 4 + j] = raw[j]
                buf_info[name] = (addr, len(ws) * 4, "words")

        tr = estimate.trace_memory(programs, symbol, target, init_regs=init_regs, init_mem=init_mem, max_steps=max_steps)

        # 1. Fault or non-termination
        if not tr["returned"] or tr["fault"] is not None:
            return {
                "status": "FALSE", "cases_run": ran, "input": _fmt_env(env, kinds),
                "reason": f"fault or non-termination: {tr['fault']}",
                "expected": "returns cleanly", "actual": str(tr["fault"]),
            }

        # 2. Stack pointer and callee-saved registers
        if tr["final_regs"].get(sp_name) != sp_entry:
            return {
                "status": "FALSE", "cases_run": ran, "input": _fmt_env(env, kinds),
                "reason": f"stack pointer {sp_name} changed on return",
                "expected": hex(sp_entry), "actual": hex(tr["final_regs"].get(sp_name, 0)),
            }
        for r in callee_saved:
            if tr["final_regs"].get(r) != init_regs[r]:
                return {
                    "status": "FALSE", "cases_run": ran, "input": _fmt_env(env, kinds),
                    "reason": f"callee-saved register {r} changed on return",
                    "expected": hex(init_regs[r]), "actual": hex(tr["final_regs"].get(r, 0)),
                }

        # 3. Check return value (`returns EXPR`)
        if contract.get("returns") is not None:
            try:
                want = _to_int(spec.eval(N, contract["returns"], env))
            except Exception as exc:
                return {"status": "skipped", "reason": f"spec eval failed: {exc}", "cases_run": ran}
            got = tr["final_regs"].get(ret_reg, 0)
            if got != want:
                return {
                    "status": "FALSE", "cases_run": ran, "input": _fmt_env(env, kinds),
                    "reason": f"return value in {ret_reg} disagrees with contract",
                    "expected": str(want), "actual": str(got),
                }

        # 4. Check output buffers (`ensures OUT = EXPR`)
        fmem = tr["final_mem"]
        for lv in leaves:
            oname = lv["name"]
            if oname not in buf_info:
                continue
            addr, blen, bkind = buf_info[oname]
            try:
                want_val = spec.eval(N, lv["expr"], env)
            except Exception as exc:
                return {"status": "skipped", "reason": f"spec eval failed: {exc}", "cases_run": ran}
            want_list = _to_int_list(want_val)
            if bkind == "words":
                got_list = [
                    struct.unpack("<I", bytes(fmem.get(addr + i * 4 + j, 0) for j in range(4)))[0]
                    for i in range(blen // 4)
                ]
            else:
                got_list = [fmem.get(addr + i, 0) for i in range(blen)]
            if got_list != want_list:
                # Find first differing index
                diff_i = next(i for i, (g, w) in enumerate(zip(got_list, want_list)) if g != w)
                fmt = (lambda x: f"0x{x:08x}") if bkind == "words" else str
                return {
                    "status": "FALSE", "cases_run": ran, "input": _fmt_env(env, kinds),
                    "reason": f"output `{oname}[{diff_i}]` disagrees with contract",
                    "expected": fmt(want_list[diff_i]), "actual": fmt(got_list[diff_i]),
                }

        # 5. Check no read-only input buffer was overwritten
        for name, (addr, blen, _) in buf_info.items():
            if name in out_names:
                continue
            for i in range(blen):
                if fmem.get(addr + i, 0) != init_mem.get(addr + i, 0):
                    return {
                        "status": "FALSE", "cases_run": ran, "input": _fmt_env(env, kinds),
                        "reason": f"read-only input `{name}` modified at byte +{i}",
                        "expected": str(init_mem.get(addr + i, 0)), "actual": str(fmem.get(addr + i, 0)),
                    }

    return {"status": "not refuted", "cases_run": ran}


def format_refutation(res, symbol):
    if res["status"] == "FALSE":
        return (f"counterexample ({symbol}, FALSE on probe #{res['cases_run']}):\n"
                f"  why:      {res['reason']}\n"
                f"  input:    {res['input']}\n"
                f"  expected: {res['expected']}\n"
                f"  actual:   {res['actual']}")
    if res["status"] == "not refuted":
        return (f"counterexample ({symbol}): none found on {res['cases_run']} concrete probe input(s) "
                f"(code matched contract functionally; check loop place, trace clause, or proof)")
    return f"counterexample ({symbol}): skipped ({res.get('reason', '')})"
