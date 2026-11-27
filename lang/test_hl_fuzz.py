#!/usr/bin/env pypy3
"""Differential compiler fuzzer for High-Level Ode (`lang/ode_hl.py`).

Generates deterministic randomized High-Level Ode programs covering nested
expressions, nested `select(...)` with compound conditions, compound-index
loads/stores (`out[3 * i] := expr`), control flow (`if/else`, `for`, early
`return`), spills/callee-saved pressure, and multi-function calls.

For every generated program and both targets (`x86_64` and `arm64`):
  1. Evaluates the program directly via an independent reference AST evaluator.
  2. Compiles the High-Level Ode source to machine code bytes via `odec.compile_info`.
  3. Executes the compiled machine bytes in `core/conc.py` (`estimate.trace_memory`)
     across multiple concrete inputs.
  4. Asserts bit-exact return value, output buffer bytes, read-only input integrity,
     callee-saved register preservation, and stack-pointer restoration.
"""
import os
import random
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for p in (HERE, os.path.join(ROOT, "advice"), os.path.join(ROOT, "core"), os.path.join(ROOT, "kcheck"), os.path.join(ROOT, "arm64")):
    if p not in sys.path:
        sys.path.insert(0, p)

import estimate
import ode_unified
import odec

M64 = (1 << 64) - 1
ARG_REGS = {
    "x86_64": ["rdi", "rsi", "rdx", "rcx", "r8", "r9"],
    "arm64": ["x0", "x1", "x2", "x3", "x4", "x5"],
}
CALLEE_SAVED = {
    "x86_64": ["rbx", "rbp", "r12", "r13", "r14", "r15"],
    "arm64": ["x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26", "x27", "x28", "x29"],
}
RET_REG = {"x86_64": "rax", "arm64": "x0"}
SP_REG = {"x86_64": "rsp", "arm64": "sp"}


# ---------------------------------------------------------------------------
# Tiny independent expression/statement generator + reference AST evaluator
# ---------------------------------------------------------------------------

def eval_expr(node, env, mem):
    kind = node[0]
    if kind == "num":
        return node[1] & M64
    if kind == "var":
        return env[node[1]] & M64
    if kind == "load":
        _, buf, idx_n = node
        idx = eval_expr(idx_n, env, mem)
        return mem[buf][idx] & 0xFF
    if kind == "bin":
        _, op, l, r = node
        lv = eval_expr(l, env, mem)
        rv = eval_expr(r, env, mem)
        if op in ("+", "+%"):
            return (lv + rv) & M64
        if op in ("-", "-%"):
            return (lv - rv) & M64
        if op == "*":
            return (lv * rv) & M64
        if op == "&":
            return (lv & rv) & M64
        if op == "|":
            return (lv | rv) & M64
        if op == "<<":
            return (lv << (rv & 63)) & M64
        if op == ">>":
            return (lv >> (rv & 63)) & M64
        raise AssertionError(f"unknown op {op}")
    if kind == "cmp":
        _, op, l, r = node
        lv = eval_expr(l, env, mem)
        rv = eval_expr(r, env, mem)
        return {
            "==": lv == rv, "!=": lv != rv,
            "<": lv < rv, "<=": lv <= rv,
            ">": lv > rv, ">=": lv >= rv,
        }[op]
    if kind == "bool":
        _, op, l, r = node
        lv = eval_expr(l, env, mem)
        rv = eval_expr(r, env, mem)
        return (lv and rv) if op == "&&" else (lv or rv)
    if kind == "not":
        return not eval_expr(node[1], env, mem)
    if kind == "select":
        _, c, t, e = node
        return eval_expr(t, env, mem) if eval_expr(c, env, mem) else eval_expr(e, env, mem)
    raise AssertionError(f"unknown node {node}")


def fmt_expr(node):
    kind = node[0]
    if kind == "num":
        return str(node[1])
    if kind == "var":
        return node[1]
    if kind == "load":
        return f"{node[1]}[{fmt_expr(node[2])}]"
    if kind == "bin":
        return f"({fmt_expr(node[2])} {node[1]} {fmt_expr(node[3])})"
    if kind == "cmp":
        return f"({fmt_expr(node[2])} {node[1]} {fmt_expr(node[3])})"
    if kind == "bool":
        return f"({fmt_expr(node[2])} {node[1]} {fmt_expr(node[3])})"
    if kind == "not":
        return f"(!{fmt_expr(node[1])})"
    if kind == "select":
        return f"select({fmt_expr(node[1])}, {fmt_expr(node[2])}, {fmt_expr(node[3])})"
    raise AssertionError(node)


def gen_expr(rng, vars_list, depth, buf_name=None, buf_len=16, allow_select=True):
    """Generate a bounded overflow-safe (or wrapping) nested expression."""
    if depth <= 0:
        choices = [("var", rng.choice(vars_list)), ("num", rng.choice([0, 1, 2, 3, 7, 15, 25, 43, 63, 65, 97, 255]))]
        if buf_name is not None and rng.random() < 0.35:
            idx = rng.choice([
                ("num", rng.randint(0, buf_len - 1)),
                ("bin", "&", ("var", rng.choice(vars_list)), ("num", buf_len - 1)),
            ])
            choices.append(("load", buf_name, idx))
        return rng.choice(choices)

    r = rng.random()
    if allow_select and r < 0.36:
        cond = gen_cond(rng, vars_list, depth - 1, buf_name, buf_len)
        t_e = gen_expr(rng, vars_list, depth - 1, buf_name, buf_len, allow_select=True)
        e_e = gen_expr(rng, vars_list, depth - 1, buf_name, buf_len, allow_select=True)
        return ("select", cond, t_e, e_e)
    if r < 0.50 and buf_name is not None:
        # Compound index load (`buf[(a & 3) * 3 + 1]`, `buf[(a & 7) + (b & 7)]`)
        v1 = rng.choice(vars_list)
        v2 = rng.choice(vars_list)
        idx_kind = rng.choice(["mul3", "add", "plus_k"])
        if idx_kind == "mul3":
            idx = ("bin", "+", ("bin", "*", ("bin", "&", ("var", v1), ("num", 3)), ("num", 3)), ("num", rng.randint(0, 3)))
        elif idx_kind == "add":
            idx = ("bin", "+", ("bin", "&", ("var", v1), ("num", 7)), ("bin", "&", ("var", v2), ("num", 7)))
        else:
            idx = ("bin", "+", ("bin", "&", ("var", v1), ("num", 7)), ("num", rng.randint(1, 7)))
        return ("load", buf_name, idx)
    if r < 0.64:
        # Multiply by constant (including odd factors 3, 5, 7, 9, 10, 12, 256!)
        lhs = gen_expr(rng, vars_list, depth - 1, buf_name, buf_len, allow_select=False)
        lhs_small = ("bin", "&", lhs, ("num", 255))
        k = rng.choice([2, 3, 4, 5, 6, 7, 9, 10, 12, 16, 256])
        return ("bin", "*", lhs_small, ("num", k)) if rng.random() < 0.6 else ("bin", "*", ("num", k), lhs_small)
    if r < 0.78:
        op = rng.choice(["<<", ">>", "&", "|"])
        lhs = gen_expr(rng, vars_list, depth - 1, buf_name, buf_len, allow_select=False)
        if op in ("<<", ">>"):
            lhs = ("bin", "&", lhs, ("num", 65535))
            return ("bin", op, lhs, ("num", rng.choice([1, 2, 3, 4, 8])))
        rhs = gen_expr(rng, vars_list, depth - 1, buf_name, buf_len, allow_select=False)
        return ("bin", op, lhs, rhs)
    # Add/sub (wrapping `+%`/`-%` so arbitrary inputs never rely on non-underflow)
    op = rng.choice(["+%", "-%", "+"])
    lhs = gen_expr(rng, vars_list, depth - 1, buf_name, buf_len, allow_select=False)
    rhs = gen_expr(rng, vars_list, depth - 1, buf_name, buf_len, allow_select=False)
    if op == "+":
        lhs = ("bin", "&", lhs, ("num", 65535))
        rhs = ("bin", "&", rhs, ("num", 65535))
    return ("bin", op, lhs, rhs)


def gen_cond(rng, vars_list, depth, buf_name=None, buf_len=16):
    r = rng.random()
    if depth > 0 and r < 0.25:
        op = rng.choice(["&&", "||"])
        return ("bool", op, gen_cond(rng, vars_list, 0, buf_name, buf_len), gen_cond(rng, vars_list, 0, buf_name, buf_len))
    if r < 0.45:
        # Wrapping range check `(c -% lo) <= span`
        v = rng.choice(vars_list)
        lo = rng.choice([48, 65, 97, 10])
        span = rng.choice([9, 25, 15])
        return ("cmp", "<=", ("bin", "-%", ("var", v), ("num", lo)), ("num", span))
    if r < 0.70:
        # Compound bitmask/expr comparison (`(b & 7) == 0`, `(a + b) < 100`)
        lhs = gen_expr(rng, vars_list, 0, buf_name, buf_len, allow_select=False)
        mask = rng.choice([1, 3, 7, 15, 255])
        return ("cmp", rng.choice(["==", "!=", "<", "<=", ">", ">="]), ("bin", "&", lhs, ("num", mask)), ("num", rng.choice([0, 1, 3, 5, 10])))
    lhs = gen_expr(rng, vars_list, 0, buf_name, buf_len, allow_select=False)
    rhs = gen_expr(rng, vars_list, 0, buf_name, buf_len, allow_select=False)
    return ("cmp", rng.choice(["==", "!=", "<", "<=", ">", ">="]), lhs, rhs)


def compile_progs(src_text, fn_name, target, helper_names=()):
    """Compile `src_text` once for `target` and return decoded `progs` dict for `estimate.trace_memory`."""
    with tempfile.TemporaryDirectory() as td:
        sp = os.path.join(td, "fuzz.ode")
        with open(sp, "w", encoding="utf-8") as f:
            f.write(src_text)
        progs = {}
        for nm in list(helper_names) + [fn_name]:
            op = os.path.join(td, f"{nm}.o")
            odec.build(sp, nm, op, target=target)
            _, progs[nm] = estimate.decode_object(op, nm, target)
        return progs


def exec_progs(progs, src_text, fn_name, target, arg_values, bufs=None):
    """Execute pre-compiled `progs` via `estimate.trace_memory` and check return, buffers, callee-saves, SP."""
    bufs = bufs or {}
    init_regs = {}
    init_mem = {}
    for ci, r in enumerate(CALLEE_SAVED[target]):
        init_regs[r] = 0x4400000000000000 + ci * 0x10101
    sp_entry = 0x70000000
    init_regs[SP_REG[target]] = sp_entry

    buf_addrs = {}
    base = 0x100000
    step = 0x10000
    for idx, (pname, pval) in enumerate(arg_values):
        reg = ARG_REGS[target][idx]
        if pname in bufs:
            addr = base + idx * step
            init_regs[reg] = addr
            buf_addrs[pname] = (addr, len(pval))
            for i, b in enumerate(pval):
                init_mem[addr + i] = b & 0xFF
        else:
            init_regs[reg] = pval & M64

    tr = estimate.trace_memory(progs, fn_name, target, init_regs=init_regs, init_mem=init_mem, max_steps=50000)
    if not tr["returned"] or tr["fault"] is not None:
        raise AssertionError(f"fault/non-return on {target}: {tr['fault']}\n--- SRC ---\n{src_text}")
    fregs = tr["final_regs"]
    fmem = tr["final_mem"]
    for ci, r in enumerate(CALLEE_SAVED[target]):
        want_r = 0x4400000000000000 + ci * 0x10101
        got_r = fregs.get(r, 0)
        if got_r != want_r:
            raise AssertionError(f"callee-saved {r} clobbered on {target}: got {got_r:#x} want {want_r:#x}\n--- SRC ---\n{src_text}")
    if fregs.get(SP_REG[target], 0) != sp_entry:
        raise AssertionError(f"SP mismatch on {target}: {fregs.get(SP_REG[target], 0):#x} != {sp_entry:#x}\n--- SRC ---\n{src_text}")

    out_bufs = {}
    for pname, (addr, blen) in buf_addrs.items():
        out_bufs[pname] = [fmem.get(addr + i, 0) for i in range(blen)]
    return fregs.get(RET_REG[target], 0) & M64, out_bufs


class TestHighLevelOdeFuzz(unittest.TestCase):
    def test_01_random_nested_exprs_and_selects_both_arches(self):
        """60 randomized deeply nested expressions (select, binops, mul-const, loads) match AST on x86_64 & arm64."""
        rng = random.Random(20261127)
        buf_data = [(i * 37 + 13) & 0xFF for i in range(16)]
        test_inputs = [
            (0, 0, 0),
            (65, 97, 48),
            (90, 122, 57),
            (43, 47, 255),
            (13, 250, 7),
        ]
        compiled_counts = {"x86_64": 0, "arm64": 0}
        refused_counts = {"x86_64": 0, "arm64": 0}
        for case_i in range(60):
            buf_first = (case_i % 2 == 0)
            depth = rng.choice([2, 3])
            expr = gen_expr(rng, ["a", "b", "c"], depth, buf_name="buf", buf_len=16, allow_select=True)
            use_inplace = (case_i % 3 == 0)
            if use_inplace:
                upd = gen_expr(rng, ["a", "b", "c", "acc"], 2, buf_name="buf", buf_len=16, allow_select=True)
                body = f"    var acc: u64 := {fmt_expr(expr)}\n    acc := {fmt_expr(upd)}\n    return acc\n"
            else:
                body = f"    return {fmt_expr(expr)}\n"
            if buf_first:
                sig = "fn f(buf: 16 bytes, a: u64, b: u64, c: u64) -> u64"
            else:
                sig = "fn f(a: u64, b: u64, c: u64, buf: 16 bytes) -> u64"
            src = f"{sig}\n    returns 0\n    trace depends on buf, a, b, c\n{{\n{body}}}\n"
            for tgt in ("x86_64", "arm64"):
                try:
                    progs = compile_progs(src, "f", tgt)
                except ode_unified.UnifiedErr as exc:
                    msg = str(exc)
                    self.assertIn("expression needs another temporary register", msg)
                    self.assertIn("currently held scratch registers:", msg)
                    refused_counts[tgt] += 1
                    continue
                compiled_counts[tgt] += 1
                for a, b, c in test_inputs:
                    env = {"a": a, "b": b, "c": c}
                    mem = {"buf": list(buf_data)}
                    v = eval_expr(expr, env, mem)
                    if use_inplace:
                        env["acc"] = v
                        v = eval_expr(upd, env, mem)
                    args = [("buf", buf_data), ("a", a), ("b", b), ("c", c)] if buf_first else [("a", a), ("b", b), ("c", c), ("buf", buf_data)]
                    got, out_b = exec_progs(progs, src, "f", tgt, args, bufs={"buf"})
                    self.assertEqual(
                        got, v,
                        f"case {case_i} ({tgt}) mismatch for a={a},b={b},c={c}: got {got}, want {v}\n{src}",
                    )
                    self.assertEqual(out_b["buf"], buf_data, f"read-only buf modified in case {case_i}")
        self.assertGreaterEqual(compiled_counts["x86_64"], 35, f"too few x86_64 cases compiled: {compiled_counts}")
        self.assertGreaterEqual(compiled_counts["arm64"], 50, f"too few arm64 cases compiled: {compiled_counts}")

    def test_02_random_compound_stores_and_loops_both_arches(self):
        """30 randomized `for` loops writing `out[3 * g + k] := expr` and `out[4 * g + k] := expr` on both arches."""
        rng = random.Random(20261128)
        inp_data = [(i * 53 + 7) & 0xFF for i in range(32)]
        compiled_counts = {"x86_64": 0, "arm64": 0}
        for case_i in range(30):
            stride = rng.choice([3, 4, 5])
            iters = 4
            out_len = stride * iters
            stmts = []
            exprs = []
            for k in range(stride):
                e = gen_expr(rng, ["g", "acc", "k0"], 2, buf_name="inp", buf_len=32, allow_select=True)
                exprs.append((k, e))
                idx_s = f"{stride} * g" if k == 0 else f"{stride} * g + {k}"
                stmts.append(f"        out[{idx_s}] := ({fmt_expr(e)}) & 255")
            body_s = "\n".join(stmts)
            src = (
                f"fn pack_f(out: {out_len} bytes, inp: 32 bytes, k0: u64) -> u64\n"
                f"    requires no_overlap(out, inp)\n"
                f"    returns 0\n"
                f"    trace depends on out, inp, k0\n"
                f"{{\n"
                f"    var acc: u64 := k0\n"
                f"    for g in 0..{iters}\n"
                f"    {{\n"
                f"{body_s}\n"
                f"        acc +%= inp[4 * g] + g\n"
                f"    }}\n"
                f"    return acc\n"
                f"}}\n"
            )
            for tgt in ("x86_64", "arm64"):
                try:
                    progs = compile_progs(src, "pack_f", tgt)
                except ode_unified.UnifiedErr as exc:
                    msg = str(exc)
                    self.assertIn("expression needs another temporary register", msg)
                    self.assertIn("currently held scratch registers:", msg)
                    continue
                compiled_counts[tgt] += 1
                for k0 in (0, 17, 251):
                    want_out = [0xAA] * out_len
                    acc = k0 & M64
                    mem = {"inp": list(inp_data)}
                    for g in range(iters):
                        env = {"g": g, "acc": acc, "k0": k0}
                        for k, e in exprs:
                            want_out[stride * g + k] = eval_expr(e, env, mem) & 0xFF
                        acc = (acc + inp_data[4 * g] + g) & M64
                    got_ret, out_b = exec_progs(
                        progs, src, "pack_f", tgt, [("out", [0xAA] * out_len), ("inp", inp_data), ("k0", k0)],
                        bufs={"out", "inp"},
                    )
                    self.assertEqual(got_ret, acc, f"store case {case_i} ({tgt}) ret mismatch\n{src}")
                    self.assertEqual(out_b["out"], want_out, f"store case {case_i} ({tgt}) out mismatch\n{src}")
                    self.assertEqual(out_b["inp"], inp_data)
        self.assertGreaterEqual(compiled_counts["x86_64"], 15, f"too few x86_64 store cases compiled: {compiled_counts}")
        self.assertGreaterEqual(compiled_counts["arm64"], 25, f"too few arm64 store cases compiled: {compiled_counts}")

    def test_03_control_flow_spills_and_arg_swapping_calls_both_arches(self):
        """High register pressure (14 live locals), `if/else` returns, and arg-swapping calls on both arches."""
        rng = random.Random(20261129)
        for case_i in range(20):
            n_vars = rng.randint(10, 15)
            lines = []
            for vi in range(n_vars):
                k = rng.randint(1, 255)
                src_v = rng.choice(["a", "b", "c"])
                lines.append(f"    let t{vi}: u64 := ({src_v} +% {k}) & 1023")
            sum_expr = " +% ".join(f"t{vi}" for vi in range(n_vars))
            if case_i % 2 == 0:
                tail = f"    if (a & 1) == 0 {{\n        return {sum_expr}\n    }} else {{\n        return ({sum_expr}) +% b\n    }}\n"
            else:
                tail = f"    return helper(b, a, ({sum_expr}) & 65535, c +% 1)\n"
            src = (
                "fn helper(x: u64, y: u64, z: u64, w: u64) -> u64\n"
                "    returns 0\n"
                "    trace depends on x, y, z, w\n"
                "{\n"
                "    return (x * 3) +% (y * 5) +% z +% (w << 2)\n"
                "}\n\n"
                "fn top(a: u64, b: u64, c: u64) -> u64\n"
                "    returns 0\n"
                "    trace depends on a, b, c\n"
                "{\n" + "\n".join(lines) + "\n" + tail + "}\n"
            )
            ks = [int(ln.split("+% ")[1].split(")")[0]) for ln in lines]
            vs = [ln.split(":= (")[1].split(" +%")[0] for ln in lines]
            for tgt in ("x86_64", "arm64"):
                progs = compile_progs(src, "top", tgt, helper_names=("helper",) if case_i % 2 == 1 else ())
                for a, b, c in [(0, 10, 20), (1, 77, 99), (42, 123, 255)]:
                    env = {"a": a, "b": b, "c": c}
                    s = sum((env[v] + k) & 1023 for v, k in zip(vs, ks)) & M64
                    if case_i % 2 == 0:
                        want = s if (a & 1) == 0 else ((s + b) & M64)
                    else:
                        x, y, z, w = b, a, s & 65535, (c + 1) & M64
                        want = ((x * 3) + (y * 5) + z + (w << 2)) & M64
                    got, _ = exec_progs(progs, src, "top", tgt, [("a", a), ("b", b), ("c", c)])
                    self.assertEqual(got, want, f"pressure/call case {case_i} ({tgt}) mismatch: got {got} want {want}\n{src}")

    def test_04_interactive_no_spill_and_scratch_diagnostics(self):
        """ODE_HL_NO_SPILL=1 prints full live-variable register table; deep scratch exhaustion prints held temps."""
        lines = [f"    let t{i}: u64 := (a +% {i + 1}) & 255" for i in range(22)]
        s = " +% ".join(f"t{i}" for i in range(22))
        spill_src = (
            "fn many(a: u64, b: u64) -> u64\n"
            "    returns 0\n"
            "    trace depends on a, b\n"
            "{\n" + "\n".join(lines) + f"\n    return ({s}) +% b\n}}\n"
        )
        old_env = os.environ.get("ODE_HL_NO_SPILL")
        try:
            os.environ["ODE_HL_NO_SPILL"] = "1"
            for tgt in ("x86_64", "arm64"):
                with self.assertRaises(ode_unified.UnifiedErr) as cm:
                    compile_progs(spill_src, "many", tgt)
                msg = str(cm.exception)
                self.assertIn("silent stack spilling is disabled", msg)
                self.assertIn("simultaneously live variables:", msg)
                self.assertIn("how to fix:", msg)
        finally:
            if old_env is None:
                os.environ.pop("ODE_HL_NO_SPILL", None)
            else:
                os.environ["ODE_HL_NO_SPILL"] = old_env

        deep_src = (
            "fn deep(buf: 16 bytes, a: u64, b: u64, c: u64) -> u64\n"
            "    returns 0\n"
            "    trace depends on buf, a, b, c\n"
            "{\n"
            "    return buf[(a & 3) * 3] | (buf[(b & 7) + (c & 7)] +% buf[(a & 7) + (c & 7)])\n"
            "}\n"
        )
        with self.assertRaises(ode_unified.UnifiedErr) as cm:
            compile_progs(deep_src, "deep", "x86_64")
        msg = str(cm.exception)
        self.assertIn("expression needs another temporary register on x86_64", msg)
        self.assertIn("currently held scratch registers:", msg)
        self.assertIn("unused named scalar registers in fn `deep`:", msg)

        split_src = (
            "fn deep(buf: 16 bytes, a: u64, b: u64, c: u64) -> u64\n"
            "    returns 0\n"
            "    trace depends on buf, a, b, c\n"
            "{\n"
            "    let rhs: u64 := buf[(b & 7) + (c & 7)] +% buf[(a & 7) + (c & 7)]\n"
            "    return buf[(a & 3) * 3] | rhs\n"
            "}\n"
        )
        buf_data = [(i * 37 + 13) & 0xFF for i in range(16)]
        for tgt in ("x86_64", "arm64"):
            progs = compile_progs(split_src, "deep", tgt)
            got, _ = exec_progs(progs, split_src, "deep", tgt, [("buf", buf_data), ("a", 5), ("b", 3), ("c", 4)], bufs={"buf"})
            want = buf_data[(5 & 3) * 3] | ((buf_data[(3 & 7) + (4 & 7)] + buf_data[(5 & 7) + (4 & 7)]) & M64)
            self.assertEqual(got, want)


if __name__ == "__main__":
    unittest.main()
