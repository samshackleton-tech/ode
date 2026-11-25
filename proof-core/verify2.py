#!/usr/bin/env python3
"""Independent second verifier for Ode `.statement` + `.proof` files (core scalar/byte/loop/call fragment).

Written from scratch in pure Python with ZERO code shared with Lean's `Core.lean`, `Machine.lean`,
`Contract.lean`, or `kcheck/`. Reads only the instruction tables (`core/x86.tab`, `arm64/arm64.tab`
via `core/table.py`), a `.statement` file, and a `.proof` file, and prints `shown` or `refused: ...`.

Covers the core fragment (both x86-64 and AArch64):
  - Table-driven symbolic execution of integer, load/store (`mem8`/`mem64`), compare, branch, call,
    and return instructions.
  - Linear-inequality Farkas/Gomory refutation certificates (`p ...; s i a j b d; q`).
  - Loop invariants (`place PC`, `name`, `fact`, `keep`, `decreases`, `marked`).
  - Pure specification `def` unfolding (`t open K`) and case splitting (`t live`/`t dead`/`t eq`/`t lt`/`t gt`).
  - Multi-function call verification by contract (stack budget, callee-saved registers, return value).
  - Trace-mark enforcement (refuses branches and memory addresses that depend on unmarked inputs).

    python3 proof-core/verify2.py TABLE STATEMENT PROOF
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
CORE = os.path.join(ROOT, "core")
if CORE not in sys.path:
    sys.path.insert(0, CORE)

import table as tab_mod

M64 = (1 << 64) - 1
M32 = (1 << 32) - 1

X86_REGS = ["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi",
            "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"]
X86_ARGS = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"]
X86_CALLEE_SAVED = ["rbx", "rbp", "r12", "r13", "r14", "r15"]

# (the numbering of the proof format: the stack pointer has the number x86-64's has, 4, and x4 the last;
# a proof names an unknown by its register's number, so a program that keeps a changing value in x4 or
# speaks of sp in a row needs this order)
ARM_REGS = ["x0", "x1", "x2", "x3", "sp"] + [f"x{i}" for i in range(5, 31)] + ["x4"]
ARM_ARGS = [f"x{i}" for i in range(8)]
ARM_CALLEE_SAVED = [f"x{i}" for i in range(19, 30)]


class Refuse(Exception):
    pass


# ---------------------------------------------------------------------------
# Linear rows (`c_0 * v_0 + ... + const >= 0`) and Farkas/Gomory refutation
# ---------------------------------------------------------------------------

def r_const(k):
    return (int(k), ())


def r_var(idx):
    return (0, tuple(1 if i == idx else 0 for i in range(idx + 1)))


def _trim(cs):
    n = len(cs)
    while n > 0 and cs[n - 1] == 0:
        n -= 1
    return cs[:n]


def r_add(a, b):
    ca, va = a
    cb, vb = b
    n = max(len(va), len(vb))
    out = tuple((va[i] if i < len(va) else 0) + (vb[i] if i < len(vb) else 0) for i in range(n))
    return (ca + cb, _trim(out))


def r_scale(k, a):
    if k == 0:
        return (0, ())
    ca, va = a
    return (k * ca, tuple(k * c for c in va))


def r_sub(a, b):
    return r_add(a, r_scale(-1, b))


def r_neg(g):
    # `-(g) - 1 >= 0` means `g < 0`
    return r_sub(r_const(-1), g)


def r_plain(facts, g):
    cg, vg = g
    if not vg:
        return cg >= 0
    for cf, vf in facts:
        if cf <= cg and vf == vg:
            return True
    return False


def r_refutes(given, starts, steps):
    """Independent checker of the Farkas/Gomory arithmetic refutation rule (indexed starts)."""
    rows = []
    for idx in starts:
        if idx < 0 or idx >= len(given):
            return False
        rows.append(given[idx])
    return _run_refute_steps(rows, steps)


def r_refutes_rows(given, start_rows, steps):
    """Independent checker of the Farkas/Gomory arithmetic refutation rule (explicit rows,
    completely independent of the verifier's internal fact-list order)."""
    given_set = set(given)
    rows = []
    for row in start_rows:
        if row not in given_set:
            return False
        rows.append(row)
    return _run_refute_steps(rows, steps)


def _run_refute_steps(rows, steps):
    for i, a, j, b, d in steps:
        if a <= 0 or b <= 0 or d <= 0:
            return False
        if i >= len(rows) or j >= len(rows):
            return False
        c_sum, v_sum = r_add(r_scale(a, rows[i]), r_scale(b, rows[j]))
        if any(c % d != 0 for c in v_sum):
            return False
        rows.append((c_sum // d, _trim(tuple(c // d for c in v_sum))))
    if not rows:
        return False
    last_c, last_v = rows[-1]
    return (not last_v) and last_c < 0


# ---------------------------------------------------------------------------
# S-expression parser for `.statement` and `.proof`
# ---------------------------------------------------------------------------

def parse_sexpr(text):
    toks = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c.isspace():
            i += 1
        elif c in "()":
            toks.append(c)
            i += 1
        else:
            j = i
            while j < n and not text[j].isspace() and text[j] not in "()":
                j += 1
            toks.append(text[i:j])
            i = j

    pos = [0]

    def read():
        if pos[0] >= len(toks):
            raise Refuse("unexpected end of s-expression")
        t = toks[pos[0]]
        pos[0] += 1
        if t == "(":
            items = []
            while pos[0] < len(toks) and toks[pos[0]] != ")":
                items.append(read())
            if pos[0] >= len(toks):
                raise Refuse("missing `)` in s-expression")
            pos[0] += 1
            return tuple(items)
        return t

    e = read()
    if pos[0] != len(toks):
        raise Refuse(f"trailing tokens in s-expression: {toks[pos[0]:]}")
    return e


def parse_statement(path):
    fns = []
    cur = None
    defs = {}
    with open(path, "r", encoding="utf-8") as f:
        for raw in f:
            line = raw.strip()
            if not line:
                continue
            parts = line.split()
            kw = parts[0]
            if kw == "fn":
                cur = {
                    "name": parts[1],
                    "machine": "x86-64",
                    "instrs": {},
                    "args": [],
                    "requires": [],
                    "below": [],
                    "atleast": [],
                    "linpre": [],
                    "returns": None,
                    "stack": 0,
                    "hidden": set(),
                    "argregs": None,
                    "keeps": None,
                    "retreg": None,
                    "keeps_vec": None,
                }
                fns.append(cur)
            elif kw == "machine":
                cur["machine"] = parts[1]
            elif kw == "i":
                pc, nxt = int(parts[1]), int(parts[2])
                cur["instrs"][pc] = (nxt, " ".join(parts[3:]))
            elif kw == "arg":
                if len(parts) == 3 and parts[2] == "number":
                    cur["args"].append((parts[1], "number", None))
                elif len(parts) == 4 and parts[2] == "bytes":
                    cur["args"].append((parts[1], "bytes", parts[3]))
                else:
                    raise Refuse(f"unsupported arg form in verify2: {line}")
            elif kw == "requires":
                cur["requires"].append(parse_sexpr(line[len("requires "):]))
            elif kw == "below":
                cur["below"].append((parts[1], int(parts[2])))
            elif kw == "atleast":
                cur["atleast"].append((parts[1], int(parts[2])))
            elif kw == "linpre":
                # `linpre K a1 c1 a2 c2 ...`: the entry condition 0 <= K + c1*a1 + c2*a2 + ...
                if len(parts) % 2 != 0:
                    raise Refuse(f"malformed linpre line in verify2: {line}")
                cur["linpre"].append((int(parts[1]), [(parts[i], int(parts[i + 1])) for i in range(2, len(parts), 2)]))
            elif kw == "returns":
                cur["returns"] = parse_sexpr(line[len("returns "):])
            elif kw == "stack":
                cur["stack"] = int(parts[1])
            elif kw == "hidden":
                cur["hidden"].update(parts[1:])
            elif kw == "argregs":
                cur["argregs"] = parts[1:]
            elif kw == "keeps":
                cur["keeps"] = parts[1:]
            elif kw == "retreg":
                cur["retreg"] = parts[1]
            elif kw == "keeps_vec":
                cur["keeps_vec"] = parts[1:]
            elif kw == "def":
                eq = line.index(" = ")
                hdr = line[:eq].split()
                defs[hdr[1]] = (hdr[2:], parse_sexpr(line[eq + 3:]))
            else:
                raise Refuse(f"unsupported statement line in verify2: {line}")
    return fns, defs


def parse_proof(path):
    proofs = {}
    cur = None
    cur_place = None
    cur_p = None
    with open(path, "r", encoding="utf-8") as f:
        for raw in f:
            line = raw.strip()
            if not line:
                continue
            parts = line.split()
            kw = parts[0]
            if kw == "for":
                cur = {"places": {}, "items": []}
                proofs[parts[1]] = cur
                cur_place = None
            elif kw in ("place", "join"):
                pc = int(parts[1])
                cur_place = {"pc": pc, "names": [], "facts": [], "keep": set(), "marked": set(), "decreases": None, "is_join": (kw == "join")}
                cur["places"][pc] = cur_place
            elif kw == "name" and cur_place is not None:
                cur_place["names"].append((parts[1], parts[2]))
            elif kw == "fact" and cur_place is not None:
                cur_place["facts"].append(parse_sexpr(line[len("fact "):]))
            elif kw == "keep" and cur_place is not None:
                cur_place["keep"].update(parts[1:])
            elif kw == "marked" and cur_place is not None:
                cur_place["marked"].update(parts[1:])
            elif kw == "decreases" and cur_place is not None:
                cur_place["decreases"] = parse_sexpr(line[len("decreases "):])
            elif kw == "t":
                cur_place = None
                tag = parts[1]
                arg = int(parts[2]) if len(parts) > 2 else 0
                cur["items"].append(("t", tag, arg))
            elif kw == "p":
                cur_place = None
                cur_p = ("p", [int(x) for x in parts[1:]], [])
            elif kw == "r":
                cur_place = None
                nums = [int(x) for x in parts[1:]]
                row = (nums[0], _trim(tuple(nums[1:])))
                if cur_p is None:
                    cur_p = ("r", [row], [])
                elif cur_p[0] == "r":
                    cur_p[1].append(row)
                else:
                    raise Refuse(f"mixed `p` and `r` in one arithmetic proof: {line}")
            elif kw == "s":
                if cur_p is None or len(parts) != 6:
                    raise Refuse(f"malformed arithmetic step: {line}")
                cur_p[2].append(tuple(int(x) for x in parts[1:]))
            elif kw == "q":
                if cur_p is None:
                    raise Refuse("unexpected `q` without `p`/`r`")
                cur["items"].append(cur_p)
                cur_p = None
            else:
                raise Refuse(f"unsupported proof line in verify2: {line}")
    return proofs


# ---------------------------------------------------------------------------
# Proof item stream & symbolic verifier state
# ---------------------------------------------------------------------------

class Stream:
    def __init__(self, items):
        self.items = items
        self.pos = 0

    def pop(self):
        if self.pos >= len(self.items):
            raise Refuse("proof ended early")
        it = self.items[self.pos]
        self.pos += 1
        return it

    def pop_tag(self, expected=None):
        it = self.pop()
        if it[0] != "t":
            raise Refuse(f"expected tag `{expected or 'any'}`, got {it[0]}")
        if expected is not None and it[1] != expected:
            raise Refuse(f"expected tag `{expected}`, got `{it[1]}`")
        return it[1], it[2]


class Verifier:
    def __init__(self, rows, defs, proven_contracts):
        self.rows = rows
        self.heads = tab_mod.by_head(rows)
        self.defs = defs
        self.proven = proven_contracts

    def entail(self, facts, g, stream):
        if r_plain(facts, g):
            return
        it = stream.pop()
        given = [r_neg(g)] + facts
        if it[0] == "p":
            if not r_refutes(given, it[1], it[2]):
                raise Refuse("arithmetic proof does not refute negated goal")
        elif it[0] == "r":
            if not r_refutes_rows(given, it[1], it[2]):
                raise Refuse("explicit-row arithmetic proof does not refute negated goal")
        else:
            raise Refuse(f"expected arithmetic proof `p`/`r`, got {it}")

    def refute_dead(self, facts, stream):
        it = stream.pop()
        if it[0] == "p":
            if not r_refutes(facts, it[1], it[2]):
                raise Refuse("arithmetic proof does not refute dead branch")
        elif it[0] == "r":
            if not r_refutes_rows(facts, it[1], it[2]):
                raise Refuse("explicit-row arithmetic proof does not refute dead branch")
        else:
            raise Refuse(f"expected arithmetic proof `p`/`r` after `dead`, got {it}")

    def entail_eq(self, facts, a, b, stream):
        self.entail(facts, r_sub(a, b), stream)
        self.entail(facts, r_sub(b, a), stream)

    def linpre_row(self, k, terms, env):
        row = r_const(k)
        for anm, coeff in terms:
            v = env.get(anm)
            if not self.is_row(v):
                raise Refuse(f"linear entry condition names `{anm}`, which is no number here")
            row = r_add(row, r_scale(coeff, v))
        return row

    def is_row(self, v):
        return isinstance(v, tuple) and len(v) == 2 and isinstance(v[0], int) and isinstance(v[1], tuple)

    def held_values(self, state):
        out = []
        for a, b in state["eqs"]:
            if isinstance(a, tuple) and len(a) == 3 and a[0] == "call" and self.is_row(b):
                out.append((a, b))
            elif isinstance(b, tuple) and len(b) == 3 and b[0] == "call" and self.is_row(a):
                out.append((b, a))
        return out

    def same_call(self, c1, c2, state, stream):
        if c1[1] != c2[1] or len(c1[2]) != len(c2[2]):
            raise Refuse(f"mismatched call `{c1[1]}` vs `{c2[1]}`")
        for a1, a2 in zip(c1[2], c2[2]):
            if a1 == a2:
                continue
            if self.is_row(a1) and self.is_row(a2):
                self.entail_eq(state["facts"], a1, a2, stream)
            else:
                raise Refuse(f"mismatched non-scalar call arg `{a1}` vs `{a2}`")

    def as_num(self, v, env, state, stream):
        if self.is_row(v):
            return v
        if isinstance(v, tuple) and len(v) == 3 and v[0] == "call":
            for c0, r0 in self.held_values(state):
                if c0 == v:
                    return r0
            if stream is None:
                raise Refuse(f"expected scalar number, got `{v}`")
            tag, idx = stream.pop_tag()
            if tag == "held":
                hv = self.held_values(state)
                if idx >= len(hv):
                    raise Refuse(f"`t held {idx}` out of range for {len(hv)} held value(s)")
                c0, r0 = hv[idx]
                self.same_call(v, c0, state, stream)
                return r0
            if tag == "open":
                _, fn_nm, args = v
                params, body = self.defs[fn_nm]
                val = self.eval_sexpr(body, dict(zip(params, args)), state, stream)
                res = self.as_num(val, env, state, stream)
                state["eqs"].insert(0, (v, res))
                return res
            raise Refuse(f"expected `held` or `open` for `{v}`, got `{tag}`")
        raise Refuse(f"expected scalar number, got `{v}`")

    def eval_sexpr(self, e, env, state, stream):
        """Evaluate a spec S-expression to a linear Row, buffer tag, or symbolic call."""
        op = e[0]
        if op == "num":
            return r_const(int(e[1]))
        if op == "name":
            nm = e[1]
            if nm in env:
                return env[nm]
            raise Refuse(f"unknown spec name `{nm}`")
        if op == "bin":
            bop, l, r = e[1], e[2], e[3]
            lv = self.as_num(self.eval_sexpr(l, env, state, stream), env, state, stream)
            rv = self.as_num(self.eval_sexpr(r, env, state, stream), env, state, stream)
            if bop == "+":
                return r_add(lv, rv)
            if bop == "-":
                res = r_sub(lv, rv)
                if stream is not None:
                    self.entail(state["facts"], res, stream)
                return res
            if bop == "*":
                if not lv[1]:
                    return r_scale(lv[0], rv)
                if not rv[1]:
                    return r_scale(rv[0], lv)
                raise Refuse(f"nonlinear multiply in spec: {e}")
            if bop in ("%", "/"):
                if rv[1] or rv[0] <= 0:
                    raise Refuse(f"unsupported divisor in `{bop}`: {rv}")
                q, rem = state["quot_rem"](lv, rv[0], state)
                return rem if bop == "%" else q
            raise Refuse(f"unsupported binary spec op `{bop}`")
        if op == "call":
            fn_nm = e[1]
            raw_args = [self.eval_sexpr(a, env, state, stream) for a in e[2:]]
            args = []
            for a in raw_args:
                if isinstance(a, tuple) and len(a) == 3 and a[0] == "call":
                    args.append(self.as_num(a, env, state, stream))
                else:
                    args.append(a)
            if fn_nm == "len":
                if len(args) == 1 and isinstance(args[0], tuple) and len(args[0]) == 2 and args[0][0] == "buf":
                    return state["buf_len"][args[0][1]]
                if len(e) == 3 and e[2][0] == "name" and e[2][1] in state["buf_len"]:
                    return state["buf_len"][e[2][1]]
                raise Refuse(f"cannot take `len` of {e[2]}")
            return ("call", fn_nm, tuple(args))
        if op == "index":
            # `a[idx]` -> symbolic byte at `(a, idx)`
            bv = self.eval_sexpr(e[1], env, state, stream)
            if isinstance(bv, tuple) and len(bv) == 2 and bv[0] == "buf":
                buf = bv[1]
            elif e[1][0] == "name" and e[1][1] in state["buf_base"]:
                buf = e[1][1]
            else:
                raise Refuse(f"index on non-buffer {e[1]}")
            idx = self.as_num(self.eval_sexpr(e[2], env, state, stream), env, state, stream)
            if stream is not None:
                self.entail(state["facts"], idx, stream)
                self.entail(state["facts"], r_sub(r_sub(state["buf_len"][buf], idx), r_const(1)), stream)
            return state["get_byte"](buf, idx, state)
        if op == "ifx":
            cond, thn, els = e[1], e[2], e[3]
            if cond[0] != "bin":
                raise Refuse(f"unsupported ifx condition {cond}")
            cop, cl, cr = cond[1], cond[2], cond[3]
            lv = self.as_num(self.eval_sexpr(cl, env, state, stream), env, state, stream)
            rv = self.as_num(self.eval_sexpr(cr, env, state, stream), env, state, stream)
            facts = state["facts"]
            diff = r_sub(lv, rv)
            if cop in ("==", "!=") and (diff in state["neq"] or r_sub(rv, lv) in state["neq"]):
                taken = (cop == "!=")
                return self.eval_sexpr(thn if taken else els, env, state, stream)
            if not diff[1]:
                k = diff[0]
                if cop == "==": taken = (k == 0)
                elif cop == "!=": taken = (k != 0)
                elif cop == "<": taken = (k < 0)
                elif cop == "<=": taken = (k <= 0)
                elif cop == ">": taken = (k > 0)
                elif cop == ">=": taken = (k >= 0)
                else: raise Refuse(f"unsupported ifx op `{cop}`")
                return self.eval_sexpr(thn if taken else els, env, state, stream)
            tag, _ = stream.pop_tag()
            if cop in ("<", ">="):
                if tag == "lt":
                    self.entail(facts, r_sub(r_sub(rv, lv), r_const(1)), stream)
                    taken = (cop == "<")
                elif tag == "ge":
                    self.entail(facts, r_sub(lv, rv), stream)
                    taken = (cop == ">=")
                else:
                    raise Refuse(f"expected `lt`/`ge` for `{cop}`, got `{tag}`")
            elif cop in (">", "<="):
                if tag == "lt":
                    self.entail(facts, r_sub(r_sub(lv, rv), r_const(1)), stream)
                    taken = (cop == ">")
                elif tag == "ge":
                    self.entail(facts, r_sub(rv, lv), stream)
                    taken = (cop == "<=")
                else:
                    raise Refuse(f"expected `lt`/`ge` for `{cop}`, got `{tag}`")
            else:
                if tag == "eq":
                    self.entail_eq(facts, lv, rv, stream)
                    taken = (cop == "==")
                elif tag == "lt":
                    self.entail(facts, r_sub(r_sub(rv, lv), r_const(1)), stream)
                    taken = (cop == "!=")
                elif tag == "gt":
                    self.entail(facts, r_sub(r_sub(lv, rv), r_const(1)), stream)
                    taken = (cop == "!=")
                else:
                    raise Refuse(f"expected `eq`/`lt`/`gt` for `{cop}`, got `{tag}`")
            return self.eval_sexpr(thn if taken else els, env, state, stream)
        raise Refuse(f"unsupported spec expr {e}")

    def expand_eq(self, lhs, rhs, env, state, stream):
        """Unfold `def` calls as directed by `t open K`, closing over held equalities in `state['eqs']`."""
        eqs = state["eqs"]

        def equiv_rows(v):
            """All values reachable from `v` through `eqs`."""
            seen = [v]
            i = 0
            while i < len(seen):
                cur = seen[i]
                i += 1
                for a, b in eqs:
                    if cur == a and b not in seen:
                        seen.append(b)
                    elif cur == b and a not in seen:
                        seen.append(a)
            return seen

        def is_row(v):
            return isinstance(v, tuple) and len(v) == 2 and isinstance(v[0], int) and isinstance(v[1], tuple)

        def calls_in(v, out):
            if isinstance(v, tuple) and len(v) == 3 and v[0] == "call":
                if v not in out:
                    out.append(v)

        for _ in range(64):
            l_eq = equiv_rows(lhs)
            r_eq = equiv_rows(rhs)
            if any(x in r_eq for x in l_eq):
                state["eqs"] = eqs
                return
            if is_row(lhs) and is_row(rhs):
                self.entail_eq(state["facts"], lhs, rhs, stream)
                state["eqs"] = eqs
                return
            nxt_item = stream.items[stream.pos] if stream.pos < len(stream.items) else None
            if nxt_item is None or nxt_item[0] != "t" or nxt_item[1] not in ("open", "carry"):
                l_rows = [x for x in l_eq if is_row(x)]
                r_rows = [x for x in r_eq if is_row(x)]
                if l_rows and r_rows:
                    for lr in l_rows:
                        for rr in r_rows:
                            if r_plain(state["facts"], r_sub(lr, rr)) and r_plain(state["facts"], r_sub(rr, lr)):
                                state["eqs"] = eqs
                                return
                    self.entail_eq(state["facts"], l_rows[0], r_rows[0], stream)
                    state["eqs"] = eqs
                    return
            calls = []
            for a, b in reversed(eqs):
                calls_in(a, calls)
                calls_in(b, calls)
            calls_in(lhs, calls)
            calls_in(rhs, calls)
            tag, idx = stream.pop_tag()
            if tag == "carry":
                hv = self.held_values({"eqs": eqs})
                if idx >= len(hv):
                    raise Refuse(f"`t carry {idx}` out of range for {len(hv)} held value(s)")
                c0, r0 = hv[idx]
                goal_call = rhs if (isinstance(rhs, tuple) and len(rhs) == 3 and rhs[0] == "call") else (
                    lhs if (isinstance(lhs, tuple) and len(lhs) == 3 and lhs[0] == "call") else None
                )
                goal_val = lhs if goal_call == rhs else rhs
                if goal_call is None or not is_row(goal_val):
                    raise Refuse("`t carry` requires one call and one scalar value")
                self.same_call(goal_call, c0, state, stream)
                self.entail_eq(state["facts"], goal_val, r0, stream)
                state["eqs"] = eqs
                return
            if tag != "open":
                raise Refuse(f"expected `open` or `carry`, got `{tag}`")
            if not calls:
                raise Refuse("cannot prove spec equality: no call to open")
            if idx >= len(calls):
                raise Refuse(f"`t open {idx}` out of range for {len(calls)} call(s)")
            c = calls[idx]
            _, fn_nm, args = c
            params, body = self.defs[fn_nm]
            val = self.eval_sexpr(body, dict(zip(params, args)), state, stream)
            eqs.insert(0, (c, val))
        raise Refuse("spec equality exceeded open limit")

    def check_fact(self, fact, env, state, stream):
        if fact[0] != "bin":
            raise Refuse(f"unsupported fact {fact}")
        op, l, r = fact[1], fact[2], fact[3]
        lv = self.eval_sexpr(l, env, state, stream)
        rv = self.eval_sexpr(r, env, state, stream)
        if op == "==":
            self.expand_eq(lv, rv, env, state, stream)
        elif op == "<=":
            self.entail(state["facts"], r_sub(rv, lv), stream)
        elif op == "<":
            self.entail(state["facts"], r_sub(r_sub(rv, lv), r_const(1)), stream)
        elif op == ">=":
            self.entail(state["facts"], r_sub(lv, rv), stream)
        elif op == ">":
            self.entail(state["facts"], r_sub(r_sub(lv, rv), r_const(1)), stream)
        else:
            raise Refuse(f"unsupported fact op `{op}`")

    def assume_fact(self, fact, env, state):
        if fact[0] != "bin":
            raise Refuse(f"unsupported assumed fact {fact}")
        op, l, r = fact[1], fact[2], fact[3]
        if op == "==" and (l[0] == "call" or r[0] == "call"):
            # Record symbolic call equality `lhs == rhs` for later substitution
            lv = self.eval_sexpr(l, env, state, None)
            rv = self.eval_sexpr(r, env, state, None)
            state["eqs"].insert(0, (lv, rv))
            return
        lv = self.eval_sexpr(l, env, state, None)
        rv = self.eval_sexpr(r, env, state, None)
        if op == "<=":
            state["facts"].append(r_sub(rv, lv))
        elif op == "<":
            state["facts"].append(r_sub(r_sub(rv, lv), r_const(1)))
        elif op == ">=":
            state["facts"].append(r_sub(lv, rv))
        elif op == ">":
            state["facts"].append(r_sub(r_sub(lv, rv), r_const(1)))
        elif op == "==":
            state["facts"].append(r_sub(lv, rv))
            state["facts"].append(r_sub(rv, lv))

    def verify_fn(self, fn, proof):
        is_arm = fn["machine"] == "arm64"
        reg_names = ARM_REGS if is_arm else X86_REGS
        arg_regs = fn["argregs"] if fn["argregs"] is not None else (ARM_ARGS if is_arm else X86_ARGS)
        callee_saved = set(fn["keeps"]) if fn["keeps"] is not None else (ARM_CALLEE_SAVED if is_arm else X86_CALLEE_SAVED)
        sp_reg = "sp" if is_arm else "rsp"
        ret_reg = fn["retreg"] if fn["retreg"] is not None else ("x0" if is_arm else "rax")

        init_nvars = 0

        def init_fresh_var(lo=0, hi=M64, target_facts=None):
            nonlocal init_nvars
            idx = init_nvars
            init_nvars += 1
            v = r_var(idx)
            if target_facts is not None:
                target_facts.append(r_sub(v, r_const(lo)))
                target_facts.append(r_sub(r_const(hi), v))
            return v

        def fresh_var(st, lo=0, hi=M64, target_facts=None):
            idx = st["nvars"]
            st["nvars"] += 1
            v = r_var(idx)
            f = st["facts"] if target_facts is None else target_facts
            f.append(r_sub(v, r_const(lo)))
            f.append(r_sub(r_const(hi), v))
            return v

        facts = []
        regs = {}
        entry_regs = {}
        for r in reg_names:
            v = init_fresh_var(0, M64, facts)
            regs[r] = v
            entry_regs[r] = v
        facts.append(r_sub(regs[sp_reg], r_const(fn["stack"])))
        if not is_arm:
            facts.append(r_sub(r_const(M64 - 8), regs[sp_reg]))
        # Reserve one slot after registers (dataVar, matching Core.lean Sym.init)
        init_fresh_var(0, M64, facts)

        # Trace marks: True = marked (kept out of trace), False = clean (may show in trace)
        marks = {r: True for r in reg_names}
        marks[sp_reg] = False
        if is_arm:
            marks["x30"] = False

        env = {}
        buf_base = {}
        buf_len = {}
        buf_clean = {}
        for idx, (aname, akind, alen) in enumerate(fn["args"]):
            areg = arg_regs[idx]
            if akind == "bytes":
                env[aname] = ("buf", aname)
                buf_base[aname] = regs[areg]
                buf_clean[aname] = aname not in fn["hidden"]
            else:
                env[aname] = regs[areg]
            if aname not in fn["hidden"] or akind == "bytes":
                marks[areg] = False

        for aname, akind, alen in fn["args"]:
            if akind == "bytes":
                buf_len[aname] = env[alen] if alen in env else r_const(int(alen))
                # Buffer sits in 64-bit address space (`base + len <= 2^64`)
                facts.append(r_sub(r_const(M64 + 1), r_add(buf_base[aname], buf_len[aname])))

        # Stack headroom: `sp >= stack_budget`
        if fn["stack"] > 0:
            facts.append(r_sub(regs[sp_reg], r_const(fn["stack"])))

        def get_byte(buf, idx_row, cur_st):
            key = (buf, idx_row)
            bc = cur_st["byte_cache"]
            if key not in bc:
                bc[key] = fresh_var(cur_st, 0, 255)
            else:
                v = bc[key]
                if v not in cur_st["facts"]:
                    cur_st["facts"].append(v)
                    cur_st["facts"].append(r_sub(r_const(255), v))
            return bc[key]

        def quot_rem(x, m, cur_st, nonneg=False):
            if not x[1]:
                return r_const(x[0] // m), r_const(x[0] % m)
            key = (x, m)
            if key in cur_st["div_cache"]:
                return cur_st["div_cache"][key]
            q_idx = cur_st["nvars"]
            r_idx = q_idx + 1
            cur_st["nvars"] += 2
            q = r_var(q_idx)
            rem = r_var(r_idx)
            f = cur_st["facts"]
            f.append(rem)
            f.append(r_sub(r_const(m - 1), rem))
            f.append(r_sub(x, r_add(r_scale(m, q), rem)))
            f.append(r_sub(r_add(r_scale(m, q), rem), x))
            if nonneg or (not x[1] and x[0] >= 0) or (x in f):
                f.append(q)
                best = None
                for fact in f:
                    s = r_add(fact, x)
                    if not s[1]:
                        if best is None or s[0] < best:
                            best = s[0]
                if best is not None:
                    f.append(r_sub(r_const(best // m), q))
            cur_st["div_cache"][key] = (q, rem)
            return q, rem

        def sym_low(x, m, cur_st):
            if not x[1]:
                return r_const(x[0] % m)
            f = cur_st["facts"]
            if (x in f) and r_plain(f, r_sub(r_const(m - 1), x)):
                return x
            return quot_rem(x, m, cur_st, nonneg=True)[1]

        state = {
            "nvars": init_nvars,
            "regs": regs,
            "marks": marks,
            "flags": {"zf": None, "cf": None},
            "flag_marks": {"zf": True, "cf": True},
            "facts": facts,
            "eqs": [],
            "neq": [],
            "buf_base": buf_base,
            "buf_len": buf_len,
            "buf_clean": buf_clean,
            "get_byte": get_byte,
            "byte_cache": {},
            "quot_rem": quot_rem,
            "div_cache": {},
            "stack_mem": {},  # sp_offset -> (val, mark)
            "min_sp": 0,
        }

        for aname, bound in fn["below"]:
            if aname in env:
                facts.append(r_sub(r_const(bound - 1), env[aname]))
        for aname, bound in fn["atleast"]:
            if aname in env:
                facts.append(r_sub(env[aname], r_const(bound)))
        for k, terms in fn["linpre"]:
            facts.append(self.linpre_row(k, terms, env))
        for req in fn["requires"]:
            self.assume_fact(req, env, state)

        stream = Stream(proof["items"])
        places = proof["places"]

        def clone(st):
            return {
                "nvars": st["nvars"],
                "regs": dict(st["regs"]),
                "marks": dict(st["marks"]),
                "flags": dict(st["flags"]),
                "flag_marks": dict(st["flag_marks"]),
                "facts": list(st["facts"]),
                "eqs": list(st["eqs"]),
                "neq": list(st["neq"]),
                "buf_base": st["buf_base"],
                "buf_len": st["buf_len"],
                "buf_clean": st["buf_clean"],
                "get_byte": st["get_byte"],
                "byte_cache": dict(st["byte_cache"]),
                "quot_rem": st["quot_rem"],
                "div_cache": dict(st["div_cache"]),
                "stack_mem": dict(st["stack_mem"]),
                "min_sp": st["min_sp"],
                "place_entry_regs": st.get("place_entry_regs", {}),
                "place_entry_fq": st.get("place_entry_fq", frozenset()),
            }

        def eval_table_expr(ex, bind, st):
            tag = ex[0]
            if tag == "number":
                return r_const(ex[1]), False
            if tag == "name":
                nm = ex[1]
                if nm == "unknown":
                    return None, True
                if nm in bind:
                    v = bind[nm]
                    if nm in tab_mod.NUMBERS:
                        return r_const(int(v, 0) if isinstance(v, str) else v), False
                    return st["regs"][v], st["marks"][v]
                return st["regs"][nm], st["marks"][nm]
            if tag == "call":
                op, args = ex[1], ex[2]
                if op == "add64":
                    a, ma = eval_table_expr(args[0], bind, st)
                    b, mb = eval_table_expr(args[1], bind, st)
                    res = r_add(a, b)
                    self.entail(st["facts"], res, stream)
                    self.entail(st["facts"], r_sub(r_const(M64), res), stream)
                    return res, (ma or mb)
                if op == "sub64":
                    a, ma = eval_table_expr(args[0], bind, st)
                    b, mb = eval_table_expr(args[1], bind, st)
                    res = r_sub(a, b)
                    self.entail(st["facts"], res, stream)
                    self.entail(st["facts"], r_sub(r_const(M64), res), stream)
                    return res, (ma or mb)
                if op == "shl64":
                    a, ma = eval_table_expr(args[0], bind, st)
                    b, mb = eval_table_expr(args[1], bind, st)
                    if b[1]:
                        raise Refuse("non-constant shift in shl64")
                    k = b[0] % 64
                    if not a[1]:
                        return r_const(((a[0] & M64) << k) & M64), (ma or mb)
                    lim = 1 << (64 - k)
                    bound_goal = r_sub(r_const(lim - 1), a)
                    if r_plain(st["facts"], bound_goal):
                        return r_scale(1 << k, a), (ma or mb)
                    tag_s, _ = stream.pop_tag()
                    if tag_s == "exact":
                        self.entail(st["facts"], bound_goal, stream)
                        return r_scale(1 << k, a), (ma or mb)
                    if tag_s == "wrap":
                        low_a = sym_low(a, lim, st)
                        return r_scale(1 << k, low_a), (ma or mb)
                    raise Refuse(f"expected `exact` or `wrap` for shl64, got `{tag_s}`")
                if op == "shr64":
                    a, ma = eval_table_expr(args[0], bind, st)
                    b, mb = eval_table_expr(args[1], bind, st)
                    if b[1]:
                        raise Refuse("non-constant shift in shr64")
                    k = b[0] % 64
                    if not a[1]:
                        return r_const((a[0] & M64) >> k), (ma or mb)
                    q, _ = quot_rem(a, 1 << k, st, nonneg=True)
                    return q, (ma or mb)
                if op == "and64":
                    a, ma = eval_table_expr(args[0], bind, st)
                    b, mb = eval_table_expr(args[1], bind, st)
                    if not b[1] and b[0] >= 0 and ((b[0] + 1) & b[0]) == 0:
                        d = b[0] + 1
                        return sym_low(a, d, st), (ma or mb)
                    if not b[1] and b[0] == (1 << 64) - 64:
                        q, _ = quot_rem(a, 64, st, nonneg=True)
                        return r_scale(64, q), (ma or mb)
                    raise Refuse(f"unsupported and64 mask {b}")
                if op == "low32":
                    a, ma = eval_table_expr(args[0], bind, st)
                    return sym_low(a, 1 << 32, st), ma
                if op == "low8":
                    a, ma = eval_table_expr(args[0], bind, st)
                    return sym_low(a, 256, st), ma
                if op == "equal":
                    a, ma = eval_table_expr(args[0], bind, st)
                    b, mb = eval_table_expr(args[1], bind, st)
                    return ("eq", a, b), (ma or mb)
                if op == "below":
                    a, ma = eval_table_expr(args[0], bind, st)
                    b, mb = eval_table_expr(args[1], bind, st)
                    return ("lt", a, b), (ma or mb)
                if op == "mem8":
                    base, mb = eval_table_expr(args[0], bind, st)
                    disp, md = eval_table_expr(args[1], bind, st)
                    addr = r_add(base, disp)
                    if mb or md:
                        raise Refuse("memory read address depends on values kept out of the trace")
                    # Match `addr = buf_base[b] + idx` with `0 <= idx < buf_len[b]`
                    # (the run is the one whose base address, a single unknown of the entry, the address
                    # is counted from once; that the address lies within it is then shown, not assumed)
                    def counted_from(bbase):
                        vs = [i for i, cf in enumerate(bbase[1]) if cf != 0]
                        return (bbase[0] == 0 and len(vs) == 1 and bbase[1][vs[0]] == 1
                                and vs[0] < len(addr[1]) and addr[1][vs[0]] == 1)
                    for bnm, bbase in st["buf_base"].items():
                        if not counted_from(bbase):
                            continue
                        idx = r_sub(addr, bbase)
                        self.entail(st["facts"], idx, stream)
                        self.entail(st["facts"], r_sub(r_sub(st["buf_len"][bnm], idx), r_const(1)), stream)
                        return st["get_byte"](bnm, idx, st), (not st["buf_clean"][bnm])
                    raise Refuse("mem8 address does not fall in any contract buffer")
                if op == "mem64":
                    base, mb = eval_table_expr(args[0], bind, st)
                    disp, md = eval_table_expr(args[1], bind, st)
                    if mb or md:
                        raise Refuse("mem64 address depends on values kept out of the trace")
                    off_row = r_sub(r_add(base, disp), entry_regs[sp_reg])
                    if not off_row[1] and off_row[0] in st["stack_mem"]:
                        return st["stack_mem"][off_row[0]]
                    raise Refuse("mem64 load from unwritten stack slot")
                if op == "on16":
                    return eval_table_expr(args[0], bind, st)
                raise Refuse(f"unsupported table op `{op}` in verify2")
            raise Refuse(f"unsupported table expr {ex} in verify2")

        def run_path(pc, st, origin_place=None, origin_dec=None, visited_places=frozenset(),
                     base_st=None, jstack=frozenset(), jdone=None):
            if jdone is None:
                jdone = {}
            if base_st is None:
                base_st = clone(st)
            while True:
                if pc in places and pc not in visited_places:
                    pl = places[pc]
                    if pl["is_join"]:
                        if pc in jstack:
                            raise Refuse(f"at join place {pc} a path returns to it (add `decreases` for a loop)")
                        def _check_arrive_join(first_j, arr_st):
                            for kr in pl["keep"]:
                                if arr_st["regs"][kr] != first_j["regs"][kr]:
                                    raise Refuse(f"at join place {pc} register {kr} does not match first arrival")
                            for r in reg_names:
                                if not first_j["marks"][r] and arr_st["marks"][r]:
                                    raise Refuse(f"at join place {pc} register {r} may depend on values kept out of the trace")
                            for o, (fv, fmk) in first_j["stack_mem"].items():
                                if o not in arr_st["stack_mem"] or arr_st["stack_mem"][o][0] != fv:
                                    raise Refuse(f"at join place {pc} stack slot {o} does not match first arrival")
                                if (not fmk) and arr_st["stack_mem"][o][1]:
                                    raise Refuse(f"at join place {pc} stack slot {o} may depend on values kept out of the trace")
                            penv = dict(env)
                            for nm, rn in pl["names"]:
                                penv[nm] = arr_st["regs"][rn]
                            for fct in pl["facts"]:
                                self.check_fact(fct, penv, arr_st, stream)
                        if pc in jdone:
                            _check_arrive_join(jdone[pc], st)
                            return
                        bn = base_st["nvars"]
                        for kr in pl["keep"]:
                            if len(st["regs"][kr][1]) > bn:
                                raise Refuse(f"at join place {pc} kept register {kr} depends on a value not in scope")
                        first_j = clone(base_st)
                        for kr in pl["keep"]:
                            first_j["regs"][kr] = st["regs"][kr]
                        first_j["stack_mem"] = {
                            o: (v, mk) for o, (v, mk) in st["stack_mem"].items() if len(v[1]) <= bn
                        }
                        for r in reg_names:
                            first_j["marks"][r] = st["marks"][r] or (r in pl["marked"])
                        _check_arrive_join(first_j, st)
                        # Build generalized join state from scope-bounded `first_j`
                        gj = clone(first_j)
                        gj["neq"] = []
                        base_v = gj["nvars"]
                        gj["nvars"] += len(reg_names)
                        for r_idx, r in enumerate(reg_names):
                            if r not in pl["keep"]:
                                v = r_var(base_v + r_idx)
                                gj["facts"].append(v)
                                gj["facts"].append(r_sub(r_const(M64), v))
                                gj["regs"][r] = v
                        gj["flags"] = {"zf": None, "cf": None}
                        gj["flag_marks"] = {"zf": True, "cf": True}
                        penv2 = dict(env)
                        for nm, rn in pl["names"]:
                            penv2[nm] = gj["regs"][rn]
                        for fct in pl["facts"]:
                            self.assume_fact(fct, penv2, gj)
                        run_path(pc, gj, origin_place, origin_dec, visited_places | {pc}, base_st, jstack | {pc}, jdone)
                        jdone[pc] = first_j
                        return
                    penv = dict(env)
                    for nm, rn in pl["names"]:
                        penv[nm] = st["regs"][rn]
                    for fct in pl["facts"]:
                        self.check_fact(fct, penv, st, stream)
                    if origin_place == pc and pl["decreases"] is not None:
                        new_dec = self.eval_sexpr(pl["decreases"], penv, st, stream)
                        self.entail(st["facts"], origin_dec, stream)
                        self.entail(st["facts"], r_sub(r_sub(origin_dec, new_dec), r_const(1)), stream)
                    if origin_place == pc:
                        for kr in pl["keep"]:
                            if st["regs"][kr] != entry_regs.get(kr, st["regs"][kr]) and kr in st["place_entry_regs"]:
                                self.entail_eq(st["facts"], st["regs"][kr], st["place_entry_regs"][kr], stream)
                        for o in st.get("place_entry_fq", frozenset()):
                            if o not in st["stack_mem"] or st["stack_mem"][o][1]:
                                raise Refuse(f"at loop place clean frame slot {o} may depend on values kept out of the trace")
                        return
                    # Enter place once as fresh symbolic state, keeping `eqs` (spec facts)
                    pst = clone(st)
                    pst["facts"] = list(facts)
                    pst["eqs"] = list(st["eqs"])
                    pst["neq"] = []
                    pst["place_entry_fq"] = frozenset(o for o, (_, mk) in st["stack_mem"].items() if not mk)
                    base_v = pst["nvars"]
                    pst["nvars"] += len(reg_names)
                    for r_idx, r in enumerate(reg_names):
                        if r not in pl["keep"]:
                            v = r_var(base_v + r_idx)
                            pst["facts"].append(v)
                            pst["facts"].append(r_sub(r_const(M64), v))
                            pst["regs"][r] = v
                            pst["marks"][r] = r in pl["marked"]
                    pst["place_entry_regs"] = dict(pst["regs"])
                    penv2 = dict(env)
                    for nm, rn in pl["names"]:
                        penv2[nm] = pst["regs"][rn]
                    for fct in pl["facts"]:
                        self.assume_fact(fct, penv2, pst)
                    dec_val = self.eval_sexpr(pl["decreases"], penv2, pst, None) if pl["decreases"] is not None else None
                    run_path(pc, pst, origin_place=pc, origin_dec=dec_val, visited_places=visited_places | {pc},
                             base_st=clone(pst), jstack=frozenset(), jdone={})
                    return

                if pc not in fn["instrs"]:
                    raise Refuse(f"pc {pc} has no instruction")
                nxt, row_text = fn["instrs"][pc]
                ins_toks = tab_mod.parse_row(row_text)
                row, bind = tab_mod.find(self.heads, ins_toks)
                if row is None:
                    raise Refuse(f"no table row matches `{row_text}`")

                next_pc = nxt
                for stmt in row.effect:
                    kind = stmt[0]
                    if kind == "nothing":
                        continue
                    if kind == "set":
                        lhs, rhs = stmt[1], stmt[2]
                        val, mk = eval_table_expr(rhs, bind, st)
                        if lhs[0] == "name":
                            v = bind.get(lhs[1], lhs[1])
                            rname = v[1:] if isinstance(v, str) and v.startswith(".") else v
                            if rname in ("zf", "cf"):
                                st["flags"][rname] = val
                                st["flag_marks"][rname] = mk
                            else:
                                st["regs"][rname] = val
                                st["marks"][rname] = mk
                        elif lhs[0] == "call" and lhs[1] == "mem64":
                            base, mb = eval_table_expr(lhs[2][0], bind, st)
                            disp, md = eval_table_expr(lhs[2][1], bind, st)
                            if mb or md:
                                raise Refuse("mem64 store address depends on values kept out of the trace")
                            off_row = r_sub(r_add(base, disp), entry_regs[sp_reg])
                            if off_row[1]:
                                raise Refuse("non-constant stack store offset")
                            st["stack_mem"][off_row[0]] = (val, mk)
                            st["min_sp"] = min(st["min_sp"], off_row[0])
                        else:
                            raise Refuse(f"unsupported lhs {lhs} in verify2")
                    elif kind == "jump":
                        tgt_expr, cond = stmt[1], stmt[2]
                        tval = bind[tgt_expr[1]] if tgt_expr[0] == "name" else tgt_expr[1]
                        target = int(tval, 0) if isinstance(tval, str) else tval
                        if cond is None:
                            next_pc = target
                            if target == origin_place:
                                visited_places = frozenset()
                            break
                        cond_flag, want = cond
                        negated = not want
                        if cond_flag == "hi":
                            if st["flag_marks"]["zf"] or st["flag_marks"]["cf"]:
                                raise Refuse("jump on a flag that may depend on values kept out of the trace")
                            zf_rel, cf_rel = st["flags"]["zf"], st["flags"]["cf"]
                            if (zf_rel is not None and cf_rel is not None
                                    and zf_rel[0] == "eq" and cf_rel[0] == "lt"
                                    and zf_rel[1] == cf_rel[1] and zf_rel[2] == cf_rel[2]):
                                frel = ("lt", zf_rel[2], zf_rel[1])
                            else:
                                raise Refuse("jump on `hi` without matching cmp flags")
                        else:
                            if st["flag_marks"][cond_flag]:
                                raise Refuse("jump on a flag that may depend on values kept out of the trace")
                            frel = st["flags"][cond_flag]
                            if frel is None:
                                raise Refuse(f"jump on unset flag `{cond_flag}`")
                        op_f, a, b = frel
                        live_ways = []
                        def _assume_way(f_is_true, w_facts):
                            dest = target if (f_is_true == want) else nxt
                            if any((not r[1]) and r[0] < 0 for r in w_facts):
                                return
                            if all(not r[1] for r in w_facts):
                                live_ways.append((dest, clone(st)))
                                return
                            tag_w, _ = stream.pop_tag()
                            if tag_w == "live":
                                st_w = clone(st)
                                st_w["facts"].extend(w_facts)
                                live_ways.append((dest, st_w))
                            elif tag_w == "dead":
                                self.refute_dead(st["facts"] + w_facts, stream)
                            else:
                                raise Refuse(f"expected `live`/`dead`, got `{tag_w}`")

                        if op_f == "eq":
                            diff_ab = r_sub(a, b)
                            diff_ba = r_sub(b, a)
                            if diff_ab not in st["neq"] and diff_ba not in st["neq"]:
                                _assume_way(True, [diff_ab, diff_ba])
                            if not diff_ab[1]:
                                if diff_ab[0] != 0:
                                    live_ways.append((target if (False == want) else nxt, clone(st)))
                            else:
                                nxt_item = stream.items[stream.pos] if stream.pos < len(stream.items) else None
                                if nxt_item is not None and nxt_item[0] == "t" and nxt_item[1] == "neq":
                                    stream.pos += 1
                                    st_w = clone(st)
                                    st_w["neq"].append(diff_ab)
                                    live_ways.append((target if (False == want) else nxt, st_w))
                                else:
                                    _assume_way(False, [r_sub(diff_ab, r_const(1))])
                                    _assume_way(False, [r_sub(diff_ba, r_const(1))])
                        elif op_f == "lt":
                            _assume_way(True, [r_sub(r_sub(b, a), r_const(1))])
                            _assume_way(False, [r_sub(a, b)])
                        else:
                            raise Refuse(f"unknown flag relation {frel}")
                        for dest, st_w in live_ways:
                            next_v = visited_places if (dest != origin_place and dest not in jstack) else (visited_places - {dest})
                            run_path(dest, st_w, origin_place, origin_dec, next_v, base_st, jstack, jdone)
                        return
                    elif kind == "call":
                        tgt_expr = stmt[1]
                        callee_nm = bind[tgt_expr[1]] if tgt_expr[0] == "name" else tgt_expr[1]
                        if callee_nm not in self.proven:
                            raise Refuse(f"callee `{callee_nm}` has not been verified")
                        c = self.proven[callee_nm]
                        c_is_arm = c["machine"] == "arm64"
                        if c_is_arm != is_arm:
                            raise Refuse(f"callee `{callee_nm}` targets a different machine")
                        c_arg_regs = c["argregs"] if c["argregs"] is not None else (ARM_ARGS if is_arm else X86_ARGS)
                        c_keeps = set(c["keeps"]) if c["keeps"] is not None else (ARM_CALLEE_SAVED if is_arm else X86_CALLEE_SAVED)
                        c_ret_reg = c["retreg"] if c["retreg"] is not None else ("x0" if is_arm else "rax")
                        need_stk = c["stack"] + (0 if is_arm else 8)
                        sp_off = r_sub(st["regs"][sp_reg], entry_regs[sp_reg])
                        if sp_off[1]:
                            raise Refuse("non-constant stack pointer at call")
                        if -sp_off[0] + need_stk > fn["stack"]:
                            raise Refuse(f"call to `{callee_nm}` exceeds stack budget {fn['stack']}")
                        if is_arm and (sp_off[0] % 16 != 0):
                            raise Refuse("stack pointer is not 16-byte aligned at AArch64 call")
                        # Build callee argument environment and check trace cleanliness of non-hidden args
                        cenv = {}
                        for idx, (anm, akind, alen) in enumerate(c["args"]):
                            areg = c_arg_regs[idx]
                            if akind == "bytes":
                                found_buf = None
                                for bnm, bbase in st["buf_base"].items():
                                    if st["regs"][areg] == bbase:
                                        found_buf = bnm
                                        break
                                if found_buf is None:
                                    raise Refuse(f"callee `{callee_nm}` bytes arg `{anm}` does not match a caller buffer")
                                cenv[anm] = ("buf", found_buf)
                                if anm not in c["hidden"] and not st["buf_clean"][found_buf]:
                                    raise Refuse(f"callee `{callee_nm}` exposes buffer `{found_buf}` kept out of caller trace")
                            else:
                                cenv[anm] = st["regs"][areg]
                                if anm not in c["hidden"] and st["marks"][areg]:
                                    raise Refuse(f"callee `{callee_nm}` trace arg `{anm}` may depend on values kept out of trace")
                        # Check callee entry preconditions (`below`, `atleast`, `requires`)
                        # (the order the proof file's items are read in: at-least, linear conditions, bounds)
                        for anm, bnd in c["atleast"]:
                            if anm in cenv:
                                self.entail(st["facts"], r_sub(cenv[anm], r_const(bnd)), stream)
                        for k, terms in c["linpre"]:
                            self.entail(st["facts"], self.linpre_row(k, terms, cenv), stream)
                        for anm, bnd in c["below"]:
                            if anm in cenv:
                                self.entail(st["facts"], r_sub(r_const(bnd - 1), cenv[anm]), stream)
                        for req in c["requires"]:
                            self.check_fact(req, cenv, st, stream)
                        # Drop stack slots below current sp; clobber non-preserved registers (matching Lean nvars + r numbering)
                        cur_sp_off = sp_off[0]
                        st["stack_mem"] = {o: v for o, v in st["stack_mem"].items() if o >= cur_sp_off}
                        base_v = st["nvars"]
                        st["nvars"] += len(reg_names)
                        for r_idx, r in enumerate(reg_names):
                            if r != sp_reg and r not in c_keeps:
                                rv_i = r_var(base_v + r_idx)
                                st["regs"][r] = rv_i
                                st["facts"].append(rv_i)
                                st["facts"].append(r_sub(r_const(M64), rv_i))
                                st["marks"][r] = True
                        st["flags"] = {"zf": None, "cf": None}
                        st["flag_marks"] = {"zf": True, "cf": True}
                        if c["returns"] is not None:
                            ret_val = self.eval_sexpr(c["returns"], cenv, st, stream)
                            rv = st["regs"][c_ret_reg]
                            if self.is_row(ret_val):
                                st["facts"].append(r_sub(rv, ret_val))
                                st["facts"].append(r_sub(ret_val, rv))
                            else:
                                st["eqs"].insert(0, (ret_val, rv))
                            st["marks"][c_ret_reg] = False
                    elif kind == "return":
                        # Check sp restored, x30 intact (AArch64), callee-saved registers intact, and trace marks clean
                        self.entail_eq(st["facts"], st["regs"][sp_reg], entry_regs[sp_reg], stream)
                        if st["marks"][sp_reg]:
                            raise Refuse("at return stack pointer may depend on values kept out of the trace")
                        if is_arm:
                            self.entail_eq(st["facts"], st["regs"]["x30"], entry_regs["x30"], stream)
                            if st["marks"]["x30"]:
                                raise Refuse("at return link register x30 may depend on values kept out of the trace")
                        for r in callee_saved:
                            self.entail_eq(st["facts"], st["regs"][r], entry_regs[r], stream)
                        if fn["returns"] is not None:
                            want = self.eval_sexpr(fn["returns"], env, st, stream)
                            self.expand_eq(st["regs"][ret_reg], want, env, st, stream)
                        return
                    else:
                        raise Refuse(f"unsupported table stmt `{kind}` in verify2")
                pc = next_pc

        run_path(0, state)
        self.proven[fn["name"]] = fn


def verify_files(table_path, statement_path, proof_path):
    rows = tab_mod.read(table_path)
    fns, defs = parse_statement(statement_path)
    proofs = parse_proof(proof_path)
    proven = {}
    v = Verifier(rows, defs, proven)
    for fn in fns:
        if fn["name"] not in proofs:
            raise Refuse(f"no proof section `for {fn['name']}`")
        v.verify_fn(fn, proofs[fn["name"]])
    return len(fns)


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if len(argv) != 3:
        print("usage: verify2.py TABLE STATEMENT PROOF", file=sys.stderr)
        return 2
    try:
        n = verify_files(argv[0], argv[1], argv[2])
    except Refuse as exc:
        print(f"refused: {exc}")
        return 1
    print(f"shown ({n} function{'s' if n != 1 else ''}, verify2)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
