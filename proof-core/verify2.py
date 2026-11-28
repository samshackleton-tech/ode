#!/usr/bin/env python3
"""Independent second verifier for Ode `.statement` + `.proof` files (scalar, byte, word, and SIMD).

Written from scratch in pure Python with ZERO code shared with Lean's `Core.lean`, `Machine.lean`,
`Contract.lean`, or `kcheck/`. Reads only the instruction tables (`core/x86.tab`, `arm64/arm64.tab`
via `core/table.py`), a `.statement` file, and a `.proof` file, and prints `shown` or `refused: ...`.

Covers both x86-64 and AArch64:
  - Table-driven symbolic execution of integer, load/store (`mem8`/`mem16`/`mem32`/`mem64`/`mem128`/
    `mem512`/`mem512a`), compare, branch, select, call, tail-call, and return instructions.
  - 32-bit word term table (`WordTab`), 128-bit and 512-bit SIMD lanes, hardware SHA-256 ops
    (x86 SHA-NI and AArch64 SHA2), uniform word-backed scalar/vector memory, aligned 64-byte stack
    spills, lane pointer tables, `ensuresw`, and vector loop `lane`/`cell` invariants.
  - Cache-line and VM-page alignment (`align`) and granule disjointness (`disjoint`).
  - Linear-inequality Farkas/Gomory refutation certificates (`p`/`r`, `s`, `q`), loop/join `place`s,
    `check` assertions, `def` unfolding, multi-function contracts, and trace-mark enforcement.

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


def r_signed(r):
    # Match `Core.lean:signed`: signed displacement constants (`>= 3 * 2^62`) wrap below 0.
    if (not r[1]) and r[0] >= 3 * (1 << 62):
        return r_const(r[0] - (1 << 64))
    return r


class FactList(list):
    """List of linear rows `(c, v_tuple)` with an O(1) minimum-constant index by variable vector."""
    __slots__ = ("_min",)

    def __init__(self, items=()):
        super().__init__()
        self._min = {}
        if items:
            self.extend(items)

    def append(self, row):
        super().append(row)
        c, v = row
        prev = self._min.get(v)
        if prev is None or c < prev:
            self._min[v] = c

    def extend(self, rows):
        m = self._min
        for row in rows:
            super().append(row)
            c, v = row
            prev = m.get(v)
            if prev is None or c < prev:
                m[v] = c

    def copy(self):
        out = FactList.__new__(FactList)
        list.__init__(out, self)
        out._min = dict(self._min)
        return out


class KnownMap:
    """Ordered map of `(fn_nm, keys_tuple) -> val`, newest-first, with O(1) exact and per-fn lookup."""
    __slots__ = ("by_fn", "exact", "by_val")

    def __init__(self, by_fn=None, exact=None, by_val=None):
        self.by_fn = {} if by_fn is None else by_fn
        self.exact = {} if exact is None else exact
        self.by_val = {} if by_val is None else by_val

    def add(self, fn_nm, keys, val):
        ks = tuple(keys)
        self.by_fn.setdefault(fn_nm, []).append((ks, val))
        self.exact[(fn_nm, ks)] = val
        if isinstance(val, int):
            self.by_val[val] = (fn_nm, ks)

    def has_fn(self, fn_nm):
        return fn_nm in self.by_fn

    def find(self, facts, fn_nm, keys, same_keys_fn):
        if fn_nm not in self.by_fn:
            return None
        ks = tuple(keys)
        hit = self.exact.get((fn_nm, ks))
        if hit is not None:
            return hit
        bucket = self.by_fn[fn_nm]
        for idx in range(len(bucket) - 1, -1, -1):
            ks0, val0 = bucket[idx]
            if same_keys_fn(facts, ks0, ks):
                return val0
        return None

    def copy(self):
        return KnownMap(
            {k: list(v) for k, v in self.by_fn.items()},
            dict(self.exact),
            dict(self.by_val),
        )


def r_plain(facts, g):
    cg, vg = g
    if not vg:
        return cg >= 0
    if isinstance(facts, FactList):
        cf = facts._min.get(vg)
        return cf is not None and cf <= cg
    for cf, vf in facts:
        if cf <= cg and vf == vg:
            return True
    return False


def r_const_of(facts, r):
    cr, vr = r
    if not vr:
        return cr
    if isinstance(facts, FactList):
        cf = facts._min.get(vr)
        if cf is not None:
            k = cr - cf
            neg_v = tuple(-c for c in vr)
            cf2 = facts._min.get(neg_v)
            if cf2 is not None and cf2 <= k - cr:
                return k
        return None
    for cf, vf in facts:
        if vf == vr:
            k = cr - cf
            if r_plain(facts, r_sub(r_const(k), r)):
                return k
    return None


# ---------------------------------------------------------------------------
# 32-bit word term table (`WordTab`) for SIMD / word-level verification
# ---------------------------------------------------------------------------

W32 = 1 << 32


def r_word(r):
    """Reduce a row's constant and coefficients modulo 2^32."""
    return (r[0] % W32, _trim(tuple(c % W32 for c in r[1])))


def r_high(r):
    """Quotient row by 2^32 (exact floor division, matching Lean `Int.tdiv`/`/` for nonnegative)."""
    return (r[0] // W32, _trim(tuple(c // W32 for c in r[1])))


def r_has_high(r):
    """Whether `r` has any nonzero coefficient that is a multiple of 2^32."""
    return any(c != 0 and (c % W32) == 0 for c in r[1])


def r_var_idx(r):
    """If `r` is exactly `1 * v_i + 0`, return `i`, else `None`."""
    if r[0] != 0:
        return None
    nz = [(i, c) for i, c in enumerate(r[1]) if c != 0]
    if len(nz) == 1 and nz[0][1] == 1:
        return nz[0][0]
    return None


def merge_add(xs, ys):
    """Canonical sorted linear combination of 32-bit word term IDs modulo 2^32."""
    out = []
    i = j = 0
    nx, ny = len(xs), len(ys)
    while i < nx and j < ny:
        a, ca = xs[i]
        b, cb = ys[j]
        if a < b:
            out.append((a, ca))
            i += 1
        elif b < a:
            out.append((b, cb))
            j += 1
        else:
            c = (ca + cb) % W32
            if c != 0:
                out.append((a, c))
            i += 1
            j += 1
    if i < nx:
        out.extend(xs[i:])
    if j < ny:
        out.extend(ys[j:])
    return tuple(out)


def vec_reg_index(name):
    """Map `zmm0..31`, `xmm0..15`, `ymm0..15`, `v0..31` to `0..31`."""
    if name.startswith(("zmm", "xmm", "ymm")):
        s = name[3:]
    elif name.startswith("v"):
        s = name[1:]
    else:
        return None
    if s.isdigit():
        r = int(s)
        if 0 <= r < 32:
            return r
    return None


class WordTab:
    """Hash-consed table of 32-bit word terms (independent Python counterpart to Core.lean `Tab`)."""

    def __init__(self, arr=None, idx=None):
        self.arr = [] if arr is None else list(arr)
        self.idx = {} if idx is None else dict(idx)

    def clone(self):
        return WordTab(self.arr, self.idx)

    def find(self, node):
        i = self.idx.get(node)
        if i is not None and i < len(self.arr) and self.arr[i] == node:
            return i
        return None

    def intern(self, node):
        i = self.find(node)
        if i is not None:
            return i
        i = len(self.arr)
        self.arr.append(node)
        self.idx[node] = i
        return i

    def addends(self, a):
        if 0 <= a < len(self.arr) and self.arr[a][0] == "add":
            return self.arr[a][1]
        return ((a, 1),)

    def w_atom(self, r):
        return self.intern(("atom", r_word(r)))

    def w_atom_k(self, known_div_rem, var_to_term, r):
        """Convert a linear row (mod 2^32) into a word term ID, resolving canonical mod-2^32
        remainders (`known_div_rem`) and `termVal` scalar variables (`var_to_term`)."""
        w0 = r_word(r)
        v0 = r_var_idx(w0)
        r_eff = known_div_rem[v0] if (v0 is not None and v0 in known_div_rem) else r
        w = r_word(r_eff)
        pulled = False
        ts = ()
        rem = []
        n_arr = len(self.arr)
        for v, c in enumerate(w[1]):
            cm = c % W32
            if cm != 0 and v in var_to_term and var_to_term[v] < n_arr:
                tid = var_to_term[v]
                pulled = True
                add = self.addends(tid) if cm == 1 else ((tid, cm),)
                ts = merge_add(add, ts)
                rem.append(0)
            else:
                rem.append(c if cm != 0 else 0)
        if not pulled:
            return self.w_atom(r)
        rem_row = (w[0], _trim(tuple(rem)))
        if rem_row == (0, ()):
            if not ts:
                return self.w_atom((0, ()))
            if len(ts) == 1 and ts[0][1] == 1:
                return ts[0][0]
            return self.intern(("add", ts))
        rid = self.w_atom(rem_row)
        if not ts:
            return rid
        return self.intern(("add", merge_add(((rid, 1),), ts)))

    def w_add(self, a, b):
        return self.intern(("add", merge_add(self.addends(a), self.addends(b))))

    def w_xor(self, a, b):
        return self.intern(("xor", min(a, b), max(a, b)))

    def w_and(self, a, b):
        return self.intern(("band", min(a, b), max(a, b)))

    def w_rotr(self, a, n):
        return self.intern(("rotr", a, n))

    def w_shl(self, a, n):
        return self.intern(("shl", a, n))

    def w_shr(self, a, n):
        return self.intern(("shr", a, n))

    def w_ult(self, a, b):
        if a == b:
            return self.w_atom((0, ()))
        return self.intern(("ult", a, b))

    def w_sel(self, m, a, b):
        if 0 <= m < len(self.arr) and self.arr[m] == ("atom", (0, ())):
            return b
        return self.intern(("sel", m, a, b))

    def w_add_const(self, a, k):
        if k == 0:
            return a
        if 0 <= a < len(self.arr) and self.arr[a][0] == "atom":
            return self.w_atom(r_add(self.arr[a][1], r_const(k)))
        return self.w_add(a, self.w_atom(r_const(k)))

    def or_turns(self, pairs):
        out = []
        for a, b in pairs:
            if not (0 <= a < len(self.arr) and 0 <= b < len(self.arr)):
                return None
            na, nb = self.arr[a], self.arr[b]
            if na[0] == "shl" and nb[0] == "shr" and na[1] == nb[1] and na[2] + nb[2] == 32 and 0 < nb[2] < 32:
                out.append((na[1], nb[2]))
            elif na[0] == "shr" and nb[0] == "shl" and na[1] == nb[1] and na[2] + nb[2] == 32 and 0 < na[2] < 32:
                out.append((na[1], na[2]))
            else:
                return None
        return out

    def const_words(self, ids):
        out = []
        for a in ids:
            if not (0 <= a < len(self.arr)):
                return None
            nd = self.arr[a]
            if nd[0] != "atom" or nd[1][1]:
                return None
            out.append(nd[1][0])
        return out

    @staticmethod
    def shuffle_turn(ks):
        if ks == [0x00030201, 0x04070605, 0x080B0A09, 0x0C0F0E0D]:
            return 8
        if ks == [0x01000302, 0x05040706, 0x09080B0A, 0x0D0C0F0E]:
            return 16
        return None

    # Hardware SHA-256 word combinators (x86 SHA-NI and AArch64 SHA2)
    def w_sha256_ch(self, e, f, g):
        fg = self.w_xor(f, g)
        efg = self.w_and(e, fg)
        return self.w_xor(g, efg)

    def w_sha256_maj(self, a, b, c):
        ab = self.w_and(a, b)
        axb = self.w_xor(a, b)
        axbc = self.w_and(axb, c)
        return self.w_xor(ab, axbc)

    def w_sha256_S0(self, a):
        r2 = self.w_rotr(a, 2)
        r13 = self.w_rotr(a, 13)
        r22 = self.w_rotr(a, 22)
        return self.w_xor(self.w_xor(r2, r13), r22)

    def w_sha256_S1(self, e):
        r6 = self.w_rotr(e, 6)
        r11 = self.w_rotr(e, 11)
        r25 = self.w_rotr(e, 25)
        return self.w_xor(self.w_xor(r6, r11), r25)

    def w_sha256_s0(self, x):
        r7 = self.w_rotr(x, 7)
        r18 = self.w_rotr(x, 18)
        s3 = self.w_shr(x, 3)
        return self.w_xor(self.w_xor(r7, r18), s3)

    def w_sha256_s1(self, x):
        r17 = self.w_rotr(x, 17)
        r19 = self.w_rotr(x, 19)
        s10 = self.w_shr(x, 10)
        return self.w_xor(self.w_xor(r17, r19), s10)

    def w_sha256_round(self, a, b, c, d, e, f, g, h, wk):
        s1 = self.w_sha256_S1(e)
        ch = self.w_sha256_ch(e, f, g)
        t1 = self.w_add(self.w_add(self.w_add(h, s1), ch), wk)
        s0 = self.w_sha256_S0(a)
        mj = self.w_sha256_maj(a, b, c)
        t2 = self.w_add(s0, mj)
        return (self.w_add(t1, t2), a, b, c, self.w_add(d, t1), e, f, g)

    def w_sha256_msg1(self, x, y):
        r0 = self.w_add(x[0], self.w_sha256_s0(x[1]))
        r1 = self.w_add(x[1], self.w_sha256_s0(x[2]))
        r2 = self.w_add(x[2], self.w_sha256_s0(x[3]))
        r3 = self.w_add(x[3], self.w_sha256_s0(y[0]))
        return (r0, r1, r2, r3)

    def w_sha256_msg2(self, x, z):
        r0 = self.w_add(x[0], self.w_sha256_s1(z[2]))
        r1 = self.w_add(x[1], self.w_sha256_s1(z[3]))
        r2 = self.w_add(x[2], self.w_sha256_s1(r0))
        r3 = self.w_add(x[3], self.w_sha256_s1(r1))
        return (r0, r1, r2, r3)

    def w_sha256_su1(self, x, y, z):
        t0 = self.w_add(x[0], y[1])
        t1 = self.w_add(x[1], y[2])
        t2 = self.w_add(x[2], y[3])
        t3 = self.w_add(x[3], z[0])
        return self.w_sha256_msg2((t0, t1, t2, t3), z)

    def w_sha256_rnds2(self, x, z, wk):
        a1, b1, c1, d1, e1, f1, g1, h1 = self.w_sha256_round(
            z[3], z[2], x[3], x[2], z[1], z[0], x[1], x[0], wk[0]
        )
        a2, b2, _, _, e2, f2, _, _ = self.w_sha256_round(a1, b1, c1, d1, e1, f1, g1, h1, wk[1])
        return (f2, e2, b2, a2)

    def w_sha256_h(self, x, y, wk):
        a1, b1, c1, d1, e1, f1, g1, h1 = self.w_sha256_round(
            x[0], x[1], x[2], x[3], y[0], y[1], y[2], y[3], wk[0]
        )
        a2, b2, c2, d2, e2, f2, g2, h2 = self.w_sha256_round(a1, b1, c1, d1, e1, f1, g1, h1, wk[1])
        a3, b3, c3, d3, e3, f3, g3, h3 = self.w_sha256_round(a2, b2, c2, d2, e2, f2, g2, h2, wk[2])
        a4, b4, c4, d4, _, _, _, _ = self.w_sha256_round(a3, b3, c3, d3, e3, f3, g3, h3, wk[3])
        return (a4, b4, c4, d4)

    def w_sha256_h2(self, x, y, wk):
        a1, b1, c1, d1, e1, f1, g1, h1 = self.w_sha256_round(
            y[0], y[1], y[2], y[3], x[0], x[1], x[2], x[3], wk[0]
        )
        a2, b2, c2, d2, e2, f2, g2, h2 = self.w_sha256_round(a1, b1, c1, d1, e1, f1, g1, h1, wk[1])
        a3, b3, c3, d3, e3, f3, g3, h3 = self.w_sha256_round(a2, b2, c2, d2, e2, f2, g2, h2, wk[2])
        _, _, _, _, e4, f4, g4, h4 = self.w_sha256_round(a3, b3, c3, d3, e3, f3, g3, h3, wk[3])
        return (e4, f4, g4, h4)


def mask_span(m):
    if m <= 0 or m >= (1 << 64):
        return None
    for k in range(64):
        powk = 1 << k
        if m % powk == 0:
            q = m // powk
            for w in range(1, 65 - k):
                if (1 << w) - 1 == q:
                    return (k, w)
    return None


def r_refutes(given, starts, steps):
    """Independent verifier of the Farkas/Gomory arithmetic refutation rule (indexed starts)."""
    rows = []
    for idx in starts:
        if idx < 0 or idx >= len(given):
            return False
        rows.append(given[idx])
    return _run_refute_steps(rows, steps)


def r_refutes_rows(given, start_rows, steps):
    """Independent verifier of the Farkas/Gomory arithmetic refutation rule (explicit rows,
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
    pieces = []
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
                    "mbounds": [],
                    "lanes": [],
                    "atleast": [],
                    "aligns": [],
                    "disjoint": [],
                    "linpre": [],
                    "returns": None,
                    "result": None,
                    "ensures": [],
                    "ensuresw": [],
                    "valspecs": [],
                    "needs": [],
                    "needsif": [],
                    "stack": 0,
                    "stacklin": None,
                    "stackbits": None,
                    "decreases": None,
                    "hidden": set(),
                    "trace_exprs": [],
                    "result_dep": None,
                    "argregs": None,
                    "keeps": None,
                    "retreg": None,
                    "keeps_vec": None,
                    "piece": None,
                    "pieces": pieces,
                }
                fns.append(cur)
            elif kw == "machine":
                cur["machine"] = parts[1]
            elif kw == "piece":
                al = int(parts[1])
                hex_str = parts[2] if len(parts) > 2 else ""
                pieces.append((al, bytes.fromhex(hex_str)))
            elif kw == "data":
                k = int(parts[1])
                if cur["instrs"]:
                    raise Refuse(f"`data` after an instruction of the function: {line}")
                if k < 0 or k >= len(pieces):
                    raise Refuse(f"no read-only data of number {k} stands before: {line}")
                cur["piece"] = k
            elif kw == "i":
                pc, nxt = int(parts[1]), int(parts[2])
                cur["instrs"][pc] = (nxt, " ".join(parts[3:]))
            elif kw == "arg":
                if len(parts) == 3 and parts[2] == "number":
                    cur["args"].append((parts[1], "number", None))
                elif len(parts) == 4 and parts[2] == "bytes":
                    cur["args"].append((parts[1], "bytes", parts[3]))
                elif len(parts) == 4 and parts[2] == "out":
                    cur["args"].append((parts[1], "out", parts[3]))
                elif len(parts) == 4 and parts[2] == "fixed":
                    cur["args"].append((parts[1], "fixed", parts[3]))
                elif len(parts) == 4 and parts[2] == "inout":
                    cur["args"].append((parts[1], "inout", parts[3]))
                elif len(parts) == 6 and parts[2] == "valarray":
                    ch, el = int(parts[4]), int(parts[5])
                    if ch <= 0 or el <= 0 or (el % 4) != 0:
                        raise Refuse(f"malformed valarray arg in verify2: {line}")
                    cur["args"].append((parts[1], "valarray", (parts[3], ch, el)))
                else:
                    raise Refuse(f"arg form not handled in verify2: {line}")
            elif kw == "valspec":
                cur["valspecs"].append((parts[1], parts[2], parse_sexpr(" ".join(parts[3:]))))
            elif kw == "ensures":
                rest = line[len("ensures "):].strip()
                run_nm, exprs_txt = rest.split(None, 1)
                es = parse_sexpr("(" + exprs_txt + ")")
                if len(es) != 3:
                    raise Refuse(f"malformed ensures line in verify2: {line}")
                cur["ensures"].append((run_nm, es[0], es[1], es[2]))
            elif kw == "ensuresw":
                run_nm = parts[1]
                if len(parts) >= 5 and parts[2].isdigit() and parts[3].isdigit():
                    part = (int(parts[2]), int(parts[3]))
                    ex = parse_sexpr(" ".join(parts[4:]))
                else:
                    part = None
                    ex = parse_sexpr(" ".join(parts[2:]))
                cur["ensuresw"].append((run_nm, part, ex))
            elif kw == "needs":
                cur["needs"].append(parts[1])
            elif kw == "needsif":
                cur["needsif"].append((parts[1], parts[2], int(parts[3])))
            elif kw == "requires":
                cur["requires"].append(parse_sexpr(line[len("requires "):]))
            elif kw == "below":
                cur["below"].append((parts[1], int(parts[2])))
            elif kw == "mbelow":
                cur["mbounds"].append((parts[1], int(parts[2]), int(parts[3])))
            elif kw == "lanes":
                cur["lanes"].append((parts[1], parts[2]))
            elif kw == "atleast":
                cur["atleast"].append((parts[1], int(parts[2])))
            elif kw == "align":
                al = int(parts[2])
                if al <= 0:
                    raise Refuse(f"malformed align line in verify2: {line}")
                cur["aligns"].append((parts[1], al))
            elif kw == "disjoint":
                ln = int(parts[3])
                if ln <= 0:
                    raise Refuse(f"malformed disjoint line in verify2: {line}")
                cur["disjoint"].append((parts[1], parts[2], ln))
            elif kw == "linpre":
                # `linpre K a1 c1 a2 c2 ...`: the entry condition 0 <= K + c1*a1 + c2*a2 + ...
                if len(parts) % 2 != 0:
                    raise Refuse(f"malformed linpre line in verify2: {line}")
                cur["linpre"].append((int(parts[1]), [(parts[i], int(parts[i + 1])) for i in range(2, len(parts), 2)]))
            elif kw == "returns":
                cur["returns"] = parse_sexpr(line[len("returns "):])
            elif kw == "result":
                cur["result"] = parts[1]
            elif kw == "stack":
                cur["stack"] = int(parts[1])
            elif kw == "stacklin":
                step, arg, sub, div = int(parts[1]), parts[2], int(parts[3]), int(parts[4])
                if div <= 0:
                    raise Refuse(f"malformed stacklin in verify2: {line}")
                cur["stacklin"] = (step, arg, sub, div)
            elif kw == "stackbits":
                step, arg, sub, div = int(parts[1]), parts[2], int(parts[3]), int(parts[4])
                if div <= 0:
                    raise Refuse(f"malformed stackbits in verify2: {line}")
                cur["stackbits"] = (step, arg, sub, div)
            elif kw == "fndecreases":
                cur["decreases"] = parts[1]
            elif kw == "hidden":
                cur["hidden"].update(parts[1:])
            elif kw == "traceexpr":
                cur["trace_exprs"].append(parse_sexpr(line[len("traceexpr "):]))
            elif kw == "resultdep":
                cur["result_dep"] = parts[1:]
            elif kw == "argregs":
                cur["argregs"] = parts[1:]
            elif kw == "keeps":
                cur["keeps"] = parts[1:]
            elif kw == "retreg":
                cur["retreg"] = parts[1]
            elif kw in ("keeps_vec", "keepsvec"):
                cur["keeps_vec"] = parts[1:]
            elif kw == "def":
                eq = line.index(" = ")
                hdr = line[:eq].split()
                defs[hdr[1]] = (hdr[2:], parse_sexpr(line[eq + 3:]))
            else:
                raise Refuse(f"statement line not handled in verify2: {line}")
    return fns, defs


def parse_proof(path):
    proofs = {}
    cur = None
    cur_place = None
    cur_check = None
    cur_p = None
    with open(path, "r", encoding="utf-8") as f:
        for raw in f:
            line = raw.strip()
            if not line:
                continue
            parts = line.split()
            kw = parts[0]
            if kw == "for":
                cur = {"places": {}, "checks": {}, "items": []}
                proofs[parts[1]] = cur
                cur_place = None
                cur_check = None
            elif kw in ("place", "join"):
                pc = int(parts[1])
                cur_place = {"pc": pc, "names": [], "facts": [], "keep": set(), "marked": set(),
                             "marked_result": set(), "decreases": None, "wrote": None,
                             "lanes": [], "cells": [], "is_join": (kw == "join")}
                cur["places"][pc] = cur_place
                cur_check = None
            elif kw == "check":
                pc = int(parts[1])
                cur_check = {"pc": pc, "names": [], "facts": []}
                cur["checks"].setdefault(pc, []).append(cur_check)
                cur_place = None
            elif kw == "name" and cur_check is not None:
                cur_check["names"].append((parts[1], parts[2]))
            elif kw == "fact" and cur_check is not None:
                cur_check["facts"].append(parse_sexpr(line[len("fact "):]))
            elif kw == "name" and cur_place is not None:
                cur_place["names"].append((parts[1], parts[2]))
            elif kw == "fact" and cur_place is not None:
                cur_place["facts"].append(parse_sexpr(line[len("fact "):]))
            elif kw == "keep" and cur_place is not None:
                cur_place["keep"].update(parts[1:])
            elif kw == "marked" and cur_place is not None:
                cur_place["marked"].update(parts[1:])
            elif kw == "marked_result" and cur_place is not None:
                cur_place["marked_result"].update(parts[1:])
            elif kw == "decreases" and cur_place is not None:
                cur_place["decreases"] = parse_sexpr(line[len("decreases "):])
            elif kw == "lane" and cur_place is not None:
                x_var = parts[1]
                eq_i = parts.index("=")
                vregs = []
                for vr_nm in parts[2:eq_i]:
                    vr_i = vec_reg_index(vr_nm)
                    if vr_i is None:
                        raise Refuse(f"invalid vector register `{vr_nm}` in `lane`: {line}")
                    vregs.append(vr_i)
                call_ex = parse_sexpr(" ".join(parts[eq_i + 1:]))
                if not (isinstance(call_ex, tuple) and len(call_ex) >= 2 and call_ex[0] == "call"):
                    raise Refuse(f"malformed `lane` line in verify2: {line}")
                cur_place["lanes"].append((vregs, x_var, call_ex[1], call_ex[2:]))
            elif kw == "cell" and cur_place is not None:
                cur_place["cells"].append((int(parts[1]), parts[2], parse_sexpr(" ".join(parts[3:]))))
            elif kw in ("wrote", "wrote_pre") and cur_place is not None:
                rest = line[len(kw):].strip()
                run_nm, expr_txt = rest.split(None, 1)
                ex = parse_sexpr(expr_txt)
                if not (isinstance(ex, tuple) and len(ex) == 3 and ex[0] == "index"
                        and isinstance(ex[1], tuple) and len(ex[1]) >= 2 and ex[1][0] == "call"):
                    raise Refuse(f"malformed `{kw}` line in verify2: {line}")
                cur_place["wrote"] = (run_nm, ex[2], ex[1][1], ex[1][2:], kw == "wrote_pre")
            elif kw == "t":
                cur_place = None
                cur_check = None
                tag = parts[1]
                arg = int(parts[2]) if len(parts) > 2 else 0
                cur["items"].append(("t", tag, arg))
            elif kw == "k":
                cur_place = None
                cur_check = None
                nums = [int(x) for x in parts[1:]]
                cur["items"].append(("k", (nums[0], _trim(tuple(nums[1:])))))
            elif kw == "p":
                cur_place = None
                cur_check = None
                cur_p = ("p", [int(x) for x in parts[1:]], [])
            elif kw == "r":
                cur_place = None
                cur_check = None
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

    def plain_entail(self, facts, g):
        if not g[1]:
            return g[0] >= 0
        return any(f[1] == g[1] and f[0] <= g[0] for f in facts)

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
        if c1 == c2:
            return
        # Match Core.lean `sameUse`: first check reachability through known `eqs`
        seen = {c1}
        frontier = [c1]
        while frontier:
            cur = frontier.pop()
            if cur == c2:
                return
            for a, b in state["eqs"]:
                if a == cur and b not in seen:
                    seen.add(b)
                    frontier.append(b)
                elif b == cur and a not in seen:
                    seen.add(a)
                    frontier.append(a)
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
            raw_l = self.eval_sexpr(l, env, state, stream)
            raw_r = self.eval_sexpr(r, env, state, stream)
            lv = self.as_num(raw_l, env, state, stream)
            rv = self.as_num(raw_r, env, state, stream)
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
                nn = (not lv[1] and lv[0] >= 0) or (lv in state["facts"])
                q, rem = state["quot_rem"](lv, rv[0], state, nonneg=nn, fold_const=False)
                return rem if bop == "%" else q
            raise Refuse(f"unsupported binary spec op `{bop}`")
        if op == "call":
            fn_nm = e[1]
            raw_args = [self.eval_sexpr(a, env, state, stream) for a in e[2:]]
            # Match Core.lean `.cons`: evaluate args left-to-right, resolve `argumentV` right-to-left
            args = [None] * len(raw_args)
            for idx in range(len(raw_args) - 1, -1, -1):
                a = raw_args[idx]
                if isinstance(a, tuple) and len(a) == 3 and a[0] == "call":
                    args[idx] = self.as_num(a, env, state, stream)
                else:
                    args[idx] = a
            if fn_nm == "len":
                if len(args) == 1 and isinstance(args[0], tuple) and len(args[0]) == 2 and args[0][0] == "buf":
                    return state["buf_len"][args[0][1]]
                if len(e) == 3 and e[2][0] == "name" and e[2][1] in state["buf_len"]:
                    return state["buf_len"][e[2][1]]
                raise Refuse(f"cannot take `len` of {e[2]}")
            if not args and fn_nm in self.defs:
                dparams, dbody = self.defs[fn_nm]
                if not dparams and isinstance(dbody, tuple) and len(dbody) == 2 and dbody[0] == "num":
                    kval = int(dbody[1])
                    if kval >= 0:
                        return r_const(kval)
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
            return state["get_byte"](buf, idx, state, stream)
        if op == "ifx":
            taken = self.eval_cond(e[1], env, state, stream)
            return self.eval_sexpr(e[2] if taken else e[3], env, state, stream)
        raise Refuse(f"unsupported spec expr {e}")

    def eval_cond(self, cond, env, state, stream):
        """Evaluate a specification condition (comparison or nested `ifx` from `&&`/`||`)."""
        if cond[0] == "ifx":
            c_taken = self.eval_cond(cond[1], env, state, stream)
            return self.eval_cond(cond[2] if c_taken else cond[3], env, state, stream)
        if cond[0] != "bin":
            raise Refuse(f"unsupported ifx condition {cond}")
        cop, cl, cr = cond[1], cond[2], cond[3]
        raw_l = self.eval_sexpr(cl, env, state, stream)
        raw_r = self.eval_sexpr(cr, env, state, stream)
        lv = self.as_num(raw_l, env, state, stream)
        rv = self.as_num(raw_r, env, state, stream)
        facts = state["facts"]
        diff = r_sub(lv, rv)
        if cop in ("==", "!=") and (diff in state["neq"] or r_sub(rv, lv) in state["neq"]):
            return cop == "!="
        if not diff[1]:
            k = diff[0]
            if cop == "==": return k == 0
            if cop == "!=": return k != 0
            if cop == "<": return k < 0
            if cop == "<=": return k <= 0
            if cop == ">": return k > 0
            if cop == ">=": return k >= 0
            raise Refuse(f"unsupported ifx op `{cop}`")
        tag, _ = stream.pop_tag()
        if cop in ("<", ">="):
            if tag == "lt":
                self.entail(facts, r_sub(r_sub(rv, lv), r_const(1)), stream)
                return cop == "<"
            if tag == "ge":
                self.entail(facts, r_sub(lv, rv), stream)
                return cop == ">="
            raise Refuse(f"expected `lt`/`ge` for `{cop}`, got `{tag}`")
        if cop in (">", "<="):
            if tag == "lt":
                self.entail(facts, r_sub(r_sub(lv, rv), r_const(1)), stream)
                return cop == ">"
            if tag == "ge":
                self.entail(facts, r_sub(rv, lv), stream)
                return cop == "<="
            raise Refuse(f"expected `lt`/`ge` for `{cop}`, got `{tag}`")
        if tag == "eq":
            self.entail_eq(facts, lv, rv, stream)
            return cop == "=="
        if tag == "lt":
            self.entail(facts, r_sub(r_sub(rv, lv), r_const(1)), stream)
            return cop == "!="
        if tag == "gt":
            self.entail(facts, r_sub(r_sub(lv, rv), r_const(1)), stream)
            return cop == "!="
        raise Refuse(f"expected `eq`/`lt`/`gt` for `{cop}`, got `{tag}`")

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
            if nxt_item is None or nxt_item[0] != "t" or nxt_item[1] not in ("open", "carry", "same"):
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
            if tag == "same":
                ci_idx, cj_idx = idx // 256, idx % 256
                if ci_idx >= len(calls) or cj_idx >= len(calls):
                    raise Refuse(f"`t same {idx}` out of range for {len(calls)} call(s)")
                self.same_call(calls[ci_idx], calls[cj_idx], state, stream)
                eqs.insert(0, (calls[ci_idx], calls[cj_idx]))
                state["eqs"] = eqs
                continue
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

    def assume_fact(self, fact, env, state, stream=None):
        if fact[0] != "bin":
            raise Refuse(f"unsupported assumed fact {fact}")
        op, l, r = fact[1], fact[2], fact[3]
        if op == "==" and (l[0] == "call" or r[0] == "call"):
            # Record symbolic call equality `lhs == rhs` for later substitution
            lv = self.eval_sexpr(l, env, state, stream)
            rv = self.eval_sexpr(r, env, state, stream)
            state["eqs"].insert(0, (lv, rv))
            return
        lv = self.eval_sexpr(l, env, state, stream)
        rv = self.eval_sexpr(r, env, state, stream)
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

        facts = FactList()
        regs = {}
        entry_regs = {}
        reg_to_idx = {r: idx for idx, r in enumerate(reg_names)}
        for r in reg_names:
            v = init_fresh_var(0, M64, facts)
            regs[r] = v
            entry_regs[r] = v
        facts.append(r_sub(regs[sp_reg], r_const(fn["stack"])))
        if not is_arm:
            facts.append(r_sub(r_const(M64 - 8), regs[sp_reg]))
        # Reserve one slot after registers (dataVar, matching Core.lean Sym.init)
        data_var_idx = init_nvars
        data_var_row = init_fresh_var(0, M64, facts)
        pieces = fn.get("pieces", [])
        data_bytes = pieces[fn["piece"]][1] if fn.get("piece") is not None else b""
        if data_bytes:
            facts.append(r_sub(r_const(M64 - len(data_bytes)), data_var_row))

        # Trace marks: True = marked (kept out of trace), False = clean (may show in trace)
        marks = {r: True for r in reg_names}
        marks[sp_reg] = False
        if is_arm:
            marks["x30"] = False

        env = {}
        buf_base = {}
        buf_len = {}
        buf_clean = {}
        out_base = {}
        out_len = {}
        outs_list = []       # [(name, reg_idx, count)] — BOTH `out` and `inout`, matching Contract.outs
        fixeds_list = []     # [(name, reg_idx, count)]
        inouts_list = []     # [(name, reg_idx, count)]
        regions_list = []    # [(base_reg_idx, len_reg_idx)]
        val_arrays_list = [] # [(name, ptr_reg_idx, len_reg_idx, ch, el)]
        arg_reg_idx_by_name = {aname: reg_to_idx[arg_regs[i]] for i, (aname, _, _) in enumerate(fn["args"])}
        for idx, (aname, akind, alen) in enumerate(fn["args"]):
            areg = arg_regs[idx]
            ridx = reg_to_idx[areg]
            if akind == "bytes":
                env[aname] = ("buf", aname)
                buf_base[aname] = regs[areg]
                buf_clean[aname] = aname not in fn["hidden"]
                if alen in arg_reg_idx_by_name:
                    regions_list.append((ridx, arg_reg_idx_by_name[alen]))
            elif akind == "out":
                cnt = int(alen)
                env[aname] = ("out", aname)
                out_base[aname] = regs[areg]
                out_len[aname] = cnt
                outs_list.append((aname, ridx, cnt))
                buf_clean[aname] = True
            elif akind == "inout":
                cnt = int(alen)
                env[aname] = regs[areg]
                out_base[aname] = regs[areg]
                out_len[aname] = cnt
                outs_list.append((aname, ridx, cnt))
                inouts_list.append((aname, ridx, cnt))
                buf_clean[aname] = aname not in fn["hidden"]
            elif akind == "fixed":
                cnt = int(alen)
                env[aname] = regs[areg]
                fixeds_list.append((aname, ridx, cnt))
                buf_clean[aname] = aname not in fn["hidden"]
            elif akind == "valarray":
                l_nm, ch, el = alen
                env[aname] = regs[areg]
                if l_nm in arg_reg_idx_by_name:
                    val_arrays_list.append((aname, ridx, arg_reg_idx_by_name[l_nm], ch, el))
                buf_clean[aname] = aname not in fn["hidden"]
            else:
                env[aname] = regs[areg]
            # Match Contract.cleanAtEntry: every pointer arg register is clean at entry; only hidden numbers are marked
            if aname not in fn["hidden"] or akind != "number":
                marks[areg] = False

        word_runs = (
            list(fixeds_list)
            + list(inouts_list)
            + [("", r, 0) for r, _ in regions_list]
            + [(nm, r, 0) for nm, r, _, _, _ in val_arrays_list]
        )
        lanes_map = dict(fn.get("lanes", ()))
        tables_by_j = {}
        for j_f, (fnm, fr, fcnt) in enumerate(fixeds_list):
            if fnm in lanes_map and lanes_map[fnm] in arg_reg_idx_by_name:
                tables_by_j[j_f] = (fnm, fr, fcnt // 8, arg_reg_idx_by_name[lanes_map[fnm]])

        if fn.get("keeps_vec") is not None:
            callee_saved_vec = [vec_reg_index(v) for v in fn["keeps_vec"] if vec_reg_index(v) is not None]
        else:
            callee_saved_vec = [8, 9, 10, 11, 12, 13, 14, 15] if is_arm else []

        for aname, akind, alen in fn["args"]:
            if akind == "bytes":
                buf_len[aname] = env[alen] if alen in env else r_const(int(alen))
                # Buffer sits in 64-bit address space (`base + len <= 2^64`)
                facts.append(r_sub(r_const(M64 + 1), r_add(buf_base[aname], buf_len[aname])))
            elif akind == "out":
                facts.append(r_sub(r_const(M64 + 1), r_add(out_base[aname], r_const(int(alen)))))
            elif akind in ("fixed", "inout"):
                facts.append(r_sub(r_const(M64 + 1), r_add(env[aname], r_const(int(alen)))))

        if fn["decreases"] is not None:
            dnm = fn["decreases"]
            if dnm not in [a[0] for a in fn["args"]] or dnm in fn["hidden"]:
                raise Refuse("`decreases` argument must be a parameter listed in `trace depends on`")
        if fn["stacklin"] is not None:
            _, sarg, _, sdiv = fn["stacklin"]
            if sdiv <= 0 or sarg not in [a[0] for a in fn["args"]] or sarg in fn["hidden"]:
                raise Refuse("stacklin argument must be a parameter listed in `trace depends on` with positive divisor")
        if fn["stackbits"] is not None:
            _, sarg, _, sdiv = fn["stackbits"]
            if sdiv <= 0 or sarg not in [a[0] for a in fn["args"]] or sarg in fn["hidden"]:
                raise Refuse("stackbits argument must be a parameter listed in `trace depends on` with positive divisor")

        def _bits_nat(n):
            return 0 if n <= 0 else n.bit_length()

        def _check_call_stack(c, sp_off_val, extra, cenv, cur_facts, strm):
            """Match Core.lean `stackFitsMAt` / `stackFitsMLin` / `stackFitsMBits`."""
            if sp_off_val > 0:
                raise Refuse(f"call to `{c['name']}` exceeds stack budget")
            c_sl = c.get("stacklin")
            c_sb = c.get("stackbits")
            p_sl = fn.get("stacklin")
            p_sb = fn.get("stackbits")
            if c_sl is None and c_sb is None:
                if -fn["stack"] <= sp_off_val - extra - c["stack"]:
                    return
                raise Refuse(f"call to `{c['name']}` exceeds stack budget {fn['stack']}")
            if c_sl is not None:
                c_step, c_arg, c_sub, c_div = c_sl
                acal = cenv.get(c_arg)
                if acal is None:
                    raise Refuse(f"stacklin argument `{c_arg}` missing in call to `{c['name']}`")
                if p_sl is None and p_sb is None:
                    rem = fn["stack"] + sp_off_val - extra - c["stack"]
                    if rem < 0:
                        raise Refuse(f"call to `{c['name']}` exceeds stack budget {fn['stack']}")
                    if c_step == 0:
                        return
                    d = rem // c_step
                    need = r_sub(r_const(c_sub + c_div * (d + 1) - 1), acal)
                    if not self.plain_entail(cur_facts, need):
                        self.entail(cur_facts, need, strm)
                    return
                if p_sl is None:
                    raise Refuse(f"call to `{c['name']}` exceeds linear stack budget")
                p_step, p_arg, p_sub, p_div = p_sl
                apar = env.get(p_arg)
                if apar is None or not (c_step <= p_step and c_div == p_div):
                    raise Refuse(f"call to `{c['name']}` exceeds linear stack budget")
                if p_sub <= c_sub and -fn["stack"] <= sp_off_val - extra - c["stack"]:
                    need = r_sub(apar, acal)
                    if not self.plain_entail(cur_facts, need):
                        self.entail(cur_facts, need, strm)
                    return
                if p_sub == c_sub and -fn["stack"] - p_step <= sp_off_val - extra - c["stack"]:
                    n1 = r_sub(r_sub(apar, r_const(c_div)), acal)
                    n2 = r_sub(apar, r_const(c_sub + c_div))
                    if not (self.plain_entail(cur_facts, n1) and self.plain_entail(cur_facts, n2)):
                        self.entail(cur_facts, n1, strm)
                        self.entail(cur_facts, n2, strm)
                    return
                raise Refuse(f"call to `{c['name']}` exceeds linear stack budget")
            # Logarithmic stack budget (`stackbits`)
            c_step, c_arg, c_sub, c_div = c_sb
            acal = cenv.get(c_arg)
            if acal is None or c_div <= 0:
                raise Refuse(f"stackbits argument `{c_arg}` missing in call to `{c['name']}`")
            if p_sl is None and p_sb is None:
                rem = fn["stack"] + sp_off_val - extra - c["stack"]
                if rem < 0:
                    raise Refuse(f"call to `{c['name']}` exceeds stack budget {fn['stack']}")
                d = 63 if c_step == 0 else min(63, rem // c_step)
                need = r_sub(r_const(c_sub + c_div * (1 << d) - 1), acal)
                if not self.plain_entail(cur_facts, need):
                    self.entail(cur_facts, need, strm)
                return
            if p_sb is None:
                raise Refuse(f"call to `{c['name']}` exceeds logarithmic stack budget")
            p_step, p_arg, p_sub, p_div = p_sb
            apar = env.get(p_arg)
            if apar is None or not (c_step <= p_step and p_div > 0):
                raise Refuse(f"call to `{c['name']}` exceeds logarithmic stack budget")
            # Zero-item fast path (`Core.lean:stackFitsAt`): try all `plain` cases before consuming any proof item!
            for d_c in range(64):
                if -fn["stack"] <= sp_off_val - extra - (c["stack"] + c_step * d_c):
                    if self.plain_entail(cur_facts, r_sub(r_const(c_sub + c_div * (1 << d_c) - 1), acal)):
                        return
            if c_div == p_div and p_sub <= c_sub and -fn["stack"] <= sp_off_val - extra - c["stack"]:
                if self.plain_entail(cur_facts, r_sub(apar, acal)):
                    return
            if -fn["stack"] - p_step <= sp_off_val - extra - c["stack"]:
                for d_c in range(64):
                    if (self.plain_entail(cur_facts, r_sub(r_const(c_sub + c_div * (1 << d_c) - 1), acal))
                            and self.plain_entail(cur_facts, r_sub(apar, r_const(p_sub + p_div * (1 << d_c))))):
                        return
                if c_div == p_div and c_sub == p_sub:
                    if (self.plain_entail(cur_facts, r_sub(r_add(apar, r_const(c_sub)), r_scale(2, acal)))
                            and self.plain_entail(cur_facts, r_sub(apar, r_const(c_sub + c_div)))):
                        return
            # Monadic fallback (`Core.lean:stackFitsMBits`)
            if c_div == p_div and p_sub <= c_sub and -fn["stack"] <= sp_off_val - extra - c["stack"]:
                self.entail(cur_facts, r_sub(apar, acal), strm)
                return
            if -fn["stack"] - p_step <= sp_off_val - extra - c["stack"]:
                if not acal[1]:
                    k = acal[0]
                    if k >= 0:
                        d = _bits_nat(max(0, k - c_sub) // c_div)
                        if d < 64:
                            self.entail(cur_facts, r_sub(apar, r_const(p_sub + p_div * (1 << d))), strm)
                            return
                    raise Refuse(f"call to `{c['name']}` exceeds logarithmic stack budget")
                diff_r = r_sub(apar, acal)
                if not diff_r[1]:
                    diff = diff_r[0]
                    if diff > 0 and (diff // c_div) > 0:
                        d = (diff // c_div).bit_length() - 1
                        if d < 64:
                            self.entail(cur_facts, r_sub(r_const(c_sub + c_div * (1 << d) - 1), acal), strm)
                            self.entail(cur_facts, r_sub(apar, r_const(p_sub + p_div * (1 << d))), strm)
                            return
                    raise Refuse(f"call to `{c['name']}` exceeds logarithmic stack budget")
                if c_div == p_div and c_sub == p_sub:
                    self.entail(cur_facts, r_sub(r_add(apar, r_const(c_sub)), r_scale(2, acal)), strm)
                    self.entail(cur_facts, r_sub(apar, r_const(c_sub + c_div)), strm)
                    return
            raise Refuse(f"call to `{c['name']}` exceeds logarithmic stack budget")

        # Stack headroom: `sp >= stack_budget` (at least the constant base `fn["stack"]`)
        if fn["stack"] > 0:
            facts.append(r_sub(regs[sp_reg], r_const(fn["stack"])))

        def get_byte(buf, idx_row, cur_st, strm=None):
            key = (buf, idx_row)
            bc = cur_st["byte_cache"]
            if key not in bc:
                if strm is not None and strm.pos < len(strm.items):
                    nxt = strm.items[strm.pos]
                    if nxt[0] == "t" and nxt[1] == "newbyte":
                        strm.pos += 1
                    elif nxt[0] == "t" and nxt[1] == "samebyte":
                        strm.pos += 1
                        want_v = nxt[2]
                        found = None
                        for (b2, o2), v2 in bc.items():
                            if b2 == buf and v2 == r_var(want_v):
                                found = (o2, v2)
                                break
                        if found is None:
                            raise Refuse(f"samebyte names unknown var v{want_v} not in buffer {buf}")
                        o2, v2 = found
                        self.entail(cur_st["facts"], r_sub(idx_row, o2), strm)
                        self.entail(cur_st["facts"], r_sub(o2, idx_row), strm)
                        if v2 not in cur_st["facts"]:
                            cur_st["facts"].append(v2)
                            cur_st["facts"].append(r_sub(r_const(255), v2))
                        return v2
                bc[key] = fresh_var(cur_st, 0, 255)
            else:
                v = bc[key]
                if v not in cur_st["facts"]:
                    cur_st["facts"].append(v)
                    cur_st["facts"].append(r_sub(r_const(255), v))
            return bc[key]

        def quot_rem(x, m, cur_st, nonneg=False, fold_const=True):
            if fold_const and not x[1]:
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
            if m == W32:
                cur_st["known_div_rem"][r_idx] = x
            return q, rem

        def r_bound_of(facts, row):
            c_r, v_r = row
            neg_v = tuple(-c for c in v_r)
            if isinstance(facts, FactList):
                cf = facts._min.get(neg_v)
                return (cf + c_r) if cf is not None else None
            best = None
            for cf, vf in facts:
                if vf == neg_v:
                    val = cf + c_r
                    if best is None or val < best:
                        best = val
            return best

        def is_word32_row(cur_st, row):
            if not row[1]:
                return 0 <= row[0] < W32
            vi = r_var_idx(row)
            if vi is not None and vi in cur_st["word32_vars"]:
                return True
            return r_plain(cur_st["facts"], row) and r_plain(cur_st["facts"], r_sub(r_const(W32 - 1), row))

        def row_word32_upper(cur_st, row):
            """Pure O(1) upper bound using only `word32_vars` (mirrors Core.lean `rowWord32Upper`)."""
            c0, cs = row
            if c0 < 0 or not cs:
                return None
            wvars = cur_st["word32_vars"]
            tot = c0
            for i, c in enumerate(cs):
                if c == 0:
                    continue
                if c < 0 or i not in wvars:
                    return None
                tot += c * (W32 - 1)
            return tot

        def r_row_upper(facts, row, wvars=()):
            c0, cs = row
            if c0 < 0:
                return None
            total = c0
            for i, c in enumerate(cs):
                if c == 0:
                    continue
                if c < 0:
                    return None
                vi = r_var(i)
                ub = None
                if r_plain(facts, vi):
                    ub = r_bound_of(facts, vi)
                    if ub is None and i in wvars:
                        ub = W32 - 1
                elif i in wvars:
                    ub = W32 - 1
                if ub is None:
                    return None
                total += c * ub
            return total

        def sym_split(facts, x, m, wvars=()):
            c0, cs = x
            q_cs = [c // m if c % m == 0 else 0 for c in cs]
            r_cs = [0 if c % m == 0 else c for c in cs]
            while q_cs and q_cs[-1] == 0:
                q_cs.pop()
            while r_cs and r_cs[-1] == 0:
                r_cs.pop()
            q = (c0 // m, tuple(q_cs))
            r = (c0 % m, tuple(r_cs))
            ub = r_row_upper(facts, r, wvars)
            if ub is not None and ub < m:
                return q, r
            return None

        def sym_low(x, m, cur_st):
            if all(c % m == 0 for c in x[1]):
                return r_const(x[0] % m)
            if m == W32 and is_word32_row(cur_st, x):
                return x
            f = cur_st["facts"]
            if r_plain(f, r_sub(r_const(m - 1), x)):
                return x
            sp = sym_split(f, x, m, cur_st["word32_vars"])
            if sp is not None:
                return sp[1]
            return quot_rem(x, m, cur_st, nonneg=True, fold_const=False)[1]

        def sym_quot(x, m, cur_st):
            if all(c % m == 0 for c in x[1]):
                q_cs = [c // m for c in x[1]]
                while q_cs and q_cs[-1] == 0:
                    q_cs.pop()
                return (x[0] // m, tuple(q_cs))
            sp = sym_split(cur_st["facts"], x, m, cur_st["word32_vars"])
            if sp is not None:
                return sp[0]
            return quot_rem(x, m, cur_st, nonneg=True, fold_const=False)[0]

        state = {
            "nvars": init_nvars,
            "regs": regs,
            "marks": marks,
            "low_clean": set(),
            "flags": {"zf": None, "cf": None},
            "flag_marks": {"zf": True, "cf": True},
            "facts": facts,
            "eqs": [],
            "neq": [],
            "buf_base": buf_base,
            "buf_len": buf_len,
            "buf_clean": buf_clean,
            "out_base": out_base,
            "out_len": out_len,
            "wrote": [],      # list of (out_name, offset_row, byte_val_row)
            "range": None,    # optional (out_name, lo_row, f_name, arg_vals_tuple, from_start)
            "get_byte": get_byte,
            "byte_cache": {},
            "quot_rem": quot_rem,
            "div_cache": {},
            "or_cache": {},
            "stack_mem": {},  # sp_offset -> (val, mark)
            "min_sp": 0,
            # Word / SIMD verification state (independent counterpart to Core.lean `Tab`/`vec`/`wroteW`)
            "tab": WordTab(),
            "vec": {},            # vec_reg (0..39) -> tuple of 4 or 16 word term IDs
            "vec_intact": set(callee_saved_vec),
            "wroteW": {},         # (out_w_idx, word_k) -> term_id
            "intact": set(range(len(outs_list))),
            "frameW": {},         # sp_offset -> term_id (4-byte stack word slots)
            "spill": {},          # frame_offset_row -> tuple of 16 term IDs (aligned 64B stack cells)
            "word32_vars": set(), # variable indices in [0, 2^32)
            "term_val_to_var": {},
            "var_to_term": {},
            "known_load": {},     # (fixed_j, byte_c) -> var_idx
            "known_load_of": {},  # var_idx -> (fixed_j, byte_c)
            "known_div_rem": {},  # rem_var_idx -> dividend_row (for m == 2^32)
            "known_block": [],    # [(j, c, off_row, vs_list)]
            "known_held": KnownMap(),     # (f, keys) -> ids
            "known_held_b": KnownMap(),   # (f, keys) -> ids
            "known_use": KnownMap(),      # (f, keys) -> h
            "known_record": [],   # [(h, fields, ids)]
            "stack_at": None,
        }

        for _, vr, vl, vch, vel in val_arrays_list:
            q_va, _ = quot_rem(r_var(vl), vch, state, nonneg=True, fold_const=False)
            state["facts"].append(r_sub(r_const(M64), r_add(r_var(vr), r_scale(vel, q_va))))
        slot_sz = 0 if is_arm else 8
        for _, _, cnt8, l_idx in tables_by_j.values():
            if cnt8 > 0 and fn["stack"] + slot_sz > 0:
                state["facts"].append(r_sub(r_const((1 << 64) - 64), r_scale(64, r_var(l_idx))))

        for aname, bound in fn["below"]:
            if aname in env:
                facts.append(r_sub(r_const(bound - 1), env[aname]))
        for aname, bound in fn["atleast"]:
            if aname in env:
                facts.append(r_sub(env[aname], r_const(bound)))
        # Entry alignment moduli per variable index (mirrors Core.lean `isAligned`).
        arg_to_reg = {aname: arg_regs[idx] for idx, (aname, _, _) in enumerate(fn["args"])}
        align_vars = {}
        for aname, al in fn["aligns"]:
            if aname in arg_to_reg:
                ev_row = entry_regs[arg_to_reg[aname]]
                if ev_row[0] == 0 and len(ev_row[1]) >= 1 and ev_row[1][-1] == 1 and all(c == 0 for c in ev_row[1][:-1]):
                    align_vars.setdefault(len(ev_row[1]) - 1, []).append(al)
        if is_arm:
            sp_row = entry_regs[sp_reg]
            if sp_row[0] == 0 and len(sp_row[1]) >= 1 and sp_row[1][-1] == 1 and all(c == 0 for c in sp_row[1][:-1]):
                align_vars.setdefault(len(sp_row[1]) - 1, []).append(16)

        def _is_aligned(row, al):
            if al <= 0 or (row[0] % al) != 0:
                return False
            for vi, ci in enumerate(row[1]):
                if ci % al == 0:
                    continue
                if any(a0 > 0 and a0 % al == 0 for a0 in align_vars.get(vi, ())):
                    continue
                return False
            return True

        def _span_row(contract, c_regs, reg_map, nm):
            reg_by_name = {a: c_regs[i] for i, (a, _, _) in enumerate(contract["args"])}
            for i, (a, k, alen) in enumerate(contract["args"]):
                if a == nm:
                    r = c_regs[i]
                    if k == "bytes":
                        rl = reg_by_name.get(alen)
                        return (reg_map[r], reg_map[rl]) if rl is not None else None
                    if k in ("out", "fixed", "inout"):
                        return (reg_map[r], r_const(int(alen)))
                    return None
            return None

        def _valarray_at(contract, c_regs, nm):
            reg_by_name = {a: c_regs[i] for i, (a, _, _) in enumerate(contract["args"])}
            for i, (a, k, alen) in enumerate(contract["args"]):
                if a == nm:
                    if k == "valarray":
                        len_nm, ch, el = alen
                        rl = reg_by_name.get(len_nm)
                        return (c_regs[i], rl, int(ch), int(el)) if rl is not None else None
                    return None
            return None

        def _row_const_diff(row, base_row):
            d = r_sub(row, base_row)
            return d[0] if not d[1] else None

        def _in_frame_span(st, b, l):
            sp_diff = _row_const_diff(st["regs"][sp_reg], entry_regs[sp_reg])
            cf = _row_const_diff(b, entry_regs[sp_reg])
            if sp_diff is None or cf is None:
                return False
            return sp_diff <= cf and r_plain(st["facts"], r_sub(r_const(-cf), l))

        def _sub_span_of(st, b, l, nm):
            su = _span_row(fn, arg_regs, entry_regs, nm)
            if su is None:
                return False
            bu, lu = su
            return r_plain(st["facts"], r_sub(b, bu)) and r_plain(st["facts"], r_sub(r_add(bu, lu), r_add(b, l)))

        def _any_buf_sub_span(st, b, l):
            for a, k, _ in fn["args"]:
                if k in ("bytes", "out", "fixed", "inout") and _sub_span_of(st, b, l, a):
                    return True
            return False

        def _disjoint_pair_ok(st, bx, lx, by_, ly, L):
            if (not lx[1] and lx[0] == 0) or (not ly[1] and ly[0] == 0):
                return True
            if _is_aligned(by_, L) and r_plain(st["facts"], r_sub(by_, r_add(bx, lx))):
                return True
            if _is_aligned(bx, L) and r_plain(st["facts"], r_sub(bx, r_add(by_, ly))):
                return True
            if L == 1 and (
                (_in_frame_span(st, bx, lx) and _any_buf_sub_span(st, by_, ly))
                or (_in_frame_span(st, by_, ly) and _any_buf_sub_span(st, bx, lx))
            ):
                return True
            for u, v, Lp in fn["disjoint"]:
                if Lp <= 0 or (Lp % L) != 0:
                    continue
                if (_sub_span_of(st, bx, lx, u) and _sub_span_of(st, by_, ly, v)) or (
                    _sub_span_of(st, bx, lx, v) and _sub_span_of(st, by_, ly, u)
                ):
                    return True
            return False

        def _valarray_span_disjoint_ok(c, c_arg_regs, st, va_name, by_, ly, L):
            va = _valarray_at(c, c_arg_regs, va_name)
            if va is None:
                return False
            rx, rl, ch, el = va
            if not (ch > 0 and el > 0):
                return False
            if not ly[1] and ly[0] == 0:
                return True
            # Slice of caller valArray
            for x0, r0, l0, ch0, el0 in val_arrays_list:
                d = _row_const_diff(st["regs"][rx], r_var(r0))
                if d is not None and d >= 0 and (d % 4) == 0:
                    va0 = _valarray_at(fn, arg_regs, x0)
                    if (
                        va0 is not None
                        and (reg_to_idx[va0[0]], reg_to_idx[va0[1]], va0[2], va0[3]) == (r0, l0, ch0, el0)
                        and ch == ch0
                        and el == el0
                        and (d % el) == 0
                        and r_plain(st["facts"], r_sub(r_var(l0), r_add(r_const((d // el) * ch), st["regs"][rl])))
                    ):
                        if L == 1 and _in_frame_span(st, by_, ly):
                            return True
                        for u, v, Lp in fn["disjoint"]:
                            if Lp <= 0 or (Lp % L) != 0:
                                continue
                            if (u == x0 and _sub_span_of(st, by_, ly, v)) or (v == x0 and _sub_span_of(st, by_, ly, u)):
                                return True
                    break
            # Frame-backed valArray (L == 1)
            if L == 1:
                sp_diff = _row_const_diff(st["regs"][sp_reg], entry_regs[sp_reg])
                cf = _row_const_diff(st["regs"][rx], entry_regs[sp_reg])
                if sp_diff is not None and cf is not None and sp_diff <= cf <= 0:
                    max_fit = (-cf) // el
                    fits_frame = r_plain(st["facts"], r_sub(r_const((max_fit + 1) * ch - 1), st["regs"][rl]))
                    if fits_frame and _any_buf_sub_span(st, by_, ly):
                        return True
                    cf2 = _row_const_diff(by_, entry_regs[sp_reg])
                    if cf2 is not None:
                        if fits_frame and sp_diff <= cf2 and r_plain(st["facts"], r_sub(r_const(cf - cf2), ly)):
                            return True
                        if cf <= cf2 <= 0:
                            max_below = (cf2 - cf) // el
                            if r_plain(st["facts"], r_sub(r_const((max_below + 1) * ch - 1), st["regs"][rl])):
                                return True
            return False

        def _check_call_align_ld(c, c_arg_regs, st):
            c_reg_by_name = {a: c_arg_regs[i] for i, (a, _, _) in enumerate(c["args"])}
            for x, al in c["aligns"]:
                if al <= 0:
                    continue
                r = c_reg_by_name.get(x)
                if r is not None and not _is_aligned(st["regs"][r], al):
                    raise Refuse(f"argument `{x}` is not shown to be {al}-byte aligned")
            for x, y, L in c["disjoint"]:
                if L <= 0:
                    continue
                sx = _span_row(c, c_arg_regs, st["regs"], x)
                sy = _span_row(c, c_arg_regs, st["regs"], y)
                if sx is not None and sy is not None:
                    if not _disjoint_pair_ok(st, sx[0], sx[1], sy[0], sy[1], L):
                        raise Refuse(f"arguments `{x}` and `{y}` are not shown to be {L}-byte disjoint")
                elif sx is None and sy is not None:
                    if x in c_reg_by_name and y in c_reg_by_name:
                        if not _valarray_span_disjoint_ok(c, c_arg_regs, st, x, sy[0], sy[1], L):
                            raise Refuse(f"arguments `{x}` and `{y}` are not shown to be {L}-byte disjoint")
                elif sx is not None and sy is None:
                    if x in c_reg_by_name and y in c_reg_by_name:
                        if not _valarray_span_disjoint_ok(c, c_arg_regs, st, y, sx[0], sx[1], L):
                            raise Refuse(f"arguments `{x}` and `{y}` are not shown to be {L}-byte disjoint")
                else:
                    if x in c_reg_by_name and y in c_reg_by_name:
                        raise Refuse(f"arguments `{x}` and `{y}` have extents not handled for {L}-byte disjointness")
        for k, terms in fn["linpre"]:
            facts.append(self.linpre_row(k, terms, env))
        for req in fn["requires"]:
            self.assume_fact(req, env, state)

        stream = Stream(proof["items"])
        places = proof["places"]
        checks = proof.get("checks", {})

        def clone(st):
            return {
                "nvars": st["nvars"],
                "regs": dict(st["regs"]),
                "marks": dict(st["marks"]),
                "low_clean": set(st["low_clean"]),
                "flags": dict(st["flags"]),
                "flag_marks": dict(st["flag_marks"]),
                "facts": st["facts"].copy(),
                "eqs": list(st["eqs"]),
                "neq": list(st["neq"]),
                "buf_base": st["buf_base"],
                "buf_len": st["buf_len"],
                "buf_clean": st["buf_clean"],
                "out_base": st["out_base"],
                "out_len": st["out_len"],
                "wrote": list(st["wrote"]),
                "range": st["range"],
                "get_byte": st["get_byte"],
                "byte_cache": dict(st["byte_cache"]),
                "quot_rem": st["quot_rem"],
                "div_cache": dict(st["div_cache"]),
                "or_cache": dict(st["or_cache"]),
                "stack_mem": dict(st["stack_mem"]),
                "min_sp": st["min_sp"],
                "place_entry_regs": st.get("place_entry_regs", {}),
                "place_entry_fq": st.get("place_entry_fq", frozenset()),
                "tab": st["tab"].clone(),
                "vec": dict(st["vec"]),
                "vec_intact": set(st["vec_intact"]),
                "wroteW": dict(st["wroteW"]),
                "intact": set(st["intact"]),
                "frameW": dict(st["frameW"]),
                "spill": dict(st["spill"]),
                "word32_vars": set(st["word32_vars"]),
                "term_val_to_var": dict(st["term_val_to_var"]),
                "var_to_term": dict(st["var_to_term"]),
                "known_load": dict(st["known_load"]),
                "known_load_of": dict(st["known_load_of"]),
                "known_div_rem": dict(st["known_div_rem"]),
                "known_block": list(st["known_block"]),
                "known_held": st["known_held"].copy(),
                "known_held_b": st["known_held_b"].copy(),
                "known_use": st["known_use"].copy(),
                "known_record": list(st["known_record"]),
                "stack_at": st.get("stack_at"),
            }

        # ---------------------------------------------------------------
        # Word-level & SIMD helpers (independent Python verification)
        # ---------------------------------------------------------------

        def _data_off(addr):
            if not data_bytes:
                return None
            d = r_sub(addr, data_var_row)
            return d[0] if not d[1] else None

        def _data_word(c, size):
            val = 0
            for k in range(size):
                val |= data_bytes[c + k] << (8 * k)
            return val

        def _find_in_runs(addr, runs):
            for idx_r, (_, r_idx, cnt) in enumerate(runs):
                if r_idx < len(addr[1]) and addr[1][r_idx] == 1:
                    return idx_r, r_sub(addr, r_var(r_idx)), cnt
            return None

        def _run_at(r_idx, runs):
            for j, (_, ri, _) in enumerate(runs):
                if ri == r_idx:
                    return j
            return None

        def _cur_sp_off(st):
            d = r_sub(st["regs"][sp_reg], entry_regs[sp_reg])
            return d[0] if not d[1] else None

        def _val_of_term(st, tid):
            tab = st["tab"]
            if 0 <= tid < len(tab.arr) and tab.arr[tid][0] == "atom":
                r = tab.arr[tid][1]
                if is_word32_row(st, r):
                    return r
            if tid in st["term_val_to_var"]:
                return r_var(st["term_val_to_var"][tid])
            v = st["nvars"]
            st["nvars"] += 1
            st["word32_vars"].add(v)
            st["term_val_to_var"][tid] = v
            st["var_to_term"][v] = tid
            return r_var(v)

        def _sym_touch(st, w):
            if w not in st["intact"]:
                return
            nm, b, n = outs_list[w]
            if (nm, b, n) in inouts_list and (n % 4) == 0:
                j = _run_at(b, word_runs)
                if j is not None:
                    tab = st["tab"]
                    for k in range(n // 4):
                        st["wroteW"][(w, k)] = tab.intern(("input", j, k))
                    st["intact"].discard(w)

        def _remember_store(st, w, word_j, ids):
            st["intact"].discard(w)
            st["spill"] = {}
            st["range"] = None
            for i, tid in enumerate(ids):
                st["wroteW"][(w, word_j + i)] = tid

        def _sym_load_words(st, addr, width):
            tab = st["tab"]
            # 1. Fixed read-only word runs
            mf = _find_in_runs(addr, fixeds_list)
            if mf is not None:
                j, off, cnt = mf
                if off[1]:
                    raise Refuse("word load at non-constant fixed buffer offset")
                c = off[0]
                if 0 <= c and (c % 4) == 0 and c + 4 * width <= cnt:
                    return tuple(tab.intern(("input", j, c // 4 + i)) for i in range(width))
                raise Refuse("word load outside fixed buffer or misaligned")
            # 2. Out / in-out word runs (pure write-only `out` is refused!)
            mo = _find_in_runs(addr, outs_list)
            if mo is not None:
                w, off, n = mo
                if off[1]:
                    raise Refuse("word load at non-constant output buffer offset")
                c = off[0]
                _, r_idx, _ = outs_list[w]
                j = _run_at(r_idx, fixeds_list + inouts_list)
                if j is None:
                    raise Refuse("a read of a run given only to write")
                n_in = (fixeds_list + inouts_list)[j][2]
                if not (0 <= c and (c % 4) == 0 and c + 4 * width <= n and c + 4 * width <= n_in):
                    raise Refuse("word load outside in-out buffer or misaligned")
                if w in st["intact"]:
                    return tuple(tab.intern(("input", j, c // 4 + i)) for i in range(width))
                ids = []
                for i in range(width):
                    key = (w, c // 4 + i)
                    if key not in st["wroteW"]:
                        raise Refuse("a part not written yet is read after a partial store")
                    ids.append(st["wroteW"][key])
                return tuple(ids)
            # 3. Stack frame (8-byte cells in `stack_mem`, `known_load` spilled cells, or 4-byte `frameW`)
            fo = r_sub(addr, entry_regs[sp_reg])
            sp_c = _cur_sp_off(st)
            if (not fo[1]) and sp_c is not None:
                o = fo[0]
                if sp_c <= o and o + 4 * width <= 0:
                    if (width % 2) == 0:
                        rows = []
                        ok_rows = True
                        for p in range(width // 2):
                            cell = st["stack_mem"].get(o + 8 * p)
                            if cell is None or not is_word32_row(st, r_word(cell[0])):
                                ok_rows = False
                                break
                            rows.append(cell[0])
                            rows.append(r_high(cell[0]))
                        if ok_rows:
                            return tuple(tab.w_atom_k(st["known_div_rem"], st["var_to_term"], r) for r in rows)
                        nodes = []
                        ok_nodes = True
                        for p in range(width // 2):
                            cell = st["stack_mem"].get(o + 8 * p)
                            if cell is None:
                                ok_nodes = False
                                break
                            vi = r_var_idx(cell[0])
                            if vi is None or vi not in st["known_load_of"]:
                                ok_nodes = False
                                break
                            fj, c0 = st["known_load_of"][vi]
                            if (c0 % 4) != 0:
                                ok_nodes = False
                                break
                            nodes.append(("input", fj, c0 // 4))
                            nodes.append(("input", fj, c0 // 4 + 1))
                        if ok_nodes:
                            return tuple(tab.intern(nd) for nd in nodes)
                    if all((o + 4 * k) in st["frameW"] for k in range(width)):
                        return tuple(st["frameW"][o + 4 * k] for k in range(width))
                    raise Refuse("stack frame word load where words are not known")
                raise Refuse("word load outside stack frame")
            # 4. Read-only value arrays
            for k_va, (_, r_idx, l_idx, ch, el) in enumerate(val_arrays_list):
                d = r_sub(addr, r_var(r_idx))
                if not d[1] and d[0] >= 0 and (d[0] % 4) == 0:
                    c = d[0]
                    ei = c // el
                    if ch > 0 and el > 0 and (el % 4) == 0 and c + 4 * width <= el * (ei + 1):
                        self.entail(st["facts"], r_sub(r_var(l_idx), r_const((ei + 1) * ch)), stream)
                        j = len(fixeds_list) + len(inouts_list) + len(regions_list) + k_va
                        return tuple(tab.intern(("input", j, c // 4 + m)) for m in range(width))
                    raise Refuse("word load outside value-array entry")
            raise Refuse("word load address does not fall in any readable word buffer or stack frame")

        def _sym_load_word_scalar(st, addr, size):
            if size == 4:
                ids = _sym_load_words(st, addr, 1)
                return _val_of_term(st, ids[0])
            if size == 8:
                ids = _sym_load_words(st, addr, 2)
                r0 = _val_of_term(st, ids[0])
                r1 = _val_of_term(st, ids[1])
                return r_add(r0, r_scale(W32, r1))
            raise Refuse("word-backed scalar load must be 4 or 8 bytes")

        def _sym_store_words(st, addr, ids, width):
            if len(ids) != width:
                raise Refuse("vector store width does not match known lanes")
            mo = _find_in_runs(addr, outs_list)
            if mo is not None:
                w, off, cnt = mo
                if off[1]:
                    raise Refuse("word store at non-constant output buffer offset")
                c = off[0]
                if not (0 <= c and (c % 4) == 0 and c + 4 * width <= cnt):
                    raise Refuse("word store outside output buffer or misaligned")
                onm = outs_list[w][0]
                if any(wn == onm for wn, _, _ in st["wrote"]):
                    raise Refuse("words written to a run that single bytes were written to")
                _remember_store(st, w, c // 4, ids)
                return
            fo = r_sub(addr, entry_regs[sp_reg])
            sp_c = _cur_sp_off(st)
            if (not fo[1]) and sp_c is not None:
                o = fo[0]
                if -fn["stack"] <= o and sp_c <= o and o + 4 * width <= 0:
                    st["spill"] = {}
                    st["range"] = None
                    st["stack_mem"] = {
                        c: v for c, v in st["stack_mem"].items()
                        if c + 8 <= o or o + 4 * width <= c
                    }
                    st["frameW"] = {
                        c: v for c, v in st["frameW"].items()
                        if c + 4 <= o or o + 4 * width <= c
                    }
                    for k, tid in enumerate(ids):
                        st["frameW"][o + 4 * k] = tid
                    return
            raise Refuse("word store address does not fall in an output buffer or active stack frame")

        def _sym_store4(st, addr, val):
            mo = _find_in_runs(addr, outs_list)
            if mo is not None:
                _sym_touch(st, mo[0])
            lo = st["tab"].w_atom_k(st["known_div_rem"], st["var_to_term"], val)
            _sym_store_words(st, addr, (lo,), 1)

        def _sym_store8_out(st, w, cnt, off, val):
            if off[1]:
                raise Refuse("8-byte output store at non-constant offset")
            c = off[0]
            onm = outs_list[w][0]
            if not (0 <= c and (c % 4) == 0 and c + 8 <= cnt) or any(wn == onm for wn, _, _ in st["wrote"]):
                raise Refuse("8-byte store outside output buffer, misaligned, or mixed with byte stores")
            _sym_touch(st, w)
            if r_has_high(val) and is_word32_row(st, r_word(val)):
                lo = st["tab"].w_atom_k(st["known_div_rem"], st["var_to_term"], val)
                hi = st["tab"].w_atom_k(st["known_div_rem"], st["var_to_term"], r_high(val))
            else:
                q, _ = quot_rem(val, W32, st, nonneg=True, fold_const=False)
                lo = st["tab"].w_atom_k(st["known_div_rem"], st["var_to_term"], val)
                hi = st["tab"].w_atom_k(st["known_div_rem"], st["var_to_term"], q)
            _remember_store(st, w, c // 4, (lo, hi))

        def _sym_halves(st, x):
            tab = st["tab"]
            if r_high(x) == (0, ()) and x[1]:
                q, rem = quot_rem(x, W32, st, nonneg=True, fold_const=False)
                return tuple(tab.w_atom_k(st["known_div_rem"], st["var_to_term"], r) for r in (rem, q, (0, ()), (0, ())))
            if not is_word32_row(st, r_word(x)):
                self.entail(st["facts"], r_word(x), stream)
                self.entail(st["facts"], r_sub(r_const(W32 - 1), r_word(x)), stream)
            return tuple(tab.w_atom_k(st["known_div_rem"], st["var_to_term"], r) for r in (x, r_high(x), (0, ()), (0, ())))

        def _vec_of(bind, nm):
            if nm == "xmm0":
                return 0
            if nm in tab_mod.VECTORS and nm in bind:
                r = int(bind[nm])
                if 0 <= r < 32:
                    return r
            return None

        def _vec_of_512(bind, nm):
            if nm in tab_mod.WIDE:
                return _vec_of(bind, tab_mod.WIDE[nm])
            if nm == "M" and "M" in bind:
                m = int(bind["M"])
                if 0 < m < 8:
                    return 32 + m
            return None

        def _sym_number(bind, ex):
            if ex[0] == "number":
                return ex[1] if 0 <= ex[1] < (1 << 64) else None
            if ex[0] == "name" and ex[1] in tab_mod.NUMBERS and ex[1] in bind:
                v = bind[ex[1]]
                iv = int(v, 0) if isinstance(v, str) else int(v)
                return iv % (1 << 64)
            return None

        def _sym_reg_val(bind, st, ex):
            if ex[0] == "name" and ex[1] not in tab_mod.NUMBERS:
                r = bind.get(ex[1], ex[1])
                if r in st["regs"]:
                    return st["regs"][r], st["marks"][r]
                return None
            if ex[0] == "call" and ex[1] == "on16" and len(ex[2]) == 1 and ex[2][0][0] == "name":
                r = bind.get(ex[2][0][1], ex[2][0][1])
                if r in st["regs"]:
                    x = st["regs"][r]
                    d = r_sub(x, entry_regs[sp_reg])
                    if is_arm and (not d[1]) and (d[0] % 16) == 0:
                        return x, st["marks"][r]
                    raise Refuse("stack pointer is not shown to be 16-byte aligned for on16")
            return None

        def _sym_word_addr(bind, st, args):
            if len(args) == 2:
                rv = _sym_reg_val(bind, st, args[0])
                k = _sym_number(bind, args[1])
                if rv is None or k is None:
                    raise Refuse("word address needs a base register and displacement")
                if rv[1]:
                    raise Refuse("word memory address depends on values kept out of the trace")
                return r_add(r_signed(rv[0]), r_signed(r_const(k)))
            if len(args) == 3:
                rv = _sym_reg_val(bind, st, args[0])
                k = _sym_number(bind, args[1])
                iv = _sym_reg_val(bind, st, args[2])
                if rv is None or k is None or iv is None:
                    raise Refuse("indexed word address needs base, displacement, and index")
                if rv[1] or iv[1]:
                    raise Refuse("word memory address depends on values kept out of the trace")
                return r_add(r_add(r_signed(rv[0]), r_signed(r_const(k))), r_signed(iv[0]))
            raise Refuse("word address needs 2 or 3 operands")

        def _frame_span_goals(st, a, size):
            o = r_sub(a, entry_regs[sp_reg])
            return [r_sub(a, st["regs"][sp_reg]), r_add(o, r_const(fn["stack"])), r_sub(r_const(-size), o)]

        def _aligned64(a):
            return (a[0] % 64) == 0 and all((c % 64) == 0 for c in a[1])

        def _cells_apart(o1, o2):
            return o1[1] == o2[1] and (o1[0] + 64 <= o2[0] or o2[0] + 64 <= o1[0])

        def _sym_spill_load(bind, st, args):
            a = _sym_word_addr(bind, st, args)
            fo = r_sub(a, entry_regs[sp_reg])
            if fo not in st["spill"]:
                raise Refuse("aligned 512-bit load does not match a saved stack vector")
            if not _aligned64(a):
                raise Refuse("aligned 512-bit load address is not 64-byte aligned")
            for g in _frame_span_goals(st, a, 64):
                self.entail(st["facts"], g, stream)
            return st["spill"][fo]

        def _sym_spill_store(bind, st, args, lanes):
            a = _sym_word_addr(bind, st, args)
            if not _aligned64(a):
                raise Refuse("aligned 512-bit store address is not 64-byte aligned")
            fo = r_sub(a, entry_regs[sp_reg])
            for g in _frame_span_goals(st, a, 64):
                self.entail(st["facts"], g, stream)
            for so in st["stack_mem"]:
                self.entail(st["facts"], r_sub(r_const(so - 64), fo), stream)
            st["range"] = None
            st["frameW"] = {}
            st["spill"] = {k: v for k, v in st["spill"].items() if _cells_apart(k, fo)}
            st["spill"][fo] = tuple(lanes)

        def _find_lane(addr, st):
            for (fj, p), v in st["known_load"].items():
                if fj in tables_by_j and v < len(addr[1]) and addr[1][v] == 1:
                    _, _, _, l_idx = tables_by_j[fj]
                    return v, fj, p, l_idx
            return None

        def _sym_load_block(st, v, j, p, l_idx, addr):
            if (p % 8) != 0:
                raise Refuse("block load through address not aligned in lane table")
            off = r_sub(addr, r_var(v))
            self.entail(st["facts"], off, stream)
            self.entail(st["facts"], r_sub(r_sub(r_scale(64, r_var(l_idx)), r_const(64)), off), stream)
            vs = [st["nvars"] + i for i in range(16)]
            st["nvars"] += 16
            tab = st["tab"]
            ids = tuple(tab.w_atom(r_var(vi)) for vi in vs)
            st["known_block"].insert(0, (j, p, off, vs))
            return ids

        def _sym_mem512(bind, st, op, args):
            if op == "mem512":
                a = _sym_word_addr(bind, st, args)
                fl = _find_lane(a, st)
                if fl is not None:
                    return _sym_load_block(st, fl[0], fl[1], fl[2], fl[3], a)
                fo = r_sub(a, entry_regs[sp_reg])
                if fo in st["spill"]:
                    for g in _frame_span_goals(st, a, 64):
                        self.entail(st["facts"], g, stream)
                    return st["spill"][fo]
                return _sym_load_words(st, a, 16)
            if op == "mem512a":
                return _sym_spill_load(bind, st, args)
            raise Refuse(f"512-bit memory op `{op}` not handled")

        def _sym_vec4(bind, st, ex):
            if ex[0] == "name":
                r = _vec_of(bind, ex[1])
                if r is not None and r in st["vec"] and len(st["vec"][r]) >= 4:
                    return st["vec"][r][:4]
            return None

        def _sym_vec16(bind, st, ex):
            if ex[0] == "name":
                r = _vec_of_512(bind, ex[1])
                if r is not None and r in st["vec"] and len(st["vec"][r]) == 16:
                    return st["vec"][r]
            return None

        def _eval_vec128(ex, bind, st):
            tab = st["tab"]
            if ex[0] == "name":
                l = _sym_vec4(bind, st, ex)
                if l is None:
                    raise Refuse("128-bit vector register has unknown words")
                return l
            if ex[0] != "call":
                raise Refuse(f"128-bit vector expression `{ex}` not handled")
            f, args = ex[1], ex[2]
            if f == "mem128":
                return _sym_load_words(st, _sym_word_addr(bind, st, args), 4)
            if f == "words":
                if len(args) != 4:
                    raise Refuse("`words` expects four constants")
                ks = [_sym_number(bind, a) for a in args]
                if any(k is None for k in ks):
                    raise Refuse("`words` operand is not a constant")
                return tuple(tab.w_atom(r_const(k)) for k in ks)
            if f == "lanes_of64":
                if len(args) != 1:
                    raise Refuse("`lanes_of64` expects one register")
                rv = _sym_reg_val(bind, st, args[0])
                if rv is None:
                    raise Refuse("`lanes_of64` operand is not a general register")
                return _sym_halves(st, rv[0])
            if f == "lanes":
                if len(args) != 4:
                    raise Refuse("`lanes` expects four lane selections")
                out = []
                for a in args:
                    if a[0] != "lane" or a[2] >= 4:
                        raise Refuse("invalid lane selector")
                    vr = _vec_of(bind, a[1])
                    if vr is None or vr not in st["vec"] or a[2] >= len(st["vec"][vr]):
                        raise Refuse("lane of unknown vector register")
                    out.append(st["vec"][vr][a[2]])
                return tuple(out)
            if f == "each32":
                if len(args) != 3 or args[0][0] != "name":
                    raise Refuse("malformed `each32`")
                op = args[0][1]
                x = _sym_vec4(bind, st, args[1])
                if x is None:
                    raise Refuse("`each32` source vector has unknown words")
                y = _sym_vec4(bind, st, args[2])
                if y is not None:
                    if op == "add32":
                        return tuple(tab.w_add(a, b) for a, b in zip(x, y))
                    if op == "xor32":
                        return tuple(tab.w_xor(a, b) for a, b in zip(x, y))
                    if op == "and32":
                        return tuple(tab.w_and(a, b) for a, b in zip(x, y))
                    if op == "or32":
                        if x == y:
                            return x
                        turns = tab.or_turns(list(zip(x, y)))
                        if turns is None:
                            raise Refuse("vector `or32` is not a word rotation")
                        return tuple(tab.w_rotr(a, n) for a, n in turns)
                    raise Refuse(f"128-bit `each32` op `{op}` not handled")
                n = _sym_number(bind, args[2])
                if n is None:
                    raise Refuse("`each32` second operand has unknown words")
                if op == "ror32":
                    return tuple(tab.w_rotr(a, n % 32) for a in x)
                if op == "shl32":
                    return tuple(tab.w_shl(a, n) for a in x)
                if op == "shr32":
                    return tuple(tab.w_shr(a, n) for a in x)
                raise Refuse(f"128-bit immediate `each32` op `{op}` not handled")
            if f == "shuffle_bytes" and len(args) == 2:
                x = _sym_vec4(bind, st, args[0])
                y = _sym_vec4(bind, st, args[1])
                if x is None or y is None:
                    raise Refuse("`shuffle_bytes` vector has unknown words")
                ks = tab.const_words(y)
                turn = tab.shuffle_turn(ks) if ks is not None else None
                if turn is None:
                    raise Refuse("`shuffle_bytes` is not an 8-bit or 16-bit word rotation")
                return tuple(tab.w_rotr(a, turn) for a in x)
            if f in ("sha256msg1", "sha256msg2") and len(args) == 2:
                x = _sym_vec4(bind, st, args[0])
                y = _sym_vec4(bind, st, args[1])
                if x is None or y is None:
                    raise Refuse(f"`{f}` vector has unknown words")
                return tab.w_sha256_msg1(x, y) if f == "sha256msg1" else tab.w_sha256_msg2(x, y)
            if f in ("sha256su1", "sha256rnds2", "sha256h", "sha256h2") and len(args) == 3:
                x = _sym_vec4(bind, st, args[0])
                y = _sym_vec4(bind, st, args[1])
                z = _sym_vec4(bind, st, args[2])
                if x is None or y is None or z is None:
                    raise Refuse(f"`{f}` vector has unknown words")
                if f == "sha256su1":
                    return tab.w_sha256_su1(x, y, z)
                if f == "sha256rnds2":
                    return tab.w_sha256_rnds2(x, y, z)
                if f == "sha256h":
                    return tab.w_sha256_h(x, y, z)
                return tab.w_sha256_h2(x, y, z)
            if f in ("pick4", "blend4", "blend_halves") and len(args) == 3:
                x = _sym_vec4(bind, st, args[0])
                y = _sym_vec4(bind, st, args[1])
                imm = _sym_number(bind, args[2])
                if x is None or y is None or imm is None:
                    raise Refuse(f"`{f}` needs two known vectors and an immediate")
                if f == "pick4":
                    return tab_mod.MOVES["pick4"](x, y, imm)
                if f == "blend4":
                    return tab_mod.MOVES["blend4"](x, y, imm)
                if all(((imm // (4 ** k)) % 4) in (0, 3) for k in range(4)):
                    return tuple(y[k] if ((imm // (4 ** k)) % 4) == 3 else x[k] for k in range(4))
                raise Refuse("`blend_halves` splits a 32-bit word")
            raise Refuse(f"128-bit vector op `{f}` not handled")

        def _each512_op(st, op, x, y):
            tab = st["tab"]
            if op == "add32":
                return tuple(tab.w_add(a, b) for a, b in zip(x, y))
            if op == "xor32":
                return tuple(tab.w_xor(a, b) for a, b in zip(x, y))
            if op == "and32":
                return tuple(tab.w_and(a, b) for a, b in zip(x, y))
            if op == "ult32":
                return tuple(tab.w_ult(a, b) for a, b in zip(x, y))
            raise Refuse(f"512-bit `each32` op `{op}` not handled")

        def _eval_vec512(ex, bind, st):
            tab = st["tab"]
            if ex[0] == "name":
                l = _sym_vec16(bind, st, ex)
                if l is None:
                    raise Refuse("512-bit register has unknown lanes")
                return l
            if ex[0] != "call":
                raise Refuse(f"512-bit expression `{ex}` not handled")
            f, args = ex[1], ex[2]
            if f == "zeros16" and not args:
                z = tab.w_atom((0, ()))
                return (z,) * 16
            if f == "spread16" and len(args) == 1 and args[0][0] == "call" and args[0][1] == "lane32" and len(args[0][2]) == 1:
                src = args[0][2][0]
                if src[0] == "call" and src[1] == "mem32":
                    ids = _sym_load_words(st, _sym_word_addr(bind, st, src[2]), 1)
                    return (ids[0],) * 16
                if src[0] == "call" and src[1] == "low32" and len(src[2]) == 1:
                    val, _ = eval_table_expr(src[2][0], bind, st)
                else:
                    val, _ = eval_table_expr(src, bind, st)
                w = tab.w_atom_k(st["known_div_rem"], st["var_to_term"], val)
                return (w,) * 16
            if f in ("mem512", "mem512a"):
                return _sym_mem512(bind, st, f, args)
            if f == "each32" and len(args) == 3 and args[0][0] == "name":
                op = args[0][1]
                x = _sym_vec16(bind, st, args[1])
                if x is None:
                    raise Refuse("512-bit `each32` source has unknown lanes")
                if op == "ror32":
                    n = _sym_number(bind, args[2])
                    if n is None:
                        raise Refuse("512-bit `ror32` needs an immediate")
                    return tuple(tab.w_rotr(a, n % 32) for a in x)
                b = args[2]
                if b[0] == "call":
                    if b[1] == "words16" and len(b[2]) == 1 and b[2][0][0] == "name" and b[2][0][1] in bind:
                        raw_k = str(bind[b[2][0][1]]).split("#")[0]
                        n512 = int(raw_k, 0)
                        ks = [(n512 >> (32 * i)) & M32 for i in range(16)]
                        if op != "add32":
                            raise Refuse(f"512-bit constant op `{op}` not handled")
                        return tuple(tab.w_add_const(a, k) for a, k in zip(x, ks))
                    y = _sym_mem512(bind, st, b[1], b[2])
                    return _each512_op(st, op, x, y)
                y = _sym_vec16(bind, st, b)
                if y is None:
                    raise Refuse("512-bit `each32` second operand has unknown lanes")
                return _each512_op(st, op, x, y)
            if f == "choose16" and len(args) == 3 and args[1][0] == "call" and args[1][1] == "each32" and len(args[1][2]) == 3:
                m_vec = _sym_vec16(bind, st, args[0])
                op_nm = args[1][2][0][1]
                a_vec = _sym_vec16(bind, st, args[1][2][1])
                b_vec = _sym_vec16(bind, st, args[1][2][2])
                c_vec = _sym_vec16(bind, st, args[2])
                if None in (m_vec, a_vec, b_vec, c_vec):
                    raise Refuse("`choose16` operand has unknown lanes")
                new_vec = _each512_op(st, op_nm, a_vec, b_vec)
                return tuple(tab.w_sel(mv, nv, ov) for mv, nv, ov in zip(m_vec, new_vec, c_vec))
            if f == "in_quarters" and len(args) == 6:
                x = _sym_vec16(bind, st, args[0])
                y = _sym_vec16(bind, st, args[1])
                picks = [a[1] for a in args[2:] if a[0] == "number" and 0 <= a[1] < 8]
                if x is None or y is None or len(picks) != 4:
                    raise Refuse("invalid `in_quarters`")
                return tab_mod.MOVES["in_quarters"](x, y, *picks)
            if f == "quarters" and len(args) == 3:
                x = _sym_vec16(bind, st, args[0])
                y = _sym_vec16(bind, st, args[1])
                imm = _sym_number(bind, args[2])
                if x is None or y is None or imm is None:
                    raise Refuse("invalid `quarters`")
                return tab_mod.MOVES["quarters"](x, y, imm)
            raise Refuse(f"512-bit op `{f}` not handled")

        # ---------------------------------------------------------------
        # Word-level specification evaluator (`weval` + `ensuresw`)
        # ---------------------------------------------------------------

        def _r_same_row(facts, a, b):
            if a == b:
                return True
            d1, d2 = r_sub(a, b), r_sub(b, a)
            return r_plain(facts, d1) and r_plain(facts, d2)

        def _w_id_of(tab, xs):
            if len(xs) == 1 and xs[0][1] == 1:
                return xs[0][0]
            return tab.find(("add", xs))

        def _w_atom_id(tab, st, r):
            i = tab.find(("atom", r_word(r)))
            if i is not None:
                return i
            w = r_word(r)
            vi = r_var_idx(w)
            if vi is not None and vi in st["var_to_term"]:
                tid = st["var_to_term"][vi]
                if tid < len(tab.arr):
                    return tid
            if (r, W32) in st["div_cache"]:
                _, rem = st["div_cache"][(r, W32)]
                return tab.find(("atom", rem))
            return None

        def _w_quot_of(st, r, m):
            if all((c % m) == 0 for c in r[1]):
                return (r[0] // m, _trim(tuple(c // m for c in r[1])))
            sp = sym_split(st["facts"], r, m, st["word32_vars"])
            if sp is not None:
                return sp[0]
            if (r, m) in st["div_cache"]:
                return st["div_cache"][(r, m)][0]
            return None

        def _w_low_of(st, r, m):
            if all((c % m) == 0 for c in r[1]):
                return r_const(r[0] % m)
            if r_plain(st["facts"], r) and r_plain(st["facts"], r_sub(r_const(m - 1), r)):
                return r
            if m == W32 and is_word32_row(st, r):
                return r
            sp = sym_split(st["facts"], r, m, st["word32_vars"])
            if sp is not None:
                return sp[1]
            if (r, m) in st["div_cache"]:
                return st["div_cache"][(r, m)][1]
            return None

        def _w_high_of(st, r):
            if r_high(r) == (0, ()) and r[1]:
                if (r, W32) in st["div_cache"]:
                    return st["div_cache"][(r, W32)][0]
                return _w_quot_of(st, r, W32)
            if (not r_word(r)[1]) or (r_has_high(r) and is_word32_row(st, r_word(r))):
                return r_high(r)
            if (r, W32) in st["div_cache"]:
                return st["div_cache"][(r, W32)][0]
            return _w_quot_of(st, r, W32)

        def _w_known_or(st, x, y):
            if (x, y) in st["or_cache"]:
                return st["or_cache"][(x, y)]
            if (y, x) in st["or_cache"]:
                return st["or_cache"][(y, x)]
            return None

        def _w_hi_plus(tab, st, r):
            if 0 < r[0] < W32 and r_plain(st["facts"], (0, r[1])):
                base = (0, r[1])
                a = _w_atom_id(tab, st, r)
                l = _w_atom_id(tab, st, base)
                hq = _w_high_of(st, base)
                h = _w_atom_id(tab, st, hq) if hq is not None else None
                one = tab.find(("atom", r_word(r_const(1))))
                if None not in (a, l, h, one):
                    m = tab.find(("ult", a, l))
                    if m is not None:
                        h1 = tab.find(("add", merge_add(((h, 1),), ((one, 1),))))
                        if h1 is not None:
                            return tab.find(("sel", m, h1, h))
            return None

        def _w_input_word_id(tab, st, j, k):
            i = tab.find(("input", j, k))
            if i is not None:
                return i
            if j < len(word_runs):
                _, r_idx, _ = word_runs[j]
                fj = _run_at(r_idx, fixeds_list)
                if fj is not None:
                    v = st["known_load"].get((fj, 4 * k))
                    if v is not None:
                        i2 = _w_atom_id(tab, st, r_var(v))
                        if i2 is not None:
                            return i2
                    if k > 0:
                        v2 = st["known_load"].get((fj, 4 * (k - 1)))
                        if v2 is not None:
                            hq = _w_high_of(st, r_var(v2))
                            if hq is not None:
                                return _w_atom_id(tab, st, hq)
            return None

        def _w_env():
            we = {}
            for idx_a, (anm, akind, alen) in enumerate(fn["args"]):
                r_idx = reg_to_idx[arg_regs[idx_a]]
                if akind == "number":
                    we[anm] = ("num", r_var(r_idx))
                elif akind == "bytes" and alen in arg_reg_idx_by_name:
                    we[anm] = ("region", r_idx, arg_reg_idx_by_name[alen])
                elif akind in ("fixed", "inout"):
                    we[anm] = ("run", r_idx, int(alen))
            # Match Core.lean `wenv = lanesW c ++ wenvIn c`: lane tables take precedence over fixed runs
            for j_f, (fnm, _, cnt8, l_idx) in tables_by_j.items():
                we[fnm] = ("lanes", j_f, cnt8, l_idx)
            return we

        WOWN = frozenset(("word", "counter", "lo", "hi", "words", "number.le"))

        def _w_num_op(st, op, x, y):
            f = st["facts"]
            if op == "+":
                return ("num", r_add(x, y))
            if op == "-":
                d = r_sub(x, y)
                return ("num", d) if r_plain(f, d) else None
            if op == "==":
                if _r_same_row(f, x, y):
                    return ("bool", True)
                if r_plain(f, r_sub(r_sub(x, y), r_const(1))) or r_plain(f, r_sub(r_sub(y, x), r_const(1))):
                    return ("bool", False)
                return None
            if op == "<":
                if r_plain(f, r_sub(r_sub(y, x), r_const(1))):
                    return ("bool", True)
                if r_plain(f, r_sub(x, y)):
                    return ("bool", False)
                return None
            if op == ">=":
                if r_plain(f, r_sub(x, y)):
                    return ("bool", True)
                if r_plain(f, r_sub(r_sub(y, x), r_const(1))):
                    return ("bool", False)
                return None
            if op == "<=":
                if r_plain(f, r_sub(y, x)):
                    return ("bool", True)
                if r_plain(f, r_sub(r_sub(x, y), r_const(1))):
                    return ("bool", False)
                return None
            if op == ">":
                if r_plain(f, r_sub(r_sub(x, y), r_const(1))):
                    return ("bool", True)
                if r_plain(f, r_sub(y, x)):
                    return ("bool", False)
                return None
            return None

        def _w_int_bin(op, a, b):
            if op == "+": return ("int", a + b)
            if op == "-": return ("int", a - b) if a >= b else None
            if op == "*": return ("int", a * b)
            if op == "/" and b > 0: return ("int", a // b)
            if op == "%" and b > 0: return ("int", a % b)
            if op == "|": return ("int", a | b)
            if op == "&": return ("int", a & b)
            if op == "^": return ("int", a ^ b)
            if op == "<<" and 0 <= b < 64: return ("int", a << b)
            if op == ">>" and 0 <= b < 64: return ("int", a >> b)
            if op == "==": return ("bool", a == b)
            if op == "!=": return ("bool", a != b)
            if op == "<": return ("bool", a < b)
            if op == "<=": return ("bool", a <= b)
            if op == ">": return ("bool", a > b)
            if op == ">=": return ("bool", a >= b)
            return None

        def _weval(tab, st, wenv, e, fuel=1000):
            if fuel <= 0 or not isinstance(e, tuple) or not e:
                return None
            tag = e[0]
            if tag == "num":
                n = int(e[1])
                return ("int", n) if n >= 0 else None
            if tag == "name":
                return wenv.get(e[1])
            if tag == "bin":
                op = e[1]
                xv = _weval(tab, st, wenv, e[2], fuel - 1)
                yv = _weval(tab, st, wenv, e[3], fuel - 1)
                if xv is None or yv is None:
                    return None
                tx, ty = xv[0], yv[0]
                if tx == "int" and ty == "int":
                    return _w_int_bin(op, xv[1], yv[1])
                if tx == "word" and ty == "word":
                    if op == "+":
                        return ("word", merge_add(xv[1], yv[1]))
                    if op == "^":
                        a, b = _w_id_of(tab, xv[1]), _w_id_of(tab, yv[1])
                        if a is not None and b is not None:
                            i = tab.find(("xor", min(a, b), max(a, b)))
                            return ("word", ((i, 1),)) if i is not None else None
                        return None
                    if op == "&":
                        a, b = _w_id_of(tab, xv[1]), _w_id_of(tab, yv[1])
                        if a is not None and b is not None:
                            i = tab.find(("band", min(a, b), max(a, b)))
                            return ("word", ((i, 1),)) if i is not None else None
                        return None
                    return None
                if tx == "word" and ty == "int":
                    n = yv[1]
                    a = _w_id_of(tab, xv[1])
                    if a is None:
                        return None
                    if op == ">>>" and 0 <= n <= 32:
                        i = tab.find(("rotr", a, n))
                        return ("word", ((i, 1),)) if i is not None else None
                    if op == ">>" and 0 <= n < 32:
                        i = tab.find(("shr", a, n))
                        return ("word", ((i, 1),)) if i is not None else None
                    if op == "<<" and 0 <= n < 32:
                        i = tab.find(("shl", a, n))
                        return ("word", ((i, 1),)) if i is not None else None
                    return None
                if tx == "num" and ty == "int":
                    r, m = xv[1], yv[1]
                    if op == "*" and m >= 0:
                        return ("num", r_scale(m, r))
                    if op == "%" and m > 0:
                        lo = _w_low_of(st, r, m)
                        return ("num", lo) if lo is not None else None
                    if op == "/" and m > 0:
                        q = _w_quot_of(st, r, m)
                        return ("num", q) if q is not None else None
                    if op == "|":
                        if m == 0 and r_plain(st["facts"], r):
                            return ("num", r)
                        kv = _w_known_or(st, r, r_const(m))
                        if kv is not None:
                            return ("num", kv)
                        for jbits in (8, 16, 32):
                            powj = 1 << jbits
                            if m >= powj and r_plain(st["facts"], r) and r_plain(st["facts"], r_sub(r_const(powj - 1), r)):
                                if (m % powj) == 0:
                                    return ("num", r_add(r, r_const(m)))
                                kv2 = _w_known_or(st, r, r_const(m % powj))
                                if kv2 is not None:
                                    return ("num", r_add(kv2, r_const(m - (m % powj))))
                                break
                        return None
                    return _w_num_op(st, op, r, r_const(m))
                if tx == "int" and ty == "num":
                    m, r = xv[1], yv[1]
                    if op == "*" and m >= 0:
                        return ("num", r_scale(m, r))
                    if op == "|":
                        return ("num", r) if (m == 0 and r_plain(st["facts"], r)) else None
                    return _w_num_op(st, op, r_const(m), r)
                if tx == "num" and ty == "num":
                    if op == "|":
                        kv = _w_known_or(st, xv[1], yv[1])
                        return ("num", kv) if kv is not None else None
                    return _w_num_op(st, op, xv[1], yv[1])
                if tx == "counter" and ty == "int":
                    if op == "+" and yv[1] >= 0:
                        return ("counter", xv[1] if yv[1] == 0 else r_add(xv[1], r_const(yv[1])))
                    return None
                if tx == "list" and ty == "list" and op == "++":
                    return ("list", xv[1] + yv[1])
                return None
            if tag == "ifx":
                cv = _weval(tab, st, wenv, e[1], fuel - 1)
                if cv == ("bool", True):
                    return _weval(tab, st, wenv, e[2], fuel - 1)
                if cv == ("bool", False):
                    return _weval(tab, st, wenv, e[3], fuel - 1)
                return None
            if tag == "index":
                av = _weval(tab, st, wenv, e[1], fuel - 1)
                iv = _weval(tab, st, wenv, e[2], fuel - 1)
                if av is None or iv is None:
                    return None
                if av[0] == "list" and iv[0] == "int":
                    k = iv[1]
                    return av[1][k] if 0 <= k < len(av[1]) else None
                if av[0] == "run" and iv[0] == "int":
                    k = iv[1]
                    return ("pbyte", av[1], k) if 0 <= k < av[2] else None
                if av[0] == "part" and iv[0] == "int":
                    k = iv[1]
                    return ("pbyte", av[1], av[2] + k) if 0 <= k < av[3] else None
                if av[0] == "span" and iv[0] == "int":
                    r_r, off_r, slen_r = av[1], av[2], av[3]
                    k = iv[1]
                    if (not off_r[1]) and off_r[0] >= 0 and k >= 0 and r_plain(st["facts"], r_sub(slen_r, r_const(k + 1))):
                        return ("pbyte", r_r, off_r[0] + k)
                    return None
                if av[0] == "lanes" and iv[0] == "int":
                    k = iv[1]
                    return ("lane", av[1], 8 * k, av[3]) if 0 <= k < av[2] else None
                if av[0] == "lane" and iv[0] in ("int", "num"):
                    off_r = r_const(64 * iv[1]) if iv[0] == "int" else r_scale(64, iv[1])
                    if iv[0] == "int" and iv[1] < 0:
                        return None
                    for bj, bc, boff, bvs in st["known_block"]:
                        if bj == av[1] and bc == av[2] and _r_same_row(st["facts"], boff, off_r):
                            ws = []
                            for bvi in bvs:
                                tid = tab.find(("atom", r_word(r_var(bvi))))
                                if tid is None:
                                    return None
                                ws.append(("word", ((tid, 1),)))
                            return ("list", ws)
                    return None
                return None
            if tag == "call":
                fn_nm = e[1]
                vs = []
                for ae in e[2:]:
                    v = _weval(tab, st, wenv, ae, fuel - 1)
                    if v is None:
                        return None
                    vs.append(v)
                if fn_nm == "len" and len(vs) == 1:
                    v0 = vs[0]
                    if v0[0] == "region": return ("num", r_var(v0[2]))
                    if v0[0] == "span": return ("num", v0[3])
                    if v0[0] == "run": return ("int", v0[2])
                    if v0[0] == "part": return ("int", v0[3])
                    if v0[0] == "list": return ("int", len(v0[1]))
                    if v0[0] == "wbytes": return ("int", 4 * len(v0[1]))
                    return None
                if fn_nm in WOWN:
                    if len(vs) != 1:
                        return None
                    v0 = vs[0]
                    if v0[0] == "int":
                        n = v0[1]
                        if fn_nm == "word" and n >= 0:
                            i = tab.find(("atom", r_word(r_const(n))))
                            return ("word", ((i, 1),)) if i is not None else None
                        if fn_nm == "counter" and n >= 0:
                            return ("counter", r_const(n))
                        return None
                    if v0[0] == "num":
                        r = v0[1]
                        if not r_plain(st["facts"], r):
                            return None
                        if fn_nm == "word":
                            i = _w_atom_id(tab, st, r)
                            return ("word", ((i, 1),)) if i is not None else None
                        if fn_nm == "counter":
                            return ("counter", r)
                        return None
                    if v0[0] == "word" and fn_nm == "word":
                        return v0
                    if v0[0] == "counter":
                        r = v0[1]
                        if fn_nm == "counter":
                            return v0
                        if fn_nm == "lo":
                            i = _w_atom_id(tab, st, r)
                            return ("word", ((i, 1),)) if i is not None else None
                        if fn_nm == "hi":
                            hq = _w_high_of(st, r)
                            if hq is not None:
                                i = _w_atom_id(tab, st, hq)
                                if i is not None:
                                    return ("word", ((i, 1),))
                            i2 = _w_hi_plus(tab, st, r)
                            return ("word", ((i2, 1),)) if i2 is not None else None
                        return None
                    if v0[0] == "run":
                        r_idx, n = v0[1], v0[2]
                        if fn_nm == "words" and (n % 4) == 0:
                            j = _run_at(r_idx, word_runs)
                            if j is None:
                                return None
                            ws = []
                            for k in range(n // 4):
                                i = _w_input_word_id(tab, st, j, k)
                                if i is None:
                                    return None
                                ws.append(("word", ((i, 1),)))
                            return ("list", ws)
                        return None
                    if v0[0] == "part":
                        r_idx, off, n = v0[1], v0[2], v0[3]
                        if fn_nm == "words" and (off % 4) == 0 and (n % 4) == 0:
                            j = _run_at(r_idx, word_runs)
                            if j is None:
                                return None
                            ws = []
                            for k in range(n // 4):
                                i = _w_input_word_id(tab, st, j, off // 4 + k)
                                if i is None:
                                    return None
                                ws.append(("word", ((i, 1),)))
                            return ("list", ws)
                        if fn_nm == "number.le" and n == 8:
                            fj = _run_at(r_idx, fixeds_list)
                            if fj is not None and (fj, off) in st["known_load"]:
                                return ("num", r_var(st["known_load"][(fj, off)]))
                        return None
                    if v0[0] == "wbytes":
                        ids = v0[1]
                        if fn_nm == "words":
                            return ("list", [("word", ((i, 1),)) for i in ids])
                        if fn_nm == "number.le" and len(ids) == 2:
                            a, b = ids
                            if (a < len(tab.arr) and b < len(tab.arr)
                                    and tab.arr[a][0] == "atom" and tab.arr[b][0] == "atom"):
                                r1, r2 = tab.arr[a][1], tab.arr[b][1]
                                if is_word32_row(st, r1) and is_word32_row(st, r2):
                                    return ("num", r_add(r1, r_scale(W32, r2)))
                        return None
                    if v0[0] == "list" and v0[1] and v0[1][0][0] == "pbyte":
                        r0, off0 = v0[1][0][1], v0[1][0][2]
                        n = len(v0[1])
                        if (fn_nm == "words" and (off0 % 4) == 0 and (n % 4) == 0
                                and all(b[0] == "pbyte" and b[1] == r0 and b[2] == off0 + idx_b for idx_b, b in enumerate(v0[1]))):
                            j = _run_at(r0, word_runs)
                            if j is None:
                                return None
                            ws = []
                            for k in range(n // 4):
                                i = _w_input_word_id(tab, st, j, off0 // 4 + k)
                                if i is None:
                                    return None
                                ws.append(("word", ((i, 1),)))
                            return ("list", ws)
                    return None
                if (st["known_held"].has_fn(fn_nm)
                        or st["known_held_b"].has_fn(fn_nm)
                        or st["known_use"].has_fn(fn_nm)):
                    ks = _flat_keys(tab, vs)
                    if ks is not None:
                        ids0 = st["known_held"].find(st["facts"], fn_nm, ks, _same_keys)
                        if ids0 is not None:
                            return ("list", [("word", ((i, 1),)) for i in ids0])
                        ids0 = st["known_held_b"].find(st["facts"], fn_nm, ks, _same_keys)
                        if ids0 is not None:
                            return ("wbytes", ids0)
                        h0 = st["known_use"].find(st["facts"], fn_nm, ks, _same_keys)
                        if h0 is not None:
                            return ("use", h0)
                if fn_nm in self.defs:
                    dparams, dbody = self.defs[fn_nm]
                    if len(dparams) == len(vs):
                        return _weval(tab, st, dict(zip(dparams, vs)), dbody, fuel - 1)
                return None
            if tag == "list":
                out = []
                for it in e[1:]:
                    v = _weval(tab, st, wenv, it, fuel - 1)
                    if v is None:
                        return None
                    out.append(v)
                return ("list", out)
            if tag == "let":
                v = _weval(tab, st, wenv, e[2], fuel - 1)
                if v is None:
                    return None
                ne = dict(wenv)
                ne[e[1]] = v
                return _weval(tab, st, ne, e[3], fuel - 1)
            if tag == "each":
                lo_v = _weval(tab, st, wenv, e[3], fuel - 1)
                hi_v = _weval(tab, st, wenv, e[4], fuel - 1)
                if lo_v is None or hi_v is None or lo_v[0] != "int" or hi_v[0] != "int":
                    return None
                out = []
                for idx_i in range(lo_v[1], hi_v[1]):
                    ne = dict(wenv)
                    ne[e[2]] = ("int", idx_i)
                    v = _weval(tab, st, ne, e[1], fuel - 1)
                    if v is None:
                        return None
                    out.append(v)
                return ("list", out)
            if tag == "with":
                av = _weval(tab, st, wenv, e[1], fuel - 1)
                if av is None or av[0] != "list":
                    return None
                lst = list(av[1])
                puts = [_weval(tab, st, wenv, pe, fuel - 1) for pe in e[2:]]
                if any(p is None for p in puts) or (len(puts) % 2) != 0:
                    return None
                for k in range(0, len(puts), 2):
                    iv, xv = puts[k], puts[k + 1]
                    if iv[0] != "int" or not (0 <= iv[1] < len(lst)):
                        return None
                    lst[iv[1]] = xv
                return ("list", lst)
            if tag == "slice":
                av = _weval(tab, st, wenv, e[1], fuel - 1)
                lo_v = _weval(tab, st, wenv, e[2], fuel - 1)
                hi_v = _weval(tab, st, wenv, e[3], fuel - 1)
                if av is None or lo_v is None or hi_v is None:
                    return None
                if lo_v[0] == "int" and hi_v[0] == "int":
                    i, j = lo_v[1], hi_v[1]
                    if av[0] == "run" and 0 <= i <= j <= av[2]:
                        return ("part", av[1], i, j - i)
                    if av[0] == "part" and 0 <= i <= j <= av[3]:
                        return ("part", av[1], av[2] + i, j - i)
                    if av[0] == "region" and 0 <= i <= j and r_plain(st["facts"], r_sub(r_var(av[2]), r_const(j))):
                        return ("part", av[1], i, j - i)
                    if av[0] == "span" and 0 <= i <= j and r_plain(st["facts"], r_sub(av[3], r_const(j))):
                        if (not av[2][1]) and av[2][0] >= 0:
                            return ("part", av[1], av[2][0] + i, j - i)
                        return ("span", av[1], r_add(av[2], r_const(i)), r_const(j - i))
                    if av[0] == "list" and 0 <= i <= j <= len(av[1]):
                        return ("list", av[1][i:j])
                    if av[0] == "wbytes" and 0 <= i <= j and (i % 4) == 0 and (j % 4) == 0 and j // 4 <= len(av[1]):
                        return ("wbytes", av[1][i // 4:j // 4])
                if lo_v[0] == "int" and hi_v[0] == "num":
                    i, jr = lo_v[1], hi_v[1]
                    if av[0] == "region" and i >= 0 and r_plain(st["facts"], r_sub(jr, r_const(i))) and r_plain(st["facts"], r_sub(r_var(av[2]), jr)):
                        return ("span", av[1], r_const(i), r_sub(jr, r_const(i)))
                if lo_v[0] == "num" and hi_v[0] == "num":
                    ir, jr = lo_v[1], hi_v[1]
                    if av[0] == "region" and r_plain(st["facts"], ir) and r_plain(st["facts"], r_sub(jr, ir)) and r_plain(st["facts"], r_sub(r_var(av[2]), jr)):
                        return ("span", av[1], ir, r_sub(jr, ir))
                    if av[0] == "span" and r_plain(st["facts"], ir) and r_plain(st["facts"], r_sub(jr, ir)) and r_plain(st["facts"], r_sub(av[3], jr)):
                        return ("span", av[1], r_add(av[2], ir), r_sub(jr, ir))
                return None
            if tag == "record":
                fvs = []
                for fpair in e[1:]:
                    v = _weval(tab, st, wenv, fpair[1], fuel - 1)
                    if v is None:
                        return None
                    fvs.append((fpair[0], v))
                for h_rec, rfields, rids in st["known_record"]:
                    if _rec_matches(st["facts"], tab.arr, rfields, rids, fvs):
                        return ("use", h_rec)
                return ("record", fvs)
            if tag == "field":
                rv = _weval(tab, st, wenv, e[1], fuel - 1)
                if rv is not None and rv[0] == "record":
                    for k_f, v_f in rv[1]:
                        if k_f == e[2]:
                            return v_f
                return None
            if tag == "thenumber":
                which, xnm, lo_e, hi_e, cond_e = e[1], e[2], e[3], e[4], e[5]
                lo_v = _weval(tab, st, wenv, lo_e, fuel - 1)
                hi_v = _weval(tab, st, wenv, hi_e, fuel - 1)
                if lo_v is None or hi_v is None or lo_v[0] != "int" or hi_v[0] != "int":
                    return None
                rng = list(range(lo_v[1], hi_v[1]))
                if which == "greatest":
                    rng.reverse()
                for n in rng:
                    ne = dict(wenv)
                    ne[xnm] = ("int", n)
                    cv = _weval(tab, st, ne, cond_e, fuel - 1)
                    if cv == ("bool", True):
                        return ("int", n)
                    if cv != ("bool", False):
                        return None
                return None
            if tag == "thepower":
                which, xnm, cond_e = e[1], e[2], e[3]
                rng = [1 << k for k in range(64)]
                if which == "greatest":
                    rng.reverse()
                for n in rng:
                    ne = dict(wenv)
                    ne[xnm] = ("int", n)
                    cv = _weval(tab, st, ne, cond_e, fuel - 1)
                    if cv == ("bool", True):
                        return ("int", n)
                    if cv != ("bool", False):
                        return None
                return None
            return None

        def _flat_key(tab, v):
            tv = v[0]
            if tv == "int": return ("num", r_const(v[1]))
            if tv == "num": return ("num", v[1])
            if tv == "counter": return ("counter", v[1])
            if tv == "list":
                ids = []
                for it in v[1]:
                    if it[0] != "word":
                        return None
                    tid = _w_id_of(tab, it[1])
                    if tid is None:
                        return None
                    ids.append(tid)
                return ("words", tuple(ids))
            if tv == "lane": return ("lane", v[1], v[2], v[3])
            if tv == "use": return ("use", v[1])
            if tv == "span": return ("span", v[1], v[2], v[3])
            if tv == "region": return ("span", v[1], r_const(0), r_var(v[2]))
            if tv == "part": return ("span", v[1], r_const(v[2]), r_const(v[3]))
            return None

        def _flat_keys(tab, vs):
            out = []
            for v in vs:
                k = _flat_key(tab, v)
                if k is None:
                    return None
                out.append(k)
            return tuple(out)

        def _key_ok(k, nvars, ntab):
            tk = k[0]
            if tk in ("num", "counter"): return len(k[1][1]) <= nvars
            if tk == "words": return all(i < ntab for i in k[1])
            if tk == "lane": return True
            if tk == "span": return len(k[2][1]) <= nvars and len(k[3][1]) <= nvars
            if tk == "use": return k[1] < nvars
            return False

        def _same_key(facts, a, b):
            if a[0] != b[0]:
                return False
            tk = a[0]
            if tk in ("num", "counter"):
                return _r_same_row(facts, a[1], b[1])
            if tk == "span":
                return a[1] == b[1] and _r_same_row(facts, a[2], b[2]) and _r_same_row(facts, a[3], b[3])
            return a == b

        def _same_keys(facts, ks1, ks2):
            return len(ks1) == len(ks2) and all(_same_key(facts, a, b) for a, b in zip(ks1, ks2))

        def _place_wenv(pl, st_p):
            we = _w_env()
            for nm, rn in pl["names"]:
                we[nm] = ("num", st_p["regs"][rn])
            return we

        def _lanes_shown(pl, st_p):
            tab = st_p["tab"]
            we = _place_wenv(pl, st_p)
            for vregs, x_var, f_nm, arg_es in pl.get("lanes", ()):
                call_e = ("call", f_nm) + tuple(arg_es)
                for i in range(16):
                    ne = dict(we)
                    ne[x_var] = ("int", i)
                    res = _weval(tab, st_p, ne, call_e)
                    if res is None or res[0] != "list" or len(res[1]) != len(vregs):
                        raise Refuse(f"at place {pl['pc']} vector lanes `{f_nm}` do not match lane {i}")
                    for vr, wv in zip(vregs, res[1]):
                        if wv[0] != "word":
                            raise Refuse(f"at place {pl['pc']} lane {i} is not a word")
                        tid = _w_id_of(tab, wv[1])
                        vec_v = st_p["vec"].get(vr)
                        if tid is None or vec_v is None or i >= len(vec_v) or vec_v[i] != tid:
                            raise Refuse(f"at place {pl['pc']} vector register v{vr} lane {i} does not match `{f_nm}`")

        def _cells_shown(pl, st_p):
            tab = st_p["tab"]
            we = _place_wenv(pl, st_p)
            for off_c, x_var, c_expr in pl.get("cells", ()):
                c_row = r_add(r_sub(st_p["regs"][sp_reg], entry_regs[sp_reg]), r_const(off_c))
                held = st_p["spill"].get(c_row)
                if held is None or len(held) != 16:
                    raise Refuse(f"at place {pl['pc']} stack cell at +{off_c} is not stored")
                for i in range(16):
                    ne = dict(we)
                    ne[x_var] = ("int", i)
                    wv = _weval(tab, st_p, ne, c_expr)
                    if wv is None or wv[0] != "word":
                        raise Refuse(f"at place {pl['pc']} stack cell +{off_c} lane {i} is not a word")
                    tid = _w_id_of(tab, wv[1])
                    if tid is None or tid != held[i]:
                        raise Refuse(f"at place {pl['pc']} stack cell +{off_c} lane {i} does not match")

        def _suppose_lanes_cells(pl, st_p):
            tab = st_p["tab"]
            we = _place_wenv(pl, st_p)
            for vregs, x_var, f_nm, arg_es in pl.get("lanes", ()):
                if f_nm == "len" or f_nm in WOWN:
                    raise Refuse("a place's lanes must name a specification definition")
                lane_keys = []
                for i in range(16):
                    ne = dict(we)
                    ne[x_var] = ("int", i)
                    vs = [_weval(tab, st_p, ne, ae) for ae in arg_es]
                    if any(v is None for v in vs):
                        raise Refuse(f"at place {pl['pc']} lane {i} arguments not followed")
                    ks = _flat_keys(tab, vs)
                    if ks is None or not all(_key_ok(k, st_p["nvars"], len(tab.arr)) for k in ks):
                        raise Refuse(f"at place {pl['pc']} lane {i} keys not followed")
                    lane_keys.append(ks)
                m = len(vregs)
                base_u = st_p["nvars"]
                st_p["nvars"] += 16 * m
                made = [tab.w_atom(r_var(base_u + u)) for u in range(16 * m)]
                for k_r, vr in enumerate(vregs):
                    st_p["vec"][vr] = tuple(made[m * i + k_r] for i in range(16))
                for i in range(16):
                    st_p["known_held"].add(f_nm, lane_keys[i], tuple(made[m * i + k_r] for k_r in range(m)))
            for off_c, x_var, c_expr in pl.get("cells", ()):
                c_row = r_add(r_sub(st_p["regs"][sp_reg], entry_regs[sp_reg]), r_const(off_c))
                ids = []
                for i in range(16):
                    ne = dict(we)
                    ne[x_var] = ("int", i)
                    wv = _weval(tab, st_p, ne, c_expr)
                    if wv is None or wv[0] != "word":
                        raise Refuse(f"at place {pl['pc']} general stack cell +{off_c} lane {i} not followed")
                    tid = _w_id_of(tab, wv[1])
                    if tid is None or tid >= len(tab.arr):
                        raise Refuse(f"at place {pl['pc']} general stack cell +{off_c} lane {i} not in table")
                    ids.append(tid)
                st_p["spill"][c_row] = tuple(ids)

        def _sym_know(st_r, limit=200):
            for _ in range(limit):
                if stream.pos >= len(stream.items):
                    break
                nxt_it = stream.items[stream.pos]
                if nxt_it[0] == "k":
                    stream.pos += 1
                    g = nxt_it[1]
                    if len(g[1]) > st_r["nvars"]:
                        raise Refuse("`k` row speaks of an unknown variable not in use")
                    self.entail(st_r["facts"], g, stream)
                    st_r["facts"].append(g)
                elif nxt_it[0] == "t" and nxt_it[1] == "next":
                    stream.pos += 1
                    break
                else:
                    break

        def _rec_matches(facts, arr, fields, ids, fvs):
            if len(fields) != len(fvs):
                return False
            pos = 0
            for rf, (x, v) in zip(fields, fvs):
                if rf[1] != x:
                    return False
                kind_f = rf[0]
                if kind_f == "words":
                    n = rf[2]
                    if v[0] != "list" or len(v[1]) != n or pos + n > len(ids):
                        return False
                    for k_w, wv in enumerate(v[1]):
                        if wv[0] != "word" or len(wv[1]) != 1 or wv[1][0] != (ids[pos + k_w], 1):
                            return False
                    pos += n
                elif kind_f == "bytes":
                    n = rf[2]
                    if (n % 4) != 0 or v[0] != "wbytes" or pos + n // 4 > len(ids):
                        return False
                    if tuple(v[1]) != tuple(ids[pos:pos + n // 4]):
                        return False
                    pos += n // 4
                elif kind_f == "u64":
                    if v[0] != "num" or pos + 2 > len(ids):
                        return False
                    a_id, b_id = ids[pos], ids[pos + 1]
                    if a_id >= len(arr) or b_id >= len(arr):
                        return False
                    na, nb = arr[a_id], arr[b_id]
                    if na[0] != "atom" or nb[0] != "atom":
                        return False
                    r1, r2 = na[1], nb[1]
                    if not (r_plain(facts, r1) and r_plain(facts, r_sub(r_const(W32 - 1), r1))
                            and r_plain(facts, r2) and r_plain(facts, r_sub(r_const(W32 - 1), r2))
                            and _r_same_row(facts, v[1], r_add(r1, r_scale(W32, r2)))):
                        return False
                    pos += 2
                else:
                    return False
            return pos == len(ids)

        def _parse_rec_part(x, e):
            if not (isinstance(e, tuple) and len(e) == 4 and e[0] == "ifx"):
                return None
            cond, thn, els = e[1], e[2], e[3]
            # Else must be `[0][1]`
            if els != ("index", ("list", ("num", "0")), ("num", "1")):
                return None
            if not (isinstance(cond, tuple) and len(cond) == 4 and cond[0] == "bin"):
                return None
            op, lhs, rhs = cond[1], cond[2], cond[3]
            if not (isinstance(rhs, tuple) and rhs[0] == "num"):
                return None
            k = int(rhs[1])
            if op == "==" and isinstance(lhs, tuple) and len(lhs) == 3 and lhs[0] == "call" and lhs[1] == "len":
                fl = lhs[2]
                if isinstance(fl, tuple) and len(fl) == 3 and fl[0] == "field" and fl[1] == ("name", x):
                    fn1 = fl[2]
                    if thn == ("field", ("name", x), fn1) and k >= 0:
                        return ("words", fn1, k)
                    if thn == ("call", "words", ("field", ("name", x), fn1)) and k >= 0 and (k % 4) == 0:
                        return ("bytes", fn1, k)
            if op == "<" and isinstance(lhs, tuple) and len(lhs) == 3 and lhs[0] == "field" and lhs[1] == ("name", x):
                fn1 = lhs[2]
                want_thn = ("list", ("call", "lo", ("call", "counter", ("field", ("name", x), fn1))),
                            ("call", "hi", ("call", "counter", ("field", ("name", x), fn1))))
                if thn == want_thn and 0 < k <= (1 << 64):
                    return ("u64", fn1, k)
            return None

        def _parse_rec_body(x, e):
            if isinstance(e, tuple) and len(e) == 4 and e[0] == "bin" and e[1] == "++":
                f = _parse_rec_part(x, e[2])
                rest = _parse_rec_body(x, e[3])
                if f is not None and rest is not None:
                    return [f] + rest
                return None
            f = _parse_rec_part(x, e)
            return [f] if f is not None else None

        def _returns_record(names, e):
            if not isinstance(e, tuple):
                return False
            if e[0] == "let":
                return _returns_record(names, e[3])
            if e[0] == "ifx":
                return _returns_record(names, e[2]) and _returns_record(names, e[3])
            if e[0] == "record":
                return [p[0] for p in e[1:]] == list(names)
            return False

        def _rec_field_nwords(rf):
            if rf[0] == "words": return rf[2]
            if rf[0] == "bytes": return rf[2] // 4
            return 2

        def _rec_bound_facts(base, fields):
            out = []
            off = 0
            for rf in fields:
                if rf[0] == "u64":
                    out.append(r_sub(r_const(rf[2] - 1), r_add(r_var(base + off), r_scale(W32, r_var(base + off + 1)))))
                off += _rec_field_nwords(rf)
            return out

        def _register_val_arg(wenv_v, fuel, st_v, e):
            tab = st_v["tab"]
            v = _weval(tab, st_v, wenv_v, e)
            if v is not None:
                k = _flat_key(tab, v)
                if k is not None and _key_ok(k, st_v["nvars"], len(tab.arr)):
                    return k
            if fuel > 0 and isinstance(e, tuple) and len(e) >= 2 and e[0] == "call":
                fn_nm = e[1]
                if fn_nm != "len" and fn_nm not in WOWN and fn_nm in self.defs:
                    dparams, _ = self.defs[fn_nm]
                    ks = []
                    for ae in e[2:]:
                        ak = _register_val_arg(wenv_v, fuel - 1, st_v, ae)
                        if ak is None:
                            return None
                        ks.append(ak)
                    ks_t = tuple(ks)
                    if len(dparams) == len(ks_t):
                        h_hit = st_v["known_use"].find(st_v["facts"], fn_nm, ks_t, _same_keys)
                        if h_hit is not None:
                            return ("use", h_hit)
                        h_new = st_v["nvars"]
                        st_v["nvars"] += 1
                        st_v["known_use"].add(fn_nm, ks_t, h_new)
                        return ("use", h_new)
            return None

        def _attach_val_arrays(st_r):
            if not val_arrays_list:
                return
            tab = st_r["tab"]
            for jf, (_, _, n_f) in enumerate(fixeds_list):
                for kw in range(n_f // 4):
                    tab.intern(("input", jf, kw))
            base_j = len(fixeds_list) + len(inouts_list) + len(regions_list)
            vs_map = {nm: (idx_nm, ex) for nm, idx_nm, ex in fn.get("valspecs", ())}
            for k_va, (xnm, _, l_idx, ch, el) in enumerate(val_arrays_list):
                if xnm not in vs_map:
                    continue
                idx_nm, expr = vs_map[xnm]
                j = base_j + k_va
                nw = el // 4
                if nw == 0 or ch == 0:
                    continue
                idxs = []
                seen_i = set()
                for nd in tab.arr:
                    if nd[0] == "input" and nd[1] == j:
                        ii = nd[2] // nw
                        if ii not in seen_i:
                            seen_i.add(ii)
                            idxs.append(ii)
                for ii in idxs:
                    if not r_plain(st_r["facts"], r_sub(r_var(l_idx), r_const((ii + 1) * ch))):
                        continue
                    ids = []
                    ok_ids = True
                    for kw in range(nw):
                        tid = tab.find(("input", j, ii * nw + kw))
                        if tid is None:
                            ok_ids = False
                            break
                        ids.append(tid)
                    if not ok_ids:
                        continue
                    if isinstance(expr, tuple) and len(expr) >= 2 and expr[0] == "call":
                        fn_nm = expr[1]
                        if fn_nm != "len" and fn_nm not in WOWN and fn_nm in self.defs:
                            dparams, _ = self.defs[fn_nm]
                            we = _w_env()
                            we[idx_nm] = ("int", ii)
                            ks = []
                            ok_k = True
                            for ae in expr[2:]:
                                ak = _register_val_arg(we, 4, st_r, ae)
                                if ak is None:
                                    ok_k = False
                                    break
                                ks.append(ak)
                            if ok_k and len(ks) == len(dparams):
                                st_r["known_held"].add(fn_nm, tuple(ks), tuple(ids))

        def _check_ensuresw(st_r, run_nm, part, val_e):
            _sym_know(st_r)
            _attach_val_arrays(st_r)
            if not (isinstance(val_e, tuple) and len(val_e) == 3 and val_e[0] == "call" and val_e[1] == "bytes_of"):
                raise Refuse("`ensuresw` value must be `(call bytes_of ...)`")
            w_idx = None
            out_n = 0
            for idx_o, (onm, _, cnt) in enumerate(outs_list):
                if onm == run_nm:
                    w_idx = idx_o
                    out_n = cnt
                    break
            if w_idx is None:
                raise Refuse(f"`ensuresw` names unknown output run `{run_nm}`")
            first = part[0] if part is not None else 0
            size = part[1] if part is not None else out_n
            res = _weval(st_r["tab"], st_r, _w_env(), val_e[2])
            if res is None or res[0] != "list":
                raise Refuse("the specification's words are not followed on the terms the function made")
            lst = res[1]
            if (first % 4) != 0 or len(lst) * 4 != size or first + size > out_n:
                raise Refuse("a word of the run is not known to hold what the specification says")
            for k_w, wv in enumerate(lst):
                if wv[0] != "word":
                    raise Refuse("a word of the run is not known to hold what the specification says")
                tid = _w_id_of(st_r["tab"], wv[1])
                if tid is None or st_r["wroteW"].get((w_idx, first // 4 + k_w)) != tid:
                    raise Refuse("a word of the run is not known to hold what the specification says")

        # ---------------------------------------------------------------
        # Word / Frame / Byte / Table Call Helpers (Core.lean symCall*)
        # ---------------------------------------------------------------

        def _c_runs(c, c_arg_regs):
            c_rmap = {anm: c_arg_regs[i] for i, (anm, _, _) in enumerate(c["args"])}
            c_outs, c_fixeds, c_inouts, c_regions, c_vas = [], [], [], [], []
            for i, (anm, ak, alen) in enumerate(c["args"]):
                rn = c_arg_regs[i]
                if ak == "out":
                    c_outs.append((anm, rn, int(alen)))
                elif ak == "inout":
                    c_outs.append((anm, rn, int(alen)))
                    c_inouts.append((anm, rn, int(alen)))
                elif ak == "fixed":
                    c_fixeds.append((anm, rn, int(alen)))
                elif ak == "bytes" and alen in c_rmap:
                    c_regions.append((anm, rn, c_rmap[alen]))
                elif ak == "valarray":
                    lnm, ch, el = alen
                    if lnm in c_rmap:
                        c_vas.append((anm, rn, c_rmap[lnm], ch, el))
            c_lanes_map = dict(c.get("lanes", ()))
            c_tables = []
            for fnm, frn, fcnt in c_fixeds:
                if fnm in c_lanes_map and c_lanes_map[fnm] in c_rmap:
                    c_tables.append((fnm, frn, fcnt // 8, c_rmap[c_lanes_map[fnm]]))
            return c_rmap, c_outs, c_fixeds, c_inouts, c_regions, c_vas, c_tables

        def _frame_at_reg(st, rname):
            d = r_sub(st["regs"][rname], entry_regs[sp_reg])
            return d[0] if not d[1] else None

        def _frame_word_row(st, off):
            cell = st["stack_mem"].get(off)
            if cell is not None:
                return cell[0]
            cell_lo = st["stack_mem"].get(off - 4)
            if cell_lo is not None:
                x = cell_lo[0]
                if is_word32_row(st, r_word(x)):
                    return r_high(x)
                return _w_high_of(st, x)
            return None

        def _frame_word_id(st, off):
            if off in st["frameW"]:
                return st["frameW"][off]
            fw = _frame_word_row(st, off)
            if fw is None:
                return None
            return st["tab"].find(("atom", r_word(fw)))

        def _frame_run(st, rname, n, sp_c):
            c_off = _frame_at_reg(st, rname)
            if c_off is None or not (sp_c <= c_off and c_off + n <= 0 and (n % 8) == 0):
                return None
            ids = []
            for k in range(n // 4):
                tid = _frame_word_id(st, c_off + 4 * k)
                if tid is None:
                    return None
                ids.append(tid)
            return c_off, tuple(ids)

        def _frame_fill(st, cw, nw):
            ids = []
            tab = st["tab"]
            for k in range(nw):
                tid = _frame_word_id(st, cw + 4 * k)
                if tid is not None:
                    ids.append(tid)
                else:
                    v = st["nvars"]
                    st["nvars"] += 1
                    ids.append(tab.w_atom(r_var(v)))
            return tuple(ids)

        def _call_frame_touch(st, c_fixeds, c_inouts):
            tab = st["tab"]
            for _, rn, cnt in list(c_fixeds) + list(c_inouts):
                c_off = _frame_at_reg(st, rn)
                if c_off is not None:
                    for k in range(cnt // 4):
                        off = c_off + 4 * k
                        if off not in st["frameW"]:
                            fw = _frame_word_row(st, off)
                            if fw is not None:
                                tab.w_atom(fw)

        def _call_touch(st, c_outs):
            if len(c_outs) == 1:
                _, rn, _ = c_outs[0]
                mo = _find_in_runs(st["regs"][rn], outs_list)
                if mo is not None:
                    w = mo[0]
                    if w in st["intact"]:
                        _, r_idx, n0 = outs_list[w]
                        j = _run_at(r_idx, fixeds_list + inouts_list)
                        if j is not None:
                            tab = st["tab"]
                            for k in range(n0 // 4):
                                st["wroteW"][(w, k)] = tab.intern(("input", j, k))
                        st["intact"].discard(w)

        def _call_run(st, rname, n):
            mo = _find_in_runs(st["regs"][rname], outs_list)
            if mo is None:
                return None
            w, off, n0 = mo
            if off[1]:
                return None
            c = off[0]
            onm, br, _ = outs_list[w]
            if not (0 <= c and (c % 4) == 0 and c + n <= n0 and (n % 4) == 0):
                return None
            if (onm, br, n0) not in inouts_list:
                return None
            if any(wnm == onm for wnm, _, _ in st["wrote"]):
                return None
            ids = []
            for k in range(n // 4):
                tid = st["wroteW"].get((w, c // 4 + k))
                if tid is None:
                    return None
                ids.append(tid)
            return w, c // 4, tuple(ids)

        def _fixed_part(st, rname, n):
            addr = st["regs"][rname]
            mf = _find_in_runs(addr, fixeds_list)
            if mf is not None:
                j, off, n0 = mf
                if (not off[1]) and 0 <= off[0] and off[0] + n <= n0:
                    return j, fixeds_list[j][1], off[0]
            for k, (br, lr) in enumerate(regions_list):
                if br < len(addr[1]) and addr[1][br] == 1:
                    off = r_sub(addr, r_var(br))
                    if (not off[1]) and 0 <= off[0] and r_plain(st["facts"], r_sub(r_var(lr), r_const(off[0] + n))):
                        return len(fixeds_list) + len(inouts_list) + k, br, off[0]
            return None

        def _region_part(st, rname, lname):
            addr = st["regs"][rname]
            lrow = st["regs"][lname]
            for br, lr in regions_list:
                if br < len(addr[1]) and addr[1][br] == 1:
                    off = r_sub(addr, r_var(br))
                    if r_plain(st["facts"], off) and r_plain(st["facts"], r_sub(r_var(lr), r_add(off, lrow))):
                        return br, off, lrow
            return None

        def _needs_of(c, c_rmap, st):
            def _covers(what):
                if what in fn["needs"]:
                    return True
                for w0, a0, k0 in fn["needsif"]:
                    if w0 == what and a0 in env and self.is_row(env[a0]):
                        v0 = env[a0]
                        if r_plain(st["facts"], r_sub(v0, r_const(k0))) and r_plain(st["facts"], r_sub(r_const(k0), v0)):
                            return True
                return False
            for w in c.get("needs", ()):
                if not _covers(w):
                    raise Refuse(f"callee `{c['name']}` needs CPU feature `{w}` not declared by caller")
            for w, arg, k in c.get("needsif", ()):
                if _covers(w):
                    continue
                rn = c_rmap.get(arg)
                if rn is None:
                    raise Refuse(f"callee `{c['name']}` conditional feature `{w}` not covered by caller")
                rv = st["regs"][rn]
                if r_plain(st["facts"], r_sub(r_const(k - 1), rv)) or r_plain(st["facts"], r_sub(rv, r_const(k + 1))):
                    continue
                ok_if = False
                for w0, a0, k0 in fn["needsif"]:
                    if w0 == w and k0 == k and a0 in env and self.is_row(env[a0]):
                        if _r_same_row(st["facts"], rv, env[a0]):
                            ok_if = True
                            break
                if not ok_if:
                    raise Refuse(f"callee `{c['name']}` conditional feature `{w}` not covered by caller")

        def _call_mbounds_ok(c, c_fixeds, sp_c, st, strm):
            for x, o, bd in c.get("mbounds", ()):
                for xnm, rn, n in c_fixeds:
                    if xnm != x:
                        continue
                    if o + 8 > n:
                        raise Refuse("a called function bounds bytes outside its fixed run")
                    fp = _fixed_part(st, rn, n)
                    if fp is not None and fp[0] < len(fixeds_list):
                        x0 = fixeds_list[fp[0]][0]
                        c0 = fp[2]
                        if any(x1 == x0 and o1 == c0 + o and bd1 <= bd for x1, o1, bd1 in fn["mbounds"]):
                            continue
                        raise Refuse("a called function bounds a number in a fixed run not bounded in caller")
                    cf = _frame_at_reg(st, rn)
                    if cf is not None and sp_c <= cf + o and cf + o + 8 <= 0 and (cf + o) in st["stack_mem"]:
                        self.entail(st["facts"], r_sub(r_const(bd - 1), st["stack_mem"][cf + o][0]), strm)
                        continue
                    raise Refuse("a called function bounds a number in memory not known to lie below that bound")

        def _val_expr_match(st_m, e1, e2, env1, env2):
            tab = st_m["tab"]
            if (isinstance(e1, tuple) and len(e1) >= 2 and e1[0] == "call"
                    and isinstance(e2, tuple) and len(e2) >= 2 and e2[0] == "call"
                    and e1[1] not in WOWN and e1[1] != "len"):
                if e1[1] != e2[1] or len(e1) != len(e2):
                    return False
                return all(_val_expr_match(st_m, a1, a2, env1, env2) for a1, a2 in zip(e1[2:], e2[2:]))
            v1 = _weval(tab, st_m, env1, e1)
            v2 = _weval(tab, st_m, env2, e2)
            if v1 is None or v2 is None:
                return False
            k1 = _flat_key(tab, v1)
            k2 = _flat_key(tab, v2)
            return k1 is not None and k2 is not None and _same_key(st_m["facts"], k1, k2)

        def _call_val_arrays_ok(c, c_vas, sp_c, cw_opt, wenv_c, st, strm):
            c_vs_map = {nm: (idx_nm, ex) for nm, idx_nm, ex in c.get("valspecs", ())}
            p_vs_map = {nm: (idx_nm, ex) for nm, idx_nm, ex in fn.get("valspecs", ())}
            tab = st["tab"]
            for xnm, rn, lrn, ch, el in c_vas:
                if not (ch > 0 and el > 0 and (el % 4) == 0):
                    raise Refuse("invalid value-array parameters")
                self.entail(st["facts"], st["regs"][lrn], strm)
                addr = st["regs"][rn]
                matched_va = None
                for x0, r0, l0, ch0, el0 in val_arrays_list:
                    d = r_sub(addr, r_var(r0))
                    if (not d[1]) and d[0] >= 0 and (d[0] % 4) == 0:
                        matched_va = (x0, l0, ch0, el0, d[0])
                        break
                if matched_va is not None:
                    x0, l0, ch0, el0, d0 = matched_va
                    if not (ch == ch0 and el == el0 and (d0 % el) == 0):
                        raise Refuse("called function value array does not align with caller value array")
                    shift = d0 // el
                    self.entail(st["facts"], r_sub(r_var(l0), r_add(r_const(shift * ch), st["regs"][lrn])), strm)
                    if xnm in c_vs_map:
                        if x0 not in p_vs_map:
                            raise Refuse("caller value array missing valspec required by callee")
                        idx_c, ex_c = c_vs_map[xnm]
                        idx_0, ex_0 = p_vs_map[x0]
                        u = st["nvars"]
                        st_m = clone(st)
                        st_m["nvars"] = u + 1
                        st_m["facts"] = FactList([
                            r_var(u), r_scale(ch, r_var(u)),
                            r_sub(st["regs"][lrn], r_add(r_scale(ch, r_var(u)), r_const(ch))),
                            r_sub(r_var(l0), r_add(r_scale(ch, r_var(u)), r_const((shift + 1) * ch))),
                        ])
                        st_m["facts"].extend(st["facts"])
                        e1_env = dict(wenv_c)
                        e1_env[idx_c] = ("num", r_var(u))
                        e2_env = _w_env()
                        e2_env[idx_0] = ("num", r_add(r_const(shift), r_var(u)))
                        if not _val_expr_match(st_m, ex_c, ex_0, e1_env, e2_env):
                            raise Refuse("called function value-array entries do not match caller value array")
                else:
                    cf = _frame_at_reg(st, rn)
                    if cf is None or not (sp_c <= cf <= 0):
                        raise Refuse("called function value array is neither a value-array slice nor in stack frame")
                    max_n = (-cf) // el
                    if xnm not in c_vs_map:
                        count = max_n
                    else:
                        idx_c, ex_c = c_vs_map[xnm]
                        count = 0
                        nw = el // 4
                        for ii in range(min(max_n, 64)):
                            off = cf + el * ii
                            if off + el > 0:
                                break
                            # Extract frame word IDs
                            fids = None
                            if (nw % 2) == 0:
                                frows = []
                                ok_f = True
                                for p in range(nw // 2):
                                    cell = st["stack_mem"].get(off + 8 * p)
                                    if cell is None or not is_word32_row(st, r_word(cell[0])):
                                        ok_f = False
                                        break
                                    frows.append(cell[0])
                                    frows.append(r_high(cell[0]))
                                if ok_f:
                                    tids = [tab.find(("atom", r_word(fr))) for fr in frows]
                                    if all(t is not None for t in tids):
                                        fids = tids
                            if fids is None:
                                if all((off + 4 * k) in st["frameW"] for k in range(nw)):
                                    fids = [st["frameW"][off + 4 * k] for k in range(nw)]
                            if fids is None:
                                break
                            ne = dict(wenv_c)
                            ne[idx_c] = ("int", ii)
                            wv = _weval(tab, st, ne, ex_c)
                            if wv is None or wv[0] != "list" or len(wv[1]) != nw:
                                break
                            if not all(w[0] == "word" and _w_id_of(tab, w[1]) == fid for w, fid in zip(wv[1], fids)):
                                break
                            count += 1
                    disjoint = True if cw_opt is None else (cf + el * count <= cw_opt[0] or cw_opt[0] + cw_opt[1] <= cf)
                    if not (sp_c <= cf and cf + el * count <= 0 and disjoint):
                        raise Refuse("called function value array in frame overlaps output or exceeds frame")
                    self.entail(st["facts"], r_sub(r_const((count + 1) * ch - 1), st["regs"][lrn]), strm)

        def _after_call_w(c, c_keeps, st, sp_c, w_idx, first_w, m_words, g_nm, keys, is_bytes=False, rec_fields=()):
            base_v = st["nvars"] + len(reg_names)
            is_rec = bool(rec_fields)
            tab = st["tab"]
            ids = tuple(tab.w_atom(r_var(base_v + k)) for k in range(m_words))
            st["stack_mem"] = {o: v for o, v in st["stack_mem"].items() if o >= sp_c}
            st["frameW"] = {o: v for o, v in st["frameW"].items() if o >= sp_c}
            old_nv = st["nvars"]
            st["nvars"] = base_v + m_words + (1 if is_rec else 0)
            for r_idx, r in enumerate(reg_names):
                if r != sp_reg and r not in c_keeps:
                    rv_i = r_var(old_nv + r_idx)
                    st["regs"][r] = rv_i
                    st["facts"].append(rv_i)
                    st["facts"].append(r_sub(r_const(M64), rv_i))
                    st["marks"][r] = True
            for k in range(m_words):
                vk = r_var(base_v + k)
                st["facts"].append(vk)
                st["facts"].append(r_sub(r_const(W32 - 1), vk))
                st["word32_vars"].add(base_v + k)
            if is_rec:
                st["facts"].extend(_rec_bound_facts(base_v, rec_fields))
            st["flags"] = {"zf": None, "cf": None}
            st["flag_marks"] = {"zf": True, "cf": True}
            st["intact"].discard(w_idx)
            c_kv = c.get("keeps_vec")
            if c_kv is not None:
                c_kv_set = {vec_reg_index(v) for v in c_kv if vec_reg_index(v) is not None}
            else:
                c_kv_set = set(range(8, 16)) if is_arm else set()
            st["vec_intact"] &= c_kv_set
            for k in range(m_words):
                st["wroteW"][(w_idx, first_w + k)] = ids[k]
            if is_rec:
                u = base_v + m_words
                st["known_use"].add(g_nm, keys, u)
                st["known_record"].insert(0, (u, rec_fields, ids))
            elif is_bytes:
                st["known_held_b"].add(g_nm, keys, ids)
            else:
                st["known_held"].add(g_nm, keys, ids)

        def _after_call_f(c, c_keeps, st, sp_c, cw, m_words, g_nm, keys, rec_fields=()):
            base_v = st["nvars"] + len(reg_names)
            is_rec = bool(rec_fields)
            tab = st["tab"]
            ids = tuple(tab.w_atom(r_var(base_v + k)) for k in range(m_words))
            st["stack_mem"] = {
                o: v for o, v in st["stack_mem"].items()
                if o >= sp_c and (o + 8 <= cw or cw + 4 * m_words <= o)
            }
            for j in range(m_words // 2):
                cell_r = r_add(r_var(base_v + 2 * j), r_scale(W32, r_var(base_v + 2 * j + 1)))
                st["stack_mem"][cw + 8 * j] = (cell_r, True)
            st["frameW"] = {
                o: v for o, v in st["frameW"].items()
                if o >= sp_c and (o + 4 <= cw or cw + 4 * m_words <= o)
            }
            old_nv = st["nvars"]
            st["nvars"] = base_v + m_words + (1 if is_rec else 0)
            for r_idx, r in enumerate(reg_names):
                if r != sp_reg and r not in c_keeps:
                    rv_i = r_var(old_nv + r_idx)
                    st["regs"][r] = rv_i
                    st["facts"].append(rv_i)
                    st["facts"].append(r_sub(r_const(M64), rv_i))
                    st["marks"][r] = True
            for k in range(m_words):
                vk = r_var(base_v + k)
                st["facts"].append(vk)
                st["facts"].append(r_sub(r_const(W32 - 1), vk))
                st["word32_vars"].add(base_v + k)
            if is_rec:
                st["facts"].extend(_rec_bound_facts(base_v, rec_fields))
            st["flags"] = {"zf": None, "cf": None}
            st["flag_marks"] = {"zf": True, "cf": True}
            c_kv = c.get("keeps_vec")
            if c_kv is not None:
                c_kv_set = {vec_reg_index(v) for v in c_kv if vec_reg_index(v) is not None}
            else:
                c_kv_set = set(range(8, 16)) if is_arm else set()
            st["vec_intact"] &= c_kv_set
            if is_rec:
                u = base_v + m_words
                st["known_use"].add(g_nm, keys, u)
                st["known_record"].insert(0, (u, rec_fields, ids))
            else:
                st["known_held"].add(g_nm, keys, ids)

        def _wval_ok(v, nvars, ntab):
            tv = v[0]
            if tv in ("int", "bool", "run", "part", "pbyte", "other"):
                return True
            if tv in ("num", "counter"):
                return len(v[1][1]) <= nvars
            if tv == "word":
                return all(p[0] < ntab for p in v[1])
            if tv == "list":
                return all(_wval_ok(x, nvars, ntab) for x in v[1])
            if tv == "use":
                return v[1] < nvars
            if tv == "wbytes":
                return all(i < ntab for i in v[1])
            return False

        def _can_name(e):
            if not isinstance(e, tuple) or not e:
                return False
            if e[0] in ("bin", "ifx", "call"):
                return True
            if e[0] == "let":
                return _can_name(e[3])
            return False

        def _nameval(st, wenv_c, e, fuel=250, skip_weval=False):
            if fuel <= 0:
                return None
            tab = st["tab"]
            if not skip_weval:
                v0 = _weval(tab, st, wenv_c, e)
                if v0 is not None:
                    if v0[0] == "num" and not v0[1][1]:
                        v0 = ("int", v0[1][0])
                    return v0 if _wval_ok(v0, st["nvars"], len(tab.arr)) else None
            if not isinstance(e, tuple) or not e:
                return None
            tag = e[0]
            if tag == "bin":
                op = e[1]
                xv = _nameval(st, wenv_c, e[2], fuel - 1)
                if xv is None:
                    return None
                yv = _nameval(st, wenv_c, e[3], fuel - 1)
                if yv is None:
                    return None
                # Evaluate binary op via _weval on synthetic names
                tmp_env = {"__x": xv, "__y": yv}
                rv = _weval(tab, st, tmp_env, ("bin", op, ("name", "__x"), ("name", "__y")), 4)
                if rv is not None:
                    return rv if _wval_ok(rv, st["nvars"], len(tab.arr)) else None
                if op == "|" and xv[0] == "num" and yv[0] == "int" and yv[1] >= 0:
                    a_r, b_r = xv[1], r_const(yv[1])
                    if r_plain(st["facts"], a_r) and r_plain(st["facts"], r_sub(r_const(M64), a_r)):
                        key_or = (a_r, b_r) if a_r <= b_r else (b_r, a_r)
                        if key_or not in st["or_cache"]:
                            nv = fresh_var(st, 0, M64)
                            st["or_cache"][key_or] = nv
                            st["facts"].append(r_sub(nv, a_r))
                            st["facts"].append(r_sub(nv, b_r))
                            st["facts"].append(r_sub(r_add(a_r, b_r), nv))
                        return ("num", st["or_cache"][key_or])
                return None
            if tag == "ifx":
                cv = _weval(tab, st, wenv_c, e[1])
                if cv == ("bool", True):
                    return _nameval(st, wenv_c, e[2], fuel - 1, skip_weval=True)
                if cv == ("bool", False):
                    return _nameval(st, wenv_c, e[3], fuel - 1, skip_weval=True)
                return None
            if tag == "let":
                nv0 = st["nvars"]
                xv = _nameval(st, wenv_c, e[2], fuel - 1)
                if xv is None:
                    return None
                ne = dict(wenv_c)
                ne[e[1]] = xv
                return _nameval(st, ne, e[3], fuel - 1, skip_weval=(st["nvars"] == nv0))
            if tag == "call":
                fn_nm = e[1]
                if fn_nm == "len" or fn_nm in WOWN or fn_nm not in self.defs:
                    return None
                dparams, dbody = self.defs[fn_nm]
                nv0 = st["nvars"]
                vs = []
                for ae in e[2:]:
                    av = _nameval(st, wenv_c, ae, fuel - 1)
                    if av is None:
                        return None
                    vs.append(av)
                if len(vs) != len(dparams):
                    return None
                ks = _flat_keys(tab, vs)
                if ks is None:
                    return _nameval(st, dict(zip(dparams, vs)), dbody, fuel - 1, skip_weval=(st["nvars"] == nv0))
                ids0 = st["known_held"].find(st["facts"], fn_nm, ks, _same_keys)
                if ids0 is not None:
                    if all(i < len(tab.arr) for i in ids0):
                        return ("list", [("word", ((i, 1),)) for i in ids0])
                    return None
                h0 = st["known_use"].find(st["facts"], fn_nm, ks, _same_keys)
                if h0 is not None:
                    return ("use", h0) if h0 < st["nvars"] else None
                if _can_name(dbody):
                    r_sub_v = _nameval(st, dict(zip(dparams, vs)), dbody, fuel - 1, skip_weval=(st["nvars"] == nv0))
                    if r_sub_v is not None:
                        return r_sub_v
                if all(_key_ok(k, st["nvars"], len(tab.arr)) for k in ks):
                    h_new = st["nvars"]
                    st["nvars"] += 1
                    st["known_use"].add(fn_nm, ks, h_new)
                    return ("use", h_new)
                return None
            return None

        def _do_sym_call(c, callee_nm, st, sp_c, extra, is_tail, strm):
            """Unified call / tail-call verification (symCallPlain / symCallB / symCallF / symCallW / symCallL)."""
            c_arg_regs = c["argregs"] if c["argregs"] is not None else (ARM_ARGS if is_arm else X86_ARGS)
            c_keeps = set(c["keeps"]) if c["keeps"] is not None else (ARM_CALLEE_SAVED if is_arm else X86_CALLEE_SAVED)
            c_ret_reg = c["retreg"] if c["retreg"] is not None else ("x0" if is_arm else "rax")
            c_rmap, c_outs, c_fixeds, c_inouts, c_regions, c_vas, c_tables = _c_runs(c, c_arg_regs)

            _needs_of(c, c_rmap, st)
            _sym_know(st)

            # Build scalar argument map for stack/atleast/linpre/decreases/below/requires checks
            cenv_num = {anm: st["regs"][c_arg_regs[i]] for i, (anm, _, _) in enumerate(c["args"])}
            _check_call_stack(c, sp_c, extra, cenv_num, st["facts"], strm)
            _call_mbounds_ok(c, c_fixeds, sp_c, st, strm)
            for anm, bnd in c["atleast"]:
                if anm in cenv_num:
                    self.entail(st["facts"], r_sub(cenv_num[anm], r_const(bnd)), strm)
            for k, terms in c["linpre"]:
                self.entail(st["facts"], self.linpre_row(k, terms, cenv_num), strm)
            _check_call_align_ld(c, c_arg_regs, st)
            if (not is_tail) and callee_nm == fn["name"]:
                dnm = fn["decreases"]
                self.entail(st["facts"], r_sub(r_sub(env[dnm], cenv_num[dnm]), r_const(1)), strm)

            # Trace cleanliness check on callee arguments (matching Core.lean `callQuiet` / `quietAtCall`)
            for i, (anm, ak, alen) in enumerate(c["args"]):
                rn = c_arg_regs[i]
                if ak == "number":
                    if anm not in c["hidden"] and st["marks"][rn]:
                        raise Refuse(f"callee `{callee_nm}` trace arg `{anm}` may depend on values kept out of trace")
                elif ak == "bytes":
                    if st["marks"][rn]:
                        raise Refuse(f"callee `{callee_nm}` pointer arg `{anm}` may depend on values kept out of trace")
                    if anm not in c["hidden"]:
                        # Must be a whole clean caller buffer
                        found_b = None
                        for bnm, bbase in st["buf_base"].items():
                            if st["regs"][rn] == bbase:
                                found_b = bnm
                                break
                        if found_b is None or not st["buf_clean"][found_b]:
                            raise Refuse(f"callee `{callee_nm}` exposes buffer kept out of caller trace")
                elif ak == "fixed":
                    if st["marks"][rn]:
                        raise Refuse(f"callee `{callee_nm}` pointer arg `{anm}` may depend on values kept out of trace")
                    if anm not in c["hidden"]:
                        cf = _frame_at_reg(st, rn)
                        cnt = int(alen)
                        if cf is None or (cnt % 8) != 0 or any(
                                (cf + 8 * k) not in st["stack_mem"] or st["stack_mem"][cf + 8 * k][1]
                                for k in range(cnt // 8)):
                            raise Refuse(f"callee `{callee_nm}` exposes fixed buffer kept out of caller trace")
                else:
                    if st["marks"][rn]:
                        raise Refuse(f"callee `{callee_nm}` pointer arg `{anm}` may depend on values kept out of trace")

            # Dispatch by call category (matching Core.lean `symCall'`)
            # Case 1: `symCallL` (callee takes a table of lane addresses in stack frame)
            if c.get("lanes"):
                if c_vas:
                    raise Refuse("callee with both lane table and valarray not handled")
                _call_frame_touch(st, c_fixeds, c_inouts)
                if not (not c_inouts and not c["ensures"] and not c_regions and c["returns"] is None and c["result"] is None):
                    raise Refuse("lane-table callee with extra outputs not handled")
                if len(c_outs) != 1 or len(c_tables) != 1:
                    raise Refuse("lane-table callee must have one out and one table")
                run_o, ro, n_o = c_outs[0]
                tx, tr, cnt_t, lr_t = c_tables[0]
                nb_r = st["regs"][lr_t]
                cw = _frame_at_reg(st, ro)
                ct = _frame_at_reg(st, tr)
                if nb_r[1] or nb_r[0] < 0 or cw is None or ct is None:
                    raise Refuse("lane-table callee block count or frame buffers not constant")
                nb = nb_r[0]
                if not (sp_c <= cw and cw + n_o <= 0 and (n_o % 8) == 0 and sp_c <= ct and ct + 8 * cnt_t <= 0
                        and (ct + 8 * cnt_t <= cw or cw + n_o <= ct)):
                    raise Refuse("lane-table callee table/output outside frame or overlapping")
                for _, frn, fcnt in c_fixeds:
                    cf = _frame_at_reg(st, frn)
                    if cf is not None and not (cf + fcnt <= cw or cw + n_o <= cf):
                        raise Refuse("lane-table callee fixed input overlaps output in frame")
                # Intern fixed-part nodes
                tab = st["tab"]
                for _, ak, alen in c["args"]:
                    pass
                for i, (anm, ak, alen) in enumerate(c["args"]):
                    if ak == "fixed":
                        fp = _fixed_part(st, c_arg_regs[i], int(alen))
                        if fp is not None and (fp[2] % 4) == 0:
                            for kw in range(int(alen) // 4):
                                tab.intern(("input", fp[0], fp[2] // 4 + kw))
                # Extract `cnt_t` lane block lists from stack table at `ct`
                lanes_val = []
                for li in range(cnt_t):
                    cell = st["stack_mem"].get(ct + 8 * li)
                    if cell is None:
                        raise Refuse("lane table cell missing in stack frame")
                    a = cell[0]
                    lids = None
                    mf = _find_in_runs(a, fixeds_list)
                    if mf is not None and not mf[1][1] and 0 <= mf[1][0] and (mf[1][0] % 4) == 0 and mf[1][0] + 64 * nb <= mf[2]:
                        lids = [tab.intern(("input", mf[0], mf[1][0] // 4 + k)) for k in range(16 * nb)]
                    else:
                        for kr, (br, lr) in enumerate(regions_list):
                            if br < len(a[1]) and a[1][br] == 1:
                                off = r_sub(a, r_var(br))
                                if (not off[1]) and 0 <= off[0] and (off[0] % 4) == 0 and r_plain(st["facts"], r_sub(r_var(lr), r_const(off[0] + 64 * nb))):
                                    j = len(fixeds_list) + len(inouts_list) + kr
                                    lids = [tab.intern(("input", j, off[0] // 4 + k)) for k in range(16 * nb)]
                                    break
                        if lids is None:
                            fo = r_sub(a, entry_regs[sp_reg])
                            if (not fo[1]) and sp_c <= fo[0] and fo[0] + 64 * nb <= 0 and (fo[0] + 64 * nb <= cw or cw + n_o <= fo[0]):
                                frows = []
                                ok_fr = True
                                for kw in range(16 * nb):
                                    fw = _frame_word_row(st, fo[0] + 4 * kw)
                                    if fw is None:
                                        ok_fr = False
                                        break
                                    frows.append(fw)
                                if ok_fr:
                                    lids = [tab.w_atom(fr) for fr in frows]
                    if lids is None:
                        raise Refuse("lane address in table does not point to known blocks")
                    blocks = [("list", [("word", ((tid, 1),)) for tid in lids[16 * b:16 * (b + 1)]]) for b in range(nb)]
                    lanes_val.append(("list", blocks))
                # Build calleeL word env
                wenv_l = {tx: ("list", lanes_val)}
                for i, (anm, ak, alen) in enumerate(c["args"]):
                    rn = c_arg_regs[i]
                    if ak == "number":
                        wenv_l[anm] = ("num", st["regs"][rn])
                    elif ak == "fixed":
                        if anm == tx:
                            if rn != tr or int(alen) != 8 * cnt_t:
                                raise Refuse("lane table argument mismatch")
                        else:
                            fp = _fixed_part(st, rn, int(alen))
                            if fp is not None:
                                wenv_l[anm] = ("part", fp[1], fp[2], int(alen))
                            else:
                                fr = _frame_run(st, rn, int(alen), sp_c)
                                if fr is None:
                                    raise Refuse("lane-table callee fixed arg not in readable run or frame")
                                wenv_l[anm] = ("wbytes", fr[1])
                # Name each lane's ensuresw words (`nameLanes`)
                out_rows = []
                a_off = 0
                for erun, epart, eval_e in c["ensuresw"]:
                    if epart is None or erun != run_o or epart[0] != a_off or (epart[1] % 4) != 0:
                        raise Refuse("lane-table callee ensuresw does not partition output run")
                    m_bytes = epart[1]
                    use_hit = None
                    if isinstance(eval_e, tuple) and len(eval_e) == 3 and eval_e[0] == "call" and eval_e[1] == "bytes_of":
                        nv = _nameval(st, wenv_l, eval_e[2])
                        if nv is not None and nv[0] == "use":
                            use_hit = st["known_use"].by_val.get(nv[1])
                    nw = m_bytes // 4
                    base_w = st["nvars"]
                    st["nvars"] += nw
                    w_rows = [r_var(base_w + k) for k in range(nw)]
                    w_ids = tuple(tab.w_atom(wr) for wr in w_rows)
                    for k in range(nw):
                        st["word32_vars"].add(base_w + k)
                        st["facts"].append(r_var(base_w + k))
                        st["facts"].append(r_sub(r_const(W32 - 1), r_var(base_w + k)))
                    if use_hit is not None:
                        st["known_held"].add(use_hit[0], use_hit[1], w_ids)
                    out_rows.extend(w_rows)
                    a_off += m_bytes
                if len(out_rows) * 4 != n_o:
                    raise Refuse("lane-table callee ensuresw word count mismatch")
                for anm, bnd in c["below"]:
                    if anm in cenv_num:
                        self.entail(st["facts"], r_sub(r_const(bnd - 1), cenv_num[anm]), strm)
                # `Sym.afterCallL`
                st["stack_mem"] = {
                    o: v for o, v in st["stack_mem"].items()
                    if o >= sp_c and (o + 8 <= cw or cw + n_o <= o)
                }
                for j in range(len(out_rows) // 2):
                    cell_r = r_add(out_rows[2 * j], r_scale(W32, out_rows[2 * j + 1]))
                    st["stack_mem"][cw + 8 * j] = (cell_r, True)
                st["frameW"] = {
                    o: v for o, v in st["frameW"].items()
                    if o >= sp_c and (o + 4 <= cw or cw + n_o <= o)
                }
                old_nv = st["nvars"]
                st["nvars"] += len(reg_names)
                for r_idx, r in enumerate(reg_names):
                    if r != sp_reg and r not in c_keeps:
                        rv_i = r_var(old_nv + r_idx)
                        st["regs"][r] = rv_i
                        st["facts"].append(rv_i)
                        st["facts"].append(r_sub(r_const(M64), rv_i))
                        st["marks"][r] = True
                st["flags"] = {"zf": None, "cf": None}
                st["flag_marks"] = {"zf": True, "cf": True}
                c_kv = c.get("keeps_vec")
                c_kv_set = {vec_reg_index(v) for v in c_kv if vec_reg_index(v) is not None} if c_kv is not None else (set(range(8, 16)) if is_arm else set())
                st["vec_intact"] &= c_kv_set
                return

            # Case 2: `symCallPlain` (scalar / byte-reading callee with no output/fixed/inout/ensuresw)
            if not c_outs and not c["ensures"] and not c_fixeds and not c_inouts and not c["ensuresw"]:
                if c_vas:
                    raise Refuse("plain callee with valarray not handled")
                cenv = {}
                for i, (anm, ak, alen) in enumerate(c["args"]):
                    rn = c_arg_regs[i]
                    if ak == "bytes":
                        found_buf = None
                        for bnm, bbase in st["buf_base"].items():
                            if st["regs"][rn] == bbase:
                                found_buf = bnm
                                break
                        if found_buf is None:
                            raise Refuse(f"callee `{callee_nm}` bytes arg `{anm}` does not match a caller buffer")
                        cenv[anm] = ("buf", found_buf)
                    else:
                        cenv[anm] = st["regs"][rn]
                for anm, bnd in c["below"]:
                    if anm in cenv:
                        self.entail(st["facts"], r_sub(r_const(bnd - 1), cenv[anm]), strm)
                for req in c["requires"]:
                    self.check_fact(req, cenv, st, strm)
                st["stack_mem"] = {o: v for o, v in st["stack_mem"].items() if o >= sp_c}
                st["frameW"] = {o: v for o, v in st["frameW"].items() if o >= sp_c}
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
                    ret_val = self.eval_sexpr(c["returns"], cenv, st, strm)
                    rv = st["regs"][c_ret_reg]
                    if self.is_row(ret_val):
                        st["facts"].append(r_sub(rv, ret_val))
                        st["facts"].append(r_sub(ret_val, rv))
                    else:
                        st["eqs"].insert(0, (ret_val, rv))
                    st["marks"][c_ret_reg] = False
                return

            # Case 3: `symCallB` (byte-level ensures writing to a caller inout word run, e.g. `b3l_pad`)
            if not c_inouts and not c["ensuresw"]:
                if c_vas or c["mbounds"] or c_fixeds or c["returns"] is not None or c["result"] is not None:
                    raise Refuse("byte-output callee with extra clauses not handled")
                _call_touch(st, c_outs)
                if len(c_outs) != 1 or len(c["ensures"]) != 1:
                    raise Refuse("byte-output callee must have one out and one ensures")
                run_o, ro, n_o = c_outs[0]
                erun, elo, ehi, eval_e = c["ensures"][0]
                if not (erun == run_o and elo == ("num", "0") and ehi == ("num", str(n_o))):
                    raise Refuse("byte-output callee ensures must cover full out run")
                cr = _call_run(st, ro, n_o)
                if cr is None:
                    raise Refuse("byte-output callee out run not whole known words of caller inout")
                w_idx, first_w, _ = cr
                wenv_b = {}
                for i, (anm, ak, alen) in enumerate(c["args"]):
                    rn = c_arg_regs[i]
                    if ak == "number":
                        wenv_b[anm] = ("num", st["regs"][rn])
                    elif ak == "bytes" and alen in c_rmap:
                        rp = _region_part(st, rn, c_rmap[alen])
                        if rp is None:
                            raise Refuse(f"callee `{callee_nm}` bytes arg `{anm}` is not a valid sub-slice of caller buffer")
                        wenv_b[anm] = ("span", rp[0], rp[1], rp[2])
                if not (isinstance(eval_e, tuple) and len(eval_e) >= 2 and eval_e[0] == "call"):
                    raise Refuse("byte-output callee ensures must be a definition call")
                g_nm = eval_e[1]
                if g_nm in WOWN or g_nm == "len" or g_nm not in self.defs:
                    raise Refuse("byte-output callee ensures definition missing")
                tab = st["tab"]
                vs = [_weval(tab, st, wenv_b, ae) for ae in eval_e[2:]]
                if any(v is None for v in vs):
                    raise Refuse("byte-output callee ensures arguments not followed")
                ks = _flat_keys(tab, vs)
                if ks is None or len(ks) != len(self.defs[g_nm][0]) or not all(_key_ok(k, st["nvars"], len(tab.arr)) for k in ks):
                    raise Refuse("byte-output callee ensures keys invalid")
                for anm, bnd in c["below"]:
                    if anm in cenv_num:
                        self.entail(st["facts"], r_sub(r_const(bnd - 1), cenv_num[anm]), strm)
                _after_call_w(c, c_keeps, st, sp_c, w_idx, first_w, n_o // 4, g_nm, ks, is_bytes=True)
                return

            # Case 4 & 5: `symCallF` (writes into caller stack frame) or `symCallW` (writes into caller inout run)
            in_frame = any(_frame_at_reg(st, rn) is not None for _, rn, _ in c_outs)
            if in_frame:
                _call_frame_touch(st, c_fixeds, c_inouts)
            else:
                _call_touch(st, c_outs)
                _call_frame_touch(st, c_fixeds, c_inouts)

            if len(c_outs) != 1 or len(c_inouts) != 1 or len(c["ensuresw"]) != 1:
                raise Refuse("word-output callee must have one inout run and one ensuresw")
            run_o, ro, n_o = c_outs[0]
            run_i, ri, n_i = c_inouts[0]
            erun, epart, eval_e = c["ensuresw"][0]
            if not (run_o == run_i and ro == ri and n_o == n_i and erun == run_o and epart is None):
                raise Refuse("word-output callee inout/ensuresw mismatch")

            tab = st["tab"]
            for i, (anm, ak, alen) in enumerate(c["args"]):
                if ak == "fixed":
                    fp = _fixed_part(st, c_arg_regs[i], int(alen))
                    if fp is not None and (fp[2] % 4) == 0:
                        for kw in range(int(alen) // 4):
                            tab.intern(("input", fp[0], fp[2] // 4 + kw))

            cw_opt = None
            if in_frame:
                cw = _frame_at_reg(st, ro)
                if cw is None or not (sp_c <= cw and cw + n_o <= 0 and (n_o % 8) == 0):
                    raise Refuse("word-output callee frame buffer outside frame or misaligned")
                for _, frn, fcnt in c_fixeds:
                    cf = _frame_at_reg(st, frn)
                    if cf is not None and not (cf + fcnt <= cw or cw + n_o <= cf):
                        raise Refuse("word-output callee fixed input overlaps output in frame")
                out_ids = _frame_fill(st, cw, n_o // 4)
                w_idx, first_w = 0, 0
                cw_opt = (cw, n_o)
            else:
                cr = _call_run(st, ro, n_o)
                if cr is None:
                    raise Refuse("word-output callee inout run not whole known words of caller inout")
                w_idx, first_w, out_ids = cr

            wenv_w = {}
            for i, (anm, ak, alen) in enumerate(c["args"]):
                rn = c_arg_regs[i]
                if ak == "number":
                    wenv_w[anm] = ("num", st["regs"][rn])
                elif ak == "fixed":
                    fp = _fixed_part(st, rn, int(alen))
                    if fp is not None:
                        wenv_w[anm] = ("part", fp[1], fp[2], int(alen))
                    else:
                        fr = _frame_run(st, rn, int(alen), sp_c)
                        if fr is None:
                            raise Refuse(f"callee `{callee_nm}` fixed arg `{anm}` not in readable run or frame")
                        wenv_w[anm] = ("wbytes", fr[1])
                elif ak == "bytes" and alen in c_rmap:
                    rp = _region_part(st, rn, c_rmap[alen])
                    if rp is None:
                        raise Refuse(f"callee `{callee_nm}` bytes arg `{anm}` is not a valid sub-slice of caller buffer")
                    wenv_w[anm] = ("span", rp[0], rp[1], rp[2])
                elif ak == "inout":
                    wenv_w[anm] = ("wbytes", out_ids)

            if not (isinstance(eval_e, tuple) and len(eval_e) == 3 and eval_e[0] == "call" and eval_e[1] == "bytes_of"):
                raise Refuse("word-output callee ensuresw must be `(call bytes_of ...)`")
            inner_e = eval_e[2]
            rec_fields = ()
            if isinstance(inner_e, tuple) and len(inner_e) >= 2 and inner_e[0] == "call":
                g_nm = inner_e[1]
                g_args = inner_e[2:]
            elif (isinstance(inner_e, tuple) and len(inner_e) == 4 and inner_e[0] == "let"
                  and isinstance(inner_e[2], tuple) and len(inner_e[2]) >= 2 and inner_e[2][0] == "call"
                  and not c_vas):
                rec_x = inner_e[1]
                g_nm = inner_e[2][1]
                g_args = inner_e[2][2:]
                parsed_f = _parse_rec_body(rec_x, inner_e[3])
                if parsed_f is None or g_nm not in self.defs:
                    raise Refuse("word-output callee serialized record layout invalid")
                fnames = [rf[1] for rf in parsed_f]
                if (sum(_rec_field_nwords(rf) for rf in parsed_f) != n_o // 4
                        or len(set(fnames)) != len(fnames)
                        or not _returns_record(fnames, self.defs[g_nm][1])):
                    raise Refuse("word-output callee serialized record does not match definition")
                rec_fields = tuple(parsed_f)
            else:
                raise Refuse("word-output callee ensuresw shape not handled")

            if g_nm in WOWN or g_nm == "len" or g_nm not in self.defs:
                raise Refuse("word-output callee ensuresw definition missing")
            vs = [_weval(tab, st, wenv_w, ae) for ae in g_args]
            if any(v is None for v in vs):
                raise Refuse("word-output callee ensuresw arguments not followed")
            ks = _flat_keys(tab, vs)
            if ks is None or len(ks) != len(self.defs[g_nm][0]) or not all(_key_ok(k, st["nvars"], len(tab.arr)) for k in ks):
                raise Refuse("word-output callee ensuresw keys invalid")

            for anm, bnd in c["below"]:
                if anm in cenv_num:
                    self.entail(st["facts"], r_sub(r_const(bnd - 1), cenv_num[anm]), strm)
            _call_val_arrays_ok(c, c_vas, sp_c, cw_opt, wenv_w, st, strm)

            if in_frame:
                _after_call_f(c, c_keeps, st, sp_c, cw_opt[0], n_o // 4, g_nm, ks, rec_fields=rec_fields)
            else:
                _after_call_w(c, c_keeps, st, sp_c, w_idx, first_w, n_o // 4, g_nm, ks, is_bytes=False, rec_fields=rec_fields)

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
                if op in ("add64", "at"):
                    a, ma = eval_table_expr(args[0], bind, st)
                    b, mb = eval_table_expr(args[1], bind, st)
                    raw = r_add(a, b)
                    if r_plain(st["facts"], raw) and r_plain(st["facts"], r_sub(r_const(M64), raw)):
                        return raw, (ma or mb)
                    ub_raw = row_word32_upper(st, raw)
                    if ub_raw is not None and ub_raw <= M64:
                        return raw, (ma or mb)
                    res = r_add(r_signed(a), r_signed(b))
                    plain_ok = r_plain(st["facts"], res) and r_plain(st["facts"], r_sub(r_const(M64), res))
                    if not plain_ok:
                        ub_res = row_word32_upper(st, res)
                        if ub_res is not None and ub_res <= M64:
                            return res, (ma or mb)
                    if (not plain_ok) and stream.pos < len(stream.items) and stream.items[stream.pos][0] == "t" and stream.items[stream.pos][1] == "wrap":
                        stream.pos += 1
                        return sym_low(r_add(a, b), M64 + 1, st), (ma or mb)
                    self.entail(st["facts"], res, stream)
                    self.entail(st["facts"], r_sub(r_const(M64), res), stream)
                    return res, (ma or mb)
                if op == "sub64":
                    a, ma = eval_table_expr(args[0], bind, st)
                    b, mb = eval_table_expr(args[1], bind, st)
                    res = r_sub(r_signed(a), r_signed(b))
                    plain_ok = r_plain(st["facts"], res) and r_plain(st["facts"], r_sub(r_const(M64), res))
                    if (not plain_ok) and stream.pos < len(stream.items) and stream.items[stream.pos][0] == "t" and stream.items[stream.pos][1] == "wrap":
                        stream.pos += 1
                        return sym_low(r_add(r_sub(a, b), r_const(M64 + 1)), M64 + 1, st), (ma or mb)
                    self.entail(st["facts"], res, stream)
                    self.entail(st["facts"], r_sub(r_const(M64), res), stream)
                    return res, (ma or mb)
                if op == "or64":
                    a, ma = eval_table_expr(args[0], bind, st)
                    b, mb = eval_table_expr(args[1], bind, st)
                    def _or_known(x, y):
                        if (x, y) in st["or_cache"]:
                            return st["or_cache"][(x, y)]
                        if (y, x) in st["or_cache"]:
                            return st["or_cache"][(y, x)]
                        v = fresh_var(st, 0, M64)
                        st["or_cache"][(x, y)] = v
                        st["facts"].append(r_sub(v, x))
                        st["facts"].append(r_sub(v, y))
                        for kbits in (8, 16, 32):
                            lim = (1 << kbits) - 1
                            if r_plain(st["facts"], r_sub(r_const(lim), x)) and r_plain(st["facts"], r_sub(r_const(lim), y)):
                                st["facts"].append(r_sub(r_const(lim), v))
                                break
                        return v
                    def _small_bits(x):
                        for jbits in (8, 16, 32):
                            if r_plain(st["facts"], x) and r_plain(st["facts"], r_sub(r_const((1 << jbits) - 1), x)):
                                return jbits
                        return None
                    def _or_small(x, k, jbits):
                        powj = 1 << jbits
                        if k % powj == 0:
                            return r_add(x, r_const(k))
                        u = _or_known(x, r_const(k % powj))
                        return r_add(u, r_const(k - (k % powj)))
                    if (not b[1]) and b[0] == 0:
                        return a, (ma or mb)
                    if (not a[1]) and a[0] == 0:
                        return b, (ma or mb)
                    def _disjoint_or(x, y):
                        u = r_row_upper(st["facts"], y, st["word32_vars"])
                        if u is None or u < 0 or (u == 0 and not any(c != 0 for c in x[1])):
                            return False
                        for jbits in range(1, 64):
                            m = 1 << jbits
                            if u < m and (x[0] % m == 0) and all(c % m == 0 for c in x[1]):
                                return True
                        return False
                    if _disjoint_or(a, b) or _disjoint_or(b, a):
                        return r_add(a, b), (ma or mb)
                    kb = r_const_of(st["facts"], b)
                    ja = _small_bits(a) if kb is not None else None
                    if kb is not None and ja is not None and (1 << ja) <= kb:
                        return _or_small(a, kb, ja), (ma or mb)
                    ka = r_const_of(st["facts"], a)
                    jb = _small_bits(b) if ka is not None else None
                    if ka is not None and jb is not None and (1 << jb) <= ka:
                        return _or_small(b, ka, jb), (ma or mb)
                    return _or_known(a, b), (ma or mb)
                if op == "shl64":
                    a, ma = eval_table_expr(args[0], bind, st)
                    b, mb = eval_table_expr(args[1], bind, st)
                    bk = r_const_of(st["facts"], b)
                    if bk is None or bk < 0 or bk >= 64:
                        raise Refuse("non-constant or out-of-range shift in shl64")
                    k = bk
                    if not a[1]:
                        return r_const(((a[0] & M64) << k) & M64), (ma or mb)
                    if k <= 32 and is_word32_row(st, a):
                        return r_scale(1 << k, a), (ma or mb)
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
                    bk = r_const_of(st["facts"], b)
                    if bk is None or bk < 0 or bk >= 64:
                        raise Refuse("non-constant or out-of-range shift in shr64")
                    k = bk
                    if not a[1]:
                        return r_const((a[0] & M64) >> k), (ma or mb)
                    return sym_quot(a, 1 << k, st), (ma or mb)
                if op == "and64":
                    a, ma = eval_table_expr(args[0], bind, st)
                    b, mb = eval_table_expr(args[1], bind, st)
                    bm = r_const_of(st["facts"], b)
                    if bm is not None:
                        val_x, mask_m = a, bm
                    else:
                        am = r_const_of(st["facts"], a)
                        if am is None:
                            raise Refuse(f"unsupported and64 mask {b}")
                        val_x, mask_m = b, am
                    if mask_m == 0:
                        return r_const(0), (ma or mb)
                    sp = mask_span(mask_m)
                    if sp is None:
                        raise Refuse(f"unsupported and64 mask {mask_m}")
                    k, w = sp
                    if k == 0:
                        if _is_aligned(val_x, 1 << w):
                            return r_const(0), (ma or mb)
                        return sym_low(val_x, 1 << w, st), (ma or mb)
                    if k + w == 64:
                        if _is_aligned(val_x, 1 << k):
                            return val_x, (ma or mb)
                        q = sym_quot(val_x, 1 << k, st)
                        return r_scale(1 << k, q), (ma or mb)
                    q1 = sym_quot(val_x, 1 << k, st)
                    rem2 = sym_low(q1, 1 << w, st)
                    return r_scale(1 << k, rem2), (ma or mb)
                if op == "low32":
                    a, ma = eval_table_expr(args[0], bind, st)
                    return sym_low(a, 1 << 32, st), ma
                if op == "low8":
                    a, ma = eval_table_expr(args[0], bind, st)
                    if args[0][0] == "name":
                        rn = bind.get(args[0][1], args[0][1])
                        if rn in st["low_clean"]:
                            ma = False
                    return sym_low(a, 256, st), ma
                if op == "sub8":
                    a, ma = eval_table_expr(args[0], bind, st)
                    b, mb = eval_table_expr(args[1], bind, st)
                    yb = sym_low(b, 256, st)
                    return sym_low(r_sub(r_add(a, r_const(256)), yb), 256, st), (ma or mb)
                if op == "setlow8":
                    a, ma = eval_table_expr(args[0], bind, st)
                    b, mb = eval_table_expr(args[1], bind, st)
                    q = sym_quot(a, 256, st)
                    bl = sym_low(b, 256, st)
                    return r_add(r_scale(256, q), bl), (ma or mb)
                if op == "data":
                    a, ma = eval_table_expr(args[0], bind, st)
                    if not data_bytes or a[1] or not (0 <= a[0] < len(data_bytes)):
                        raise Refuse("`data(I)` out of range or function has no read-only data")
                    return r_add(data_var_row, r_const(a[0])), ma
                if op == "equal":
                    a, ma = eval_table_expr(args[0], bind, st)
                    b, mb = eval_table_expr(args[1], bind, st)
                    return ("eq", a, b), (ma or mb)
                if op == "below":
                    a, ma = eval_table_expr(args[0], bind, st)
                    b, mb = eval_table_expr(args[1], bind, st)
                    return ("lt", a, b), (ma or mb)
                if op in ("mem8", "mem16", "mem32", "mem64"):
                    sz_map = {"mem8": 1, "mem16": 2, "mem32": 4, "mem64": 8}
                    msz = sz_map[op]
                    base, mb = eval_table_expr(args[0], bind, st)
                    disp, md = eval_table_expr(args[1], bind, st)
                    addr = r_add(r_signed(base), r_signed(disp))
                    if mb or md:
                        raise Refuse(f"{op} address depends on values kept out of the trace")
                    # 1. Stack frame (8-byte `stack_mem` or word-backed `frameW`)
                    off_row = r_sub(addr, entry_regs[sp_reg])
                    if not off_row[1]:
                        sp_c = _cur_sp_off(st)
                        if sp_c is not None and sp_c <= off_row[0] and off_row[0] + msz <= 0:
                            if msz == 8:
                                if off_row[0] in st["stack_mem"]:
                                    return st["stack_mem"][off_row[0]]
                                if all((off_row[0] + 4 * k) in st["frameW"] for k in range(2)):
                                    return _sym_load_word_scalar(st, addr, 8), True
                                raise Refuse("a read of the frame where nothing was written")
                            if msz == 4:
                                return _sym_load_word_scalar(st, addr, 4), True
                            raise Refuse("a read of the frame that is not 4 or 8 bytes")
                    # 2. Read-only file data
                    doff = _data_off(addr)
                    if doff is not None:
                        if msz in (1, 4, 8) and 0 <= doff and doff + msz <= len(data_bytes):
                            return r_const(_data_word(doff, msz)), False
                        raise Refuse("a read of the file's read-only data out of bounds")
                    # 3. Byte-addressed `bytes` regions
                    def counted_from(bbase):
                        vs = [i for i, cf in enumerate(bbase[1]) if cf != 0]
                        return (bbase[0] == 0 and len(vs) == 1 and bbase[1][vs[0]] == 1
                                and vs[0] < len(addr[1]) and addr[1][vs[0]] == 1)
                    for bnm, bbase in st["buf_base"].items():
                        if not counted_from(bbase):
                            continue
                        idx0 = r_sub(addr, bbase)
                        acc = r_const(0)
                        mul = 1
                        for k_off in range(msz):
                            idx_k = idx0 if k_off == 0 else r_add(idx0, r_const(k_off))
                            self.entail(st["facts"], idx_k, stream)
                            self.entail(st["facts"], r_sub(r_sub(st["buf_len"][bnm], idx_k), r_const(1)), stream)
                            bk_row = st["get_byte"](bnm, idx_k, st, stream)
                            acc = r_add(acc, r_scale(mul, bk_row))
                            mul *= 256
                        return acc, (not st["buf_clean"][bnm])
                    # 4. In-out / out runs (4B & 8B word loads; pure write-only `out` is refused!)
                    mo = _find_in_runs(addr, outs_list)
                    if mo is not None:
                        if msz in (4, 8):
                            return _sym_load_word_scalar(st, addr, msz), True
                        raise Refuse("a read of a run given only to write")
                    # 5. Fixed read-only word runs (`mem32` -> word scalar; `mem64` -> `known_load` + `mbounds`)
                    mf = _find_in_runs(addr, fixeds_list)
                    if mf is not None:
                        fj, foff, fcnt = mf
                        fnm = fixeds_list[fj][0]
                        fmk = fnm in fn["hidden"]
                        if msz == 4:
                            return _sym_load_word_scalar(st, addr, 4), fmk
                        if msz == 8 and (not foff[1]) and 0 <= foff[0] and foff[0] + 8 <= fcnt:
                            c = foff[0]
                            if (fj, c) in st["known_load"]:
                                return r_var(st["known_load"][(fj, c)]), fmk
                            v = st["nvars"]
                            st["nvars"] += 1
                            vr = r_var(v)
                            st["known_load"][(fj, c)] = v
                            st["known_load_of"][v] = (fj, c)
                            st["facts"].append(vr)
                            st["facts"].append(r_sub(r_const(M64), vr))
                            for m_nm, m_off, m_bnd in fn.get("mbounds", ()):
                                if m_nm == fnm and m_off == c:
                                    st["facts"].append(r_sub(r_const(m_bnd - 1), vr))
                            return vr, fmk
                        raise Refuse("a read of a fixed run that is not 4 or 8 bytes within it")
                    # 6. Read-only value arrays
                    if msz in (4, 8):
                        for _, r_idx, _, _, _ in val_arrays_list:
                            d = r_sub(addr, r_var(r_idx))
                            if not d[1] and d[0] >= 0 and (d[0] % 4) == 0:
                                return _sym_load_word_scalar(st, addr, msz), True
                    raise Refuse(f"{op} address does not fall in any contract buffer or stack slot")
                if op == "on16":
                    rv = _sym_reg_val(bind, st, ex)
                    if rv is not None:
                        return rv
                    return eval_table_expr(args[0], bind, st)
                raise Refuse(f"table op `{op}` not handled in verify2")
            raise Refuse(f"unsupported table expr {ex} in verify2")

        def _each_of(f_name, nargs):
            if f_name not in self.defs:
                return None
            params, body = self.defs[f_name]
            if (len(params) == nargs and isinstance(body, tuple) and len(body) == 5
                    and body[0] == "each" and body[3] == ("num", "0")
                    and isinstance(body[4], tuple) and len(body[4]) == 2 and body[4][0] == "num"):
                hi = int(body[4][1])
                if hi >= 0:
                    return params, body[2], body[1], hi
            return None

        def _wrote_at(wrote_list, run_nm, place_row):
            for w_nm, o_row, b_val in wrote_list:
                if w_nm == run_nm:
                    d = r_sub(o_row, place_row)
                    if not d[1] and d[0] == 0:
                        return b_val
            return None

        def _range_shown(pl, penv, cur_st):
            if pl.get("wrote") is None:
                return
            run_nm, lo_e, f_name, arg_es, from_start = pl["wrote"]
            if run_nm not in cur_st["out_len"]:
                raise Refuse(f"place wrote names unknown out buffer `{run_nm}`")
            lo_val = self.as_num(self.eval_sexpr(lo_e, penv, cur_st, stream), penv, cur_st, stream)
            vs = tuple(self.eval_sexpr(ae, penv, cur_st, stream) for ae in arg_es)
            eo = _each_of(f_name, len(vs))
            if eo is None:
                raise Refuse(f"place wrote `{f_name}` is not an `(each ... 0 hi)` list definition")
            params, x_var, body, hi = eo
            if cur_st["out_len"][run_nm] < hi:
                raise Refuse("place wrote exceeds output buffer length")
            self.entail(cur_st["facts"], lo_val, stream)
            rg = cur_st["range"]
            if rg is not None and rg[0] == run_nm and rg[2] == f_name and rg[3] == vs and rg[4] == from_start:
                base = rg[1]
            else:
                base = r_const(0) if from_start else r_const(hi)
            diff = r_sub(lo_val, base) if from_start else r_sub(base, lo_val)
            if diff[1] or diff[0] < 0 or diff[0] > 64:
                raise Refuse("place wrote step is not a constant in 0..64")
            count = diff[0]
            start = base if from_start else lo_val
            for k_step in range(count):
                here = r_add(start, r_const(k_step))
                b_val = _wrote_at(cur_st["wrote"], run_nm, here)
                if b_val is None:
                    raise Refuse(f"place wrote: byte at offset +{k_step} not known written")
                benv = dict(zip(params, vs))
                benv[x_var] = here
                ev_b = self.eval_sexpr(body, benv, cur_st, stream)
                if not self.is_row(ev_b):
                    raise Refuse("place wrote: list element is not a number")
                self.entail(cur_st["facts"], r_sub(ev_b, b_val), stream)
                self.entail(cur_st["facts"], r_sub(b_val, ev_b), stream)

        def _suppose_range(pl, penv, cur_st):
            if pl.get("wrote") is None:
                return
            run_nm, lo_e, f_name, arg_es, from_start = pl["wrote"]
            if run_nm not in cur_st["out_len"]:
                raise Refuse(f"place wrote names unknown out buffer `{run_nm}`")
            lo_val = self.as_num(self.eval_sexpr(lo_e, penv, cur_st, stream), penv, cur_st, stream)
            vs = tuple(self.eval_sexpr(ae, penv, cur_st, stream) for ae in arg_es)
            cur_st["range"] = (run_nm, lo_val, f_name, vs, from_start)

        def run_path(pc, st, origin_place=None, origin_dec=None, visited_places=frozenset(),
                     base_st=None, jstack=frozenset(), jdone=None, at_entry=False):
            if jdone is None:
                jdone = {}
            if base_st is None:
                base_st = clone(st)
            while True:
                if at_entry:
                    at_entry = False
                elif pc in places and pc not in visited_places:
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
                            _range_shown(pl, penv, arr_st)
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
                        gj["wrote"] = []
                        gj["range"] = None
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
                            self.assume_fact(fct, penv2, gj, stream)
                        _suppose_range(pl, penv2, gj)
                        run_path(pc, gj, origin_place, origin_dec, visited_places | {pc}, base_st, jstack | {pc}, jdone)
                        jdone[pc] = first_j
                        return
                    penv = dict(env)
                    for nm, rn in pl["names"]:
                        penv[nm] = st["regs"][rn]
                    for fct in pl["facts"]:
                        self.check_fact(fct, penv, st, stream)
                    _range_shown(pl, penv, st)
                    if pl.get("lanes") or pl.get("cells"):
                        _sym_know(st)
                        _lanes_shown(pl, st)
                        _cells_shown(pl, st)
                    if origin_place == pc and pl["decreases"] is not None:
                        new_dec = self.eval_sexpr(pl["decreases"], penv, st, stream)
                        self.entail(st["facts"], r_sub(r_sub(origin_dec, new_dec), r_const(1)), stream)
                    if origin_place == pc:
                        for kr in pl["keep"]:
                            if st["regs"][kr] != entry_regs.get(kr, st["regs"][kr]) and kr in st["place_entry_regs"]:
                                self.entail_eq(st["facts"], st["regs"][kr], st["place_entry_regs"][kr], stream)
                        for o in st.get("place_entry_fq", frozenset()):
                            if o not in st["stack_mem"] or st["stack_mem"][o][1]:
                                raise Refuse(f"at loop place clean frame slot {o} may depend on values kept out of the trace")
                        for vr in st.get("place_entry_vec_intact", frozenset()):
                            if vr not in st["vec_intact"]:
                                raise Refuse(f"at loop place callee-saved vector register v{vr} was modified")
                        return
                    # Enter place once as fresh symbolic state, keeping path facts, `eqs`, and `neq` (matching Core.lean `Sym.general`)
                    pst = clone(st)
                    pst["facts"] = st["facts"].copy()
                    pst["eqs"] = list(st["eqs"])
                    pst["neq"] = list(st["neq"])
                    pst["wrote"] = []
                    pst["wroteW"] = {}
                    pst["intact"] = set()
                    pst["vec"] = {}
                    pst["spill"] = {}
                    pst["range"] = None
                    pst["place_entry_fq"] = frozenset(o for o, (_, mk) in st["stack_mem"].items() if not mk)
                    pst["place_entry_vec_intact"] = frozenset(st["vec_intact"])
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
                        self.assume_fact(fct, penv2, pst, stream)
                    _suppose_range(pl, penv2, pst)
                    _suppose_lanes_cells(pl, pst)
                    dec_val = self.eval_sexpr(pl["decreases"], penv2, pst, stream) if pl["decreases"] is not None else None
                    if dec_val is not None:
                        self.entail(pst["facts"], dec_val, stream)
                    run_path(pc, pst, origin_place=pc, origin_dec=dec_val, visited_places=(visited_places - jstack),
                             base_st=clone(pst), jstack=frozenset(), jdone={}, at_entry=True)
                    return

                if pc not in fn["instrs"]:
                    raise Refuse(f"pc {pc} has no instruction")
                for chk in checks.get(pc, ()):
                    chk_st = clone(st)
                    cenv = dict(env)
                    for nm, rn in chk["names"]:
                        if rn not in chk_st["regs"]:
                            raise Refuse(f"at check {pc} register {rn} is out of range")
                        cenv[nm] = chk_st["regs"][rn]
                    for fct in chk["facts"]:
                        self.check_fact(fct, cenv, chk_st, stream)
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
                        if (len(row.effect) == 1 and lhs[0] == "name"
                                and rhs[0] == "call" and rhs[1] == "select" and len(rhs[2]) == 3
                                and rhs[2][0][0] == "name" and rhs[2][1][0] == "name" and rhs[2][2][0] == "name"):
                            if fn.get("trace_exprs"):
                                raise Refuse("conditional select cannot be used with computed `trace depends on` values")
                            cond_nm = rhs[2][0][1]
                            sel_map = {"zf": ("zf", True), "nzf": ("zf", False),
                                       "cf": ("cf", True), "ncf": ("cf", False),
                                       "hi": ("hi", True), "nhi": ("hi", False)}
                            if cond_nm not in sel_map:
                                raise Refuse(f"unknown select condition `{cond_nm}`")
                            cond_flag, want = sel_map[cond_nm]
                            def _reg_of_tok(tok):
                                v = bind.get(tok, tok)
                                return v[1:] if isinstance(v, str) and v.startswith(".") else v
                            dst = _reg_of_tok(lhs[1])
                            ra = _reg_of_tok(rhs[2][1][1])
                            rb = _reg_of_tok(rhs[2][2][1])
                            if cond_flag == "hi":
                                mk_flag = st["flag_marks"]["zf"] or st["flag_marks"]["cf"]
                                zf_rel, cf_rel = st["flags"]["zf"], st["flags"]["cf"]
                                if (zf_rel is not None and cf_rel is not None
                                        and zf_rel[0] == "eq" and cf_rel[0] == "lt"
                                        and zf_rel[1] == cf_rel[1] and zf_rel[2] == cf_rel[2]):
                                    frel = ("lt", zf_rel[2], zf_rel[1])
                                else:
                                    raise Refuse("select on `hi`/`nhi` without matching cmp flags")
                            else:
                                mk_flag = st["flag_marks"][cond_flag]
                                frel = st["flags"][cond_flag]
                                if frel is None:
                                    raise Refuse(f"select on unset flag `{cond_flag}`")
                            mk_out = bool(mk_flag or st["marks"][ra] or st["marks"][rb])
                            op_f, a_row, b_row = frel
                            live_sel = []
                            def _assume_sel(f_is_true, w_facts):
                                chosen_val = st["regs"][ra] if (f_is_true == want) else st["regs"][rb]
                                if any((not r[1]) and r[0] < 0 for r in w_facts):
                                    return
                                if all(not r[1] for r in w_facts):
                                    st_w = clone(st)
                                    st_w["regs"][dst] = chosen_val
                                    st_w["marks"][dst] = mk_out
                                    live_sel.append(st_w)
                                    return
                                tag_w, _ = stream.pop_tag()
                                if tag_w == "live":
                                    st_w = clone(st)
                                    st_w["facts"].extend(w_facts)
                                    st_w["regs"][dst] = chosen_val
                                    st_w["marks"][dst] = mk_out
                                    live_sel.append(st_w)
                                elif tag_w == "dead":
                                    self.refute_dead(st["facts"] + w_facts, stream)
                                else:
                                    raise Refuse(f"expected `live`/`dead`, got `{tag_w}`")
                            if op_f == "eq":
                                diff_ab = r_sub(a_row, b_row)
                                diff_ba = r_sub(b_row, a_row)
                                if diff_ab not in st["neq"] and diff_ba not in st["neq"]:
                                    _assume_sel(True, [diff_ab, diff_ba])
                                if not diff_ab[1]:
                                    if diff_ab[0] != 0:
                                        st_w = clone(st)
                                        st_w["regs"][dst] = st["regs"][ra] if (False == want) else st["regs"][rb]
                                        st_w["marks"][dst] = mk_out
                                        live_sel.append(st_w)
                                else:
                                    nxt_item = stream.items[stream.pos] if stream.pos < len(stream.items) else None
                                    if nxt_item is not None and nxt_item[0] == "t" and nxt_item[1] == "neq":
                                        stream.pos += 1
                                        st_w = clone(st)
                                        st_w["neq"].append(diff_ab)
                                        st_w["regs"][dst] = st["regs"][ra] if (False == want) else st["regs"][rb]
                                        st_w["marks"][dst] = mk_out
                                        live_sel.append(st_w)
                                    else:
                                        _assume_sel(False, [r_sub(diff_ab, r_const(1))])
                                        _assume_sel(False, [r_sub(diff_ba, r_const(1))])
                            elif op_f == "lt":
                                _assume_sel(True, [r_sub(r_sub(b_row, a_row), r_const(1))])
                                _assume_sel(False, [r_sub(a_row, b_row)])
                            else:
                                raise Refuse(f"unknown flag relation {frel}")
                            for st_w in live_sel:
                                next_v = visited_places if (nxt != origin_place and nxt not in jstack) else (visited_places - {nxt})
                                run_path(nxt, st_w, origin_place, origin_dec, next_v, base_st, jstack, jdone)
                            return
                        # Vector / 512-bit / mask / above128 statements
                        if lhs[0] == "name" and lhs[1] == "above128":
                            if rhs != ("name", "unknown"):
                                raise Refuse("`above128` assignment not handled")
                            st["vec"] = {r: (v[:4] if r < 16 else v) for r, v in st["vec"].items()}
                            st["vec_intact"] = {r for r in st["vec_intact"] if r >= 16}
                            continue
                        if lhs[0] == "name" and lhs[1] in tab_mod.VECTORS:
                            vr = _vec_of(bind, lhs[1])
                            if vr is None:
                                raise Refuse("vector register assignment out of range")
                            lanes = _eval_vec128(rhs, bind, st)
                            if len(lanes) != 4:
                                raise Refuse("128-bit vector assignment did not yield 4 words")
                            st["vec"][vr] = tuple(lanes)
                            st["vec_intact"].discard(vr)
                            continue
                        if lhs[0] == "name" and (lhs[1] in tab_mod.WIDE or lhs[1] in tab_mod.MASKS):
                            vr = _vec_of_512(bind, lhs[1])
                            if vr is None:
                                raise Refuse("512-bit/mask register assignment out of range")
                            lanes = _eval_vec512(rhs, bind, st)
                            if len(lanes) != 16:
                                raise Refuse("512-bit vector assignment did not yield 16 lanes")
                            st["vec"][vr] = tuple(lanes)
                            st["vec_intact"].discard(vr)
                            continue
                        if lhs[0] == "call" and lhs[1] == "mem128":
                            lanes = _sym_vec4(bind, st, rhs)
                            if lanes is None:
                                raise Refuse("128-bit store from unknown vector register")
                            addr = _sym_word_addr(bind, st, lhs[2])
                            _sym_store_words(st, addr, lanes, 4)
                            continue
                        if lhs[0] == "call" and lhs[1] == "mem512":
                            lanes = _sym_vec16(bind, st, rhs)
                            if lanes is None:
                                raise Refuse("512-bit store from unknown vector register")
                            addr = _sym_word_addr(bind, st, lhs[2])
                            _sym_store_words(st, addr, lanes, 16)
                            continue
                        if lhs[0] == "call" and lhs[1] == "mem512a":
                            lanes = _sym_vec16(bind, st, rhs)
                            if lanes is None:
                                raise Refuse("aligned 512-bit store from unknown vector register")
                            _sym_spill_store(bind, st, lhs[2], lanes)
                            continue
                        low_is_clean = False
                        if rhs[0] == "call" and rhs[1] == "setlow8" and len(rhs[2]) == 2:
                            _, mb_low = eval_table_expr(rhs[2][1], bind, st)
                            low_is_clean = not mb_low
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
                                if low_is_clean:
                                    st["low_clean"].add(rname)
                                else:
                                    st["low_clean"].discard(rname)
                        elif lhs[0] == "call" and lhs[1] == "mem32":
                            base, mb = eval_table_expr(lhs[2][0], bind, st)
                            disp, md = eval_table_expr(lhs[2][1], bind, st)
                            if mb or md:
                                raise Refuse("mem32 store address depends on values kept out of the trace")
                            _sym_store4(st, r_add(r_signed(base), r_signed(disp)), val)
                        elif lhs[0] == "call" and lhs[1] == "mem64":
                            base, mb = eval_table_expr(lhs[2][0], bind, st)
                            disp, md = eval_table_expr(lhs[2][1], bind, st)
                            if mb or md:
                                raise Refuse("mem64 store address depends on values kept out of the trace")
                            addr = r_add(r_signed(base), r_signed(disp))
                            off_row = r_sub(addr, entry_regs[sp_reg])
                            if not off_row[1]:
                                o = off_row[0]
                                st["spill"] = {}
                                st["stack_mem"][o] = (val, mk)
                                st["frameW"] = {c: v for c, v in st["frameW"].items() if c + 4 <= o or o + 8 <= c}
                                st["min_sp"] = min(st["min_sp"], o)
                            else:
                                mo = _find_in_runs(addr, outs_list)
                                if mo is None:
                                    raise Refuse("mem64 store address does not fall in stack frame or output buffer")
                                _sym_store8_out(st, mo[0], mo[2], mo[1], val)
                        elif lhs[0] == "call" and lhs[1] == "mem8":
                            base, mb = eval_table_expr(lhs[2][0], bind, st)
                            disp, md = eval_table_expr(lhs[2][1], bind, st)
                            if mb or md:
                                raise Refuse("mem8 store address depends on values kept out of the trace")
                            addr = r_add(base, disp)
                            def _counted_from_out(obase):
                                vs = [i for i, cf in enumerate(obase[1]) if cf != 0]
                                return (obase[0] == 0 and len(vs) == 1 and obase[1][vs[0]] == 1
                                        and vs[0] < len(addr[1]) and addr[1][vs[0]] == 1)
                            matched_out = None
                            for onm, obase in st["out_base"].items():
                                if _counted_from_out(obase):
                                    matched_out = (onm, r_sub(addr, obase))
                                    break
                            if matched_out is None:
                                if addr == st["regs"][sp_reg]:
                                    # `symTouchFrame`: stack probe write to `[rsp]` (e.g. `mov byte ptr [rsp], 0`)
                                    fo = r_sub(addr, entry_regs[sp_reg])
                                    for g in _frame_span_goals(st, addr, 1):
                                        self.entail(st["facts"], g, stream)
                                    for so in sorted(st["stack_mem"].keys()):
                                        self.entail(st["facts"], r_sub(r_const(so - 1), fo), stream)
                                    st["spill"] = {}
                                    st["frameW"] = {}
                                    st["range"] = None
                                    continue
                                raise Refuse("mem8 store address does not fall in any output buffer")
                            onm, off = matched_out
                            self.entail(st["facts"], off, stream)
                            self.entail(st["facts"], r_sub(r_const(st["out_len"][onm] - 1), off), stream)
                            self.entail(st["facts"], val, stream)
                            self.entail(st["facts"], r_sub(r_const(255), val), stream)
                            kept_w = []
                            for w_nm, o_prev, v_prev in st["wrote"]:
                                if w_nm != onm:
                                    kept_w.append((w_nm, o_prev, v_prev))
                                else:
                                    d = r_sub(o_prev, off)
                                    if d[1]:
                                        raise Refuse("mem8 store at offset not known apart from an earlier write")
                                    if d[0] != 0:
                                        kept_w.append((w_nm, o_prev, v_prev))
                            rg = st["range"]
                            if rg is not None and rg[0] == onm:
                                if rg[4]:
                                    self.entail(st["facts"], r_sub(off, rg[1]), stream)
                                else:
                                    self.entail(st["facts"], r_sub(r_sub(rg[1], off), r_const(1)), stream)
                            st["wrote"] = [(onm, off, val)] + kept_w
                        else:
                            raise Refuse(f"unsupported lhs {lhs} in verify2")
                    elif kind == "jump":
                        tgt_expr, cond = stmt[1], stmt[2]
                        tval = bind[tgt_expr[1]] if tgt_expr[0] == "name" else tgt_expr[1]
                        if cond is None and isinstance(tval, str) and (tval in self.proven or (tval == fn["name"] and fn["decreases"] is not None)):
                            # Tail call (`jmp callee` on x86-64 / `b callee` on AArch64)
                            c = fn if tval == fn["name"] else self.proven[tval]
                            if (c["machine"] == "arm64") != is_arm:
                                raise Refuse(f"tail callee `{tval}` targets a different machine")
                            c_arg_regs = c["argregs"] if c["argregs"] is not None else (ARM_ARGS if is_arm else X86_ARGS)
                            c_keeps = set(c["keeps"]) if c["keeps"] is not None else (ARM_CALLEE_SAVED if is_arm else X86_CALLEE_SAVED)
                            c_ret_reg = c["retreg"] if c["retreg"] is not None else ("x0" if is_arm else "rax")
                            if c_ret_reg != ret_reg:
                                raise Refuse(f"tail callee `{tval}` returns in `{c_ret_reg}`, expected `{ret_reg}`")
                            self.entail_eq(st["facts"], st["regs"][sp_reg], entry_regs[sp_reg], stream)
                            if st["marks"][sp_reg]:
                                raise Refuse("at tail call stack pointer may depend on values kept out of the trace")
                            if is_arm:
                                self.entail_eq(st["facts"], st["regs"]["x30"], entry_regs["x30"], stream)
                                if st["marks"]["x30"]:
                                    raise Refuse("at tail call link register x30 may depend on values kept out of the trace")
                            for r in callee_saved:
                                if r not in c_keeps:
                                    raise Refuse(f"tail callee `{tval}` does not preserve `{r}`")
                                self.entail_eq(st["facts"], st["regs"][r], entry_regs[r], stream)
                            c_kv = c.get("keeps_vec")
                            c_kv_set = {vec_reg_index(v) for v in c_kv if vec_reg_index(v) is not None} if c_kv is not None else (set(range(8, 16)) if is_arm else set())
                            for vr in callee_saved_vec:
                                if vr not in st["vec_intact"] or vr not in c_kv_set:
                                    raise Refuse(f"at tail call callee-saved vector register v{vr} not preserved")
                            if fn["ensuresw"] or c["ensuresw"] or c["ensures"]:
                                if tval == fn["name"]:
                                    raise Refuse("word/byte tail self-recursion not handled")
                                _do_sym_call(c, tval, st, 0, 0, True, stream)
                                for run_nm, part, val_e in fn["ensuresw"]:
                                    _check_ensuresw(st, run_nm, part, val_e)
                                return
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
                                        raise Refuse(f"tail callee `{tval}` bytes arg `{anm}` does not match a caller buffer")
                                    cenv[anm] = ("buf", found_buf)
                                    if anm not in c["hidden"] and not st["buf_clean"][found_buf]:
                                        raise Refuse(f"tail callee `{tval}` exposes buffer `{found_buf}` kept out of caller trace")
                                else:
                                    cenv[anm] = st["regs"][areg]
                                    if anm not in c["hidden"] and st["marks"][areg]:
                                        raise Refuse(f"tail callee `{tval}` trace arg `{anm}` may depend on values kept out of trace")
                            _check_call_stack(c, 0, 0, cenv, st["facts"], stream)
                            for anm, bnd in c["atleast"]:
                                if anm in cenv:
                                    self.entail(st["facts"], r_sub(cenv[anm], r_const(bnd)), stream)
                            for k, terms in c["linpre"]:
                                self.entail(st["facts"], self.linpre_row(k, terms, cenv), stream)
                            _check_call_align_ld(c, c_arg_regs, st)
                            if tval == fn["name"]:
                                dnm = fn["decreases"]
                                self.entail(st["facts"], r_sub(r_sub(env[dnm], cenv[dnm]), r_const(1)), stream)
                            for anm, bnd in c["below"]:
                                if anm in cenv:
                                    self.entail(st["facts"], r_sub(r_const(bnd - 1), cenv[anm]), stream)
                            for req in c["requires"]:
                                self.check_fact(req, cenv, st, stream)
                            if fn["returns"] is not None:
                                if c["returns"] is None:
                                    raise Refuse(f"tail callee `{tval}` has no returns clause")
                                got_val = self.eval_sexpr(c["returns"], cenv, st, stream)
                                rv = r_var(st["nvars"])
                                st["nvars"] += 1
                                if isinstance(got_val, tuple) and len(got_val) == 3 and got_val[0] == "call":
                                    st["eqs"].insert(0, (got_val, rv))
                                else:
                                    st["facts"].append(r_sub(rv, got_val))
                                    st["facts"].append(r_sub(got_val, rv))
                                want = self.eval_sexpr(fn["returns"], env, st, stream)
                                self.expand_eq(rv, want, env, st, stream)
                            return
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
                        if callee_nm == fn["name"] and fn["decreases"] is not None:
                            c = fn
                        elif callee_nm in self.proven:
                            c = self.proven[callee_nm]
                        else:
                            raise Refuse(f"callee `{callee_nm}` has not been verified")
                        c_is_arm = c["machine"] == "arm64"
                        if c_is_arm != is_arm:
                            raise Refuse(f"callee `{callee_nm}` targets a different machine")
                        sp_off = r_sub(st["regs"][sp_reg], entry_regs[sp_reg])
                        if sp_off[1]:
                            raise Refuse("non-constant stack pointer at call")
                        if is_arm and (sp_off[0] % 16 != 0):
                            raise Refuse("stack pointer is not 16-byte aligned at AArch64 call")
                        _do_sym_call(c, callee_nm, st, sp_off[0], 0 if is_arm else 8, False, stream)
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
                        for vr in callee_saved_vec:
                            if vr not in st["vec_intact"]:
                                raise Refuse(f"at return callee-saved vector register v{vr} was modified")

                        def _check_ret_body(st_r):
                            for run_nm, part, val_e in fn["ensuresw"]:
                                _check_ensuresw(st_r, run_nm, part, val_e)
                            for run_nm, lo_e, hi_e, val_e in fn["ensures"]:
                                if run_nm not in st_r["out_len"]:
                                    raise Refuse(f"ensures names unknown out buffer `{run_nm}`")
                                rg = st_r["range"]
                                if (rg is not None and isinstance(val_e, tuple) and len(val_e) >= 2
                                        and val_e[0] == "call" and val_e[1] == rg[2]):
                                    vs = tuple(self.eval_sexpr(ae, env, st_r, stream) for ae in val_e[2:])
                                    if vs != rg[3]:
                                        raise Refuse("ensures range arguments do not match loop place")
                                    eo = _each_of(rg[2], len(vs))
                                    if eo is None:
                                        raise Refuse("ensures range is not an `(each ... 0 hi)` list")
                                    _, _, _, hi_n = eo
                                    lo_v = self.as_num(self.eval_sexpr(lo_e, env, st_r, stream), env, st_r, stream)
                                    top_v = self.as_num(self.eval_sexpr(hi_e, env, st_r, stream), env, st_r, stream)
                                    self.entail(st_r["facts"], lo_v, stream)
                                    self.entail(st_r["facts"], r_scale(-1, lo_v), stream)
                                    self.entail(st_r["facts"], r_sub(top_v, r_const(hi_n)), stream)
                                    self.entail(st_r["facts"], r_sub(r_const(hi_n), top_v), stream)
                                    self.entail(st_r["facts"], r_sub(rg[1], r_const(hi_n)) if rg[4] else r_scale(-1, rg[1]), stream)
                                    if run_nm != rg[0]:
                                        raise Refuse("ensures names a different out buffer than loop place")
                                else:
                                    raise Refuse(f"unsupported non-range ensures in verify2: {val_e}")
                            if fn["returns"] is not None:
                                want = self.eval_sexpr(fn["returns"], env, st_r, stream)
                                self.expand_eq(st_r["regs"][ret_reg], want, env, st_r, stream)

                        def _check_ret_split(st_r, fuel=8):
                            if (fuel > 0 and stream.pos < len(stream.items)
                                    and stream.items[stream.pos][0] == "t"
                                    and stream.items[stream.pos][1] == "split"):
                                stream.pos += 1
                                if stream.pos >= len(stream.items) or stream.items[stream.pos][0] != "k":
                                    raise Refuse("split expects a row (`k ...`)")
                                row = stream.items[stream.pos][1]
                                stream.pos += 1
                                if len(row[1]) > st_r["nvars"]:
                                    raise Refuse("split row references an unknown variable")
                                st_pos = clone(st_r)
                                st_pos["facts"].append(row)
                                _check_ret_split(st_pos, fuel - 1)
                                st_neg = clone(st_r)
                                st_neg["facts"].append(r_sub(r_const(-1), row))
                                _check_ret_split(st_neg, fuel - 1)
                            else:
                                _check_ret_body(st_r)

                        _check_ret_split(st)
                        return
                    else:
                        raise Refuse(f"table stmt `{kind}` not handled in verify2")
                # Mirror Core.lean `settle` when `rsp` has a non-constant offset from entry `rsp` (e.g. `and rsp, -64`)
                sp_off_now = r_sub(st["regs"][sp_reg], entry_regs[sp_reg])
                if sp_off_now[1]:
                    cur_sig = (st["regs"][sp_reg], tuple(sorted(st["stack_mem"].keys())), tuple(st["spill"].keys()))
                    if st.get("stack_at") != cur_sig:
                        goals = [
                            r_add(sp_off_now, r_const(fn["stack"])),
                            r_scale(-1, sp_off_now),
                        ]
                        for so in sorted(st["stack_mem"].keys()):
                            goals.append(r_sub(r_const(so), sp_off_now))
                        for sp_k in st["spill"]:
                            goals.append(r_sub(sp_k, sp_off_now))
                        missing = [g for g in goals if not r_plain(st["facts"], g)]
                        for g in missing:
                            self.entail(st["facts"], g, stream)
                        st["facts"].extend(missing)
                        st["frameW"] = {}
                        st["stack_at"] = cur_sig
                else:
                    st["stack_at"] = None
                pc = next_pc

        run_path(0, state, at_entry=True)
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
