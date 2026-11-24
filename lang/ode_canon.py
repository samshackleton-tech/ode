"""Canonicalization, glossary splitting, and 52-char base-32 BLAKE3 IDs for Ode contracts (.ocl).

A canonical Ode contract has NO name, NO comments, NO unused helper definitions, and NO
author-chosen identifiers: every reachable constant, layout, sequence, definition, argument,
and local variable is numbered in deterministic first-mention order from the contract root.

The contract's sole identity is the 52-character lowercase RFC 4648 base-32 encoding
(without padding) of the 256-bit BLAKE3 hash of its canonical UTF-8 bytes (`[a-z2-7]{52}`). Author-chosen human
names are split out into a separate glossary dict so they never enter the contract hash.
"""

import base64
import os
import re
import struct
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
KCHECK = os.path.join(ROOT, "kcheck")
if KCHECK not in sys.path:
    sys.path.insert(0, KCHECK)

import ode

B32_RE = re.compile(r"^[a-z2-7]{52}$")

# Built-in functions and constants of OdeSpecL / Ode Contract Language (never alpha-renamed).
BUILTINS = frozenset({
    "len", "word", "words", "bytes_of", "counter", "lo", "hi", "bits",
    "failed", "value", "min", "max", "abs", "byte", "bytes",
    "true", "false",
})

# Built-in argument kind keywords (never alpha-renamed as layout names).
BUILTIN_KINDS = frozenset({"number", "bytes", "byte", "cv", "block", "u32", "u64", "table", "of"})

# Precedence table matching kcheck/ode.py LEVELS (lowest to highest).
OP_PREC = {}
for _lvl, _ops in enumerate(ode.LEVELS):
    for _op in _ops:
        OP_PREC[_op] = _lvl


# ---------------------------------------------------------------------------
# Self-contained BLAKE3-256 (standard mode, exact spec; cross-checked vs b3sum)
# ---------------------------------------------------------------------------

_IV = (
    0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
    0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
)
_MSG_PERM = (2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8)
_CHUNK_START = 1
_CHUNK_END = 2
_PARENT = 4
_ROOT = 8
_M32 = 0xFFFFFFFF


def _rotr32(x, n):
    return ((x >> n) | ((x << (32 - n)) & _M32)) & _M32


def _g(s, a, b, c, d, mx, my):
    s[a] = (s[a] + s[b] + mx) & _M32
    s[d] = _rotr32(s[d] ^ s[a], 16)
    s[c] = (s[c] + s[d]) & _M32
    s[b] = _rotr32(s[b] ^ s[c], 12)
    s[a] = (s[a] + s[b] + my) & _M32
    s[d] = _rotr32(s[d] ^ s[a], 8)
    s[c] = (s[c] + s[d]) & _M32
    s[b] = _rotr32(s[b] ^ s[c], 7)


def _compress(cv, block, counter, block_len, flags):
    m = list(struct.unpack("<16I", block))
    s = [
        cv[0], cv[1], cv[2], cv[3], cv[4], cv[5], cv[6], cv[7],
        _IV[0], _IV[1], _IV[2], _IV[3],
        counter & _M32, (counter >> 32) & _M32, block_len, flags,
    ]
    for r in range(7):
        _g(s, 0, 4, 8, 12, m[0], m[1])
        _g(s, 1, 5, 9, 13, m[2], m[3])
        _g(s, 2, 6, 10, 14, m[4], m[5])
        _g(s, 3, 7, 11, 15, m[6], m[7])
        _g(s, 0, 5, 10, 15, m[8], m[9])
        _g(s, 1, 6, 11, 12, m[10], m[11])
        _g(s, 2, 7, 8, 13, m[12], m[13])
        _g(s, 3, 4, 9, 14, m[14], m[15])
        if r < 6:
            m = [m[i] for i in _MSG_PERM]
    return [s[i] ^ s[i + 8] for i in range(8)]


def _chunk_output(data, chunk_counter):
    cv = list(_IV)
    if not data:
        return (cv, b"\x00" * 64, chunk_counter, 0, _CHUNK_START | _CHUNK_END)
    n_blocks = (len(data) + 63) // 64
    for i in range(n_blocks):
        blk = data[64 * i : 64 * (i + 1)]
        blen = len(blk)
        if blen < 64:
            blk = blk + b"\x00" * (64 - blen)
        fl = 0
        if i == 0:
            fl |= _CHUNK_START
        if i == n_blocks - 1:
            fl |= _CHUNK_END
            return (cv, blk, chunk_counter, blen, fl)
        cv = _compress(cv, blk, chunk_counter, blen, fl)
    raise AssertionError("unreachable")


def _parent_output(left_cv, right_cv):
    blk = struct.pack("<8I8I", *left_cv, *right_cv)
    return (list(_IV), blk, 0, 64, _PARENT)


def blake3_256(data):
    """Return the exact 32-byte BLAKE3-256 digest of `data` (bytes)."""
    if not isinstance(data, (bytes, bytearray, memoryview)):
        raise TypeError("blake3_256 requires bytes")
    data = bytes(data)
    if len(data) <= 1024:
        cv, blk, ctr, blen, fl = _chunk_output(data, 0)
        out = _compress(cv, blk, ctr, blen, fl | _ROOT)
        return struct.pack("<8I", *out)
    stack = []
    pos = 0
    chunk_idx = 0
    while len(data) - pos > 1024:
        cv, blk, ctr, blen, fl = _chunk_output(data[pos : pos + 1024], chunk_idx)
        new_cv = _compress(cv, blk, ctr, blen, fl)
        chunk_idx += 1
        total = chunk_idx
        while (total & 1) == 0:
            left = stack.pop()
            p_cv, p_blk, p_ctr, p_blen, p_fl = _parent_output(left, new_cv)
            new_cv = _compress(p_cv, p_blk, p_ctr, p_blen, p_fl)
            total >>= 1
        stack.append(new_cv)
        pos += 1024
    out_tuple = _chunk_output(data[pos:], chunk_idx)
    while stack:
        cv, blk, ctr, blen, fl = out_tuple
        right_cv = _compress(cv, blk, ctr, blen, fl)
        left_cv = stack.pop()
        out_tuple = _parent_output(left_cv, right_cv)
    cv, blk, ctr, blen, fl = out_tuple
    out = _compress(cv, blk, ctr, blen, fl | _ROOT)
    return struct.pack("<8I", *out)


def blake3_b32(data):
    """Return the 52-char lowercase RFC 4648 base-32 BLAKE3-256 digest (without padding)."""
    s = base64.b32encode(blake3_256(data)).decode("ascii").rstrip("=").lower()
    assert len(s) == 52 and B32_RE.fullmatch(s)
    return s


def ode_symbol(contract_id):
    """Canonical linker symbol derived solely from a 52-char base-32 contract ID."""
    if not B32_RE.fullmatch(contract_id):
        raise ValueError(f"contract ID must be a full 52-char lowercase base-32 BLAKE3 digest, got {contract_id!r}")
    return f"ode_{contract_id}"


# ---------------------------------------------------------------------------
# Parsing nameless `contract (...) { ... }` as well as named `contract NAME(...)`
# ---------------------------------------------------------------------------

_NAMELESS_CONTRACT_RE = re.compile(r"(^|\n)(\s*)contract\s*\(")
_SENTINEL_NAME = "__ode_anon_contract__"


def bind_symbol(ocl_text, symbol):
    """Bind a nameless canonical `.ocl` contract to a concrete symbol for `kcheck/ode.py`."""
    m = _NAMELESS_CONTRACT_RE.search(ocl_text)
    if not m:
        raise ValueError("expected a nameless canonical `contract (...)` block")
    return ocl_text[:m.start()] + f"{m.group(1)}{m.group(2)}contract {symbol}(" + ocl_text[m.end():]


def _parse_any(spec_text):
    """Parse either a nameless `.ocl` file or a named `.spec` file via `kcheck/ode.py`."""
    if _NAMELESS_CONTRACT_RE.search(spec_text):
        wrapped = _NAMELESS_CONTRACT_RE.sub(rf"\1\2contract {_SENTINEL_NAME}(", spec_text, count=1)
        return ode.Spec(wrapped), True
    return ode.Spec(spec_text), False


# ---------------------------------------------------------------------------
# AST formatter + deterministic first-mention alpha-renaming canonicalizer
# ---------------------------------------------------------------------------

def _fmt_expr(e, parent_prec=-1, right_child=False):
    tag = e[0]
    if tag == "num":
        return str(e[1])
    if tag == "name":
        return e[1]
    if tag == "not":
        inner = _fmt_expr(e[1], len(ode.LEVELS))
        return f"!{inner}"
    if tag == "bin":
        _, op, a, b = e
        prec = OP_PREC[op]
        sa = _fmt_expr(a, prec, right_child=False)
        sb = _fmt_expr(b, prec, right_child=True)
        out = f"{sa} {op} {sb}"
        if prec < parent_prec or (right_child and prec == parent_prec):
            return f"({out})"
        return out
    if tag == "ifx":
        _, cond, a, b = e
        out = f"if {_fmt_expr(cond)} then {_fmt_expr(a)} else {_fmt_expr(b)}"
        return f"({out})" if parent_prec >= 0 else out
    if tag == "index":
        return f"{_fmt_expr(e[1], len(ode.LEVELS))}[{_fmt_expr(e[2])}]"
    if tag == "slice":
        return f"{_fmt_expr(e[1], len(ode.LEVELS))}[{_fmt_expr(e[2])} .. {_fmt_expr(e[3])}]"
    if tag == "field":
        return f"{_fmt_expr(e[1], len(ode.LEVELS))}.{e[2]}"
    if tag == "with":
        places = ", ".join(f"{_fmt_expr(i, 1)}: {_fmt_expr(v)}" for i, v in e[2])
        return f"({_fmt_expr(e[1], len(ode.LEVELS))} with [{places}])"
    if tag == "list":
        return "[" + ", ".join(_fmt_expr(x) for x in e[1]) + "]"
    if tag == "each":
        _, body, var, a, b = e
        return f"[{_fmt_expr(body)} for {var} in {_fmt_expr(a)} .. {_fmt_expr(b)}]"
    if tag == "the":
        _, which, var, among, cond = e
        if among[0] == "range":
            return f"(the {which} number {var} in {_fmt_expr(among[1], 1)} .. {_fmt_expr(among[2], 1)} with {_fmt_expr(cond)})"
        return f"(the {which} power of two {var} with {_fmt_expr(cond)})"
    if tag == "record":
        return "{" + ", ".join(f"{k}: {_fmt_expr(v)}" for k, v in e[1]) + "}"
    if tag == "call":
        return f"{e[1]}(" + ", ".join(_fmt_expr(a) for a in e[2]) + ")"
    raise ValueError(f"unsupported AST node in canonicalizer: {tag!r}")


def _fmt_body_expr(e, indent=4):
    """Deterministically format a top-level `def` body expression (breaking `if/else` chains for readability)."""
    if e[0] != "ifx":
        return " " * indent + _fmt_expr(e)
    pad = " " * indent
    lines = []
    cur = e
    first = True
    while cur[0] == "ifx":
        _, cond, thn, els = cur
        kw = "if" if first else "else if"
        first = False
        if thn[0] == "ifx":
            lines.append(f"{pad}{kw} {_fmt_expr(cond)} then")
            lines.append(_fmt_body_expr(thn, indent + 4))
        else:
            lines.append(f"{pad}{kw} {_fmt_expr(cond)} then {_fmt_expr(thn)}")
        cur = els
    lines.append(f"{pad}else {_fmt_expr(cur)}")
    return "\n".join(lines)


class _Canon:
    def __init__(self, sp):
        self.sp = sp
        self.const_map = {}     # orig -> C0, C1, ...
        self.layout_map = {}    # orig -> L0, L1, ...
        self.field_map = {}     # (layout_orig, field_orig) -> k0, k1, ...
        self.rec_field_map = {} # record literal field_orig -> r0, r1, ...
        self.seq_map = {}       # orig -> S0, S1, ...
        self.mach_map = {}      # orig -> M0, M1, ...
        self.fn_map = {}        # orig -> f0, f1, ...
        self.glossary = {}      # canonical_name -> original_name
        self.order = []         # emitted top-level declarations in deterministic order
        self._done_top = set()  # (kind, orig_name) already emitted/visiting

    def _alloc(self, mapping, prefix, orig):
        if orig in mapping:
            return mapping[orig]
        cname = f"{prefix}{len(mapping)}"
        mapping[orig] = cname
        self.glossary[cname] = orig
        return cname

    def use_const(self, orig):
        cname = self._alloc(self.const_map, "C", orig)
        key = ("const", orig)
        if key not in self._done_top:
            self._done_top.add(key)
            val = self.sp.consts[orig]
            if isinstance(val, tuple):
                e = self.rw_expr(val, {})
            elif isinstance(val, list):
                e = ("list", [("num", int(x)) for x in val])
            else:
                e = ("num", int(val))
            self.order.append(("const", cname, e))
        return cname

    def use_layout(self, orig):
        cname = self._alloc(self.layout_map, "L", orig)
        key = ("layout", orig)
        if key not in self._done_top:
            self._done_top.add(key)
            lay = self.sp.layouts[orig]
            fmap = {}
            new_fields = []
            for idx, (fname, fmeta) in enumerate(lay["fields"].items()):
                cf = f"k{idx}"
                fmap[fname] = cf
                self.field_map[(orig, fname)] = cf
                self.glossary[f"{cname}.{cf}"] = fname
                new_fields.append((cf, dict(fmeta)))
            self.order.append(("layout", cname, lay["size"], new_fields))
        return cname

    def use_seq(self, orig):
        cname = self._alloc(self.seq_map, "S", orig)
        key = ("seq", orig)
        if key not in self._done_top:
            self._done_top.add(key)
            params, h, b, first, nxt = self.sp.seqs[orig]
            env = {}
            cparams = []
            for i, p in enumerate(params):
                cp = f"p{i}"
                env[p] = cp
                cparams.append(cp)
            cfirst = self.rw_expr(first, env)
            env2 = dict(env)
            env2[h] = "h"
            env2[b] = "i"
            cnxt = self.rw_expr(nxt, env2)
            self.order.append(("seq", cname, cparams, cfirst, cnxt))
        return cname

    def use_mach(self, orig):
        cname = self._alloc(self.mach_map, "M", orig)
        key = ("mach", orig)
        if key not in self._done_top:
            self._done_top.add(key)
            m = self.sp.machines[orig]
            env = {}
            cparams = []
            for i, p in enumerate(m["params"]):
                cp = f"p{i}"
                env[p] = cp
                cparams.append(cp)
            cstates = []
            env_s = dict(env)
            for i, st in enumerate(m["states"]):
                cs = f"s{i}"
                env_s[st] = cs
                cstates.append(cs)
            cinits = [self.rw_expr(ex, env) for ex in m["inits"]] if m["inits"] is not None else None
            loop = m["loop"]
            env_t = dict(env_s)
            if loop[0] == "while":
                cloop = ("while", self.rw_expr(loop[1], env_s))
            else:
                _, lvar, la, lb = loop
                env_t[lvar] = "i"
                cloop = ("for", "i", self.rw_expr(la, env_s), self.rw_expr(lb, env_s))
            cturn = [(env_s[st], self.rw_expr(ex, env_t)) for _, st, ex in m["turn"]]
            self.order.append(("mach", cname, cparams, cstates, cinits, cloop, cturn))
        return cname

    def use_fn(self, orig):
        cname = self._alloc(self.fn_map, "f", orig)
        key = ("fn", orig)
        if key not in self._done_top:
            self._done_top.add(key)
            params, body = self.sp.fns[orig]
            env = {}
            cparams = []
            for i, p in enumerate(params):
                cp = f"p{i}"
                env[p] = cp
                cparams.append(cp)
            vcount = [0]

            def fresh():
                n = f"v{vcount[0]}"
                vcount[0] += 1
                return n

            cbody = []
            for stmt in body:
                st = stmt[0]
                if st == "set":
                    _, nm, ex = stmt
                    cex = self.rw_expr(ex, env, vcount)
                    cnm = fresh()
                    env[nm] = cnm
                    cbody.append(("set", cnm, cex))
                elif st == "first":
                    _, nm, ex = stmt
                    cex = self.rw_expr(ex, env, vcount)
                    cnm = env.get(nm) or fresh()
                    env[nm] = cnm
                    cbody.append(("first", cnm, cex))
                elif st == "next":
                    _, nm, ivar, ex = stmt
                    cnm = env[nm]
                    env2 = dict(env)
                    ci = fresh()
                    env2[ivar] = ci
                    cex = self.rw_expr(ex, env2, vcount)
                    cbody.append(("next", cnm, ci, cex))
                elif st == "fails":
                    _, reason, cond = stmt
                    cbody.append(("fails", self.rw_expr(reason, env, vcount), self.rw_expr(cond, env, vcount)))
                elif st == "expr":
                    cbody.append(("expr", self.rw_expr(stmt[1], env, vcount)))
                else:
                    raise ValueError(f"unsupported def statement {st!r}")
            self.order.append(("fn", cname, cparams, cbody))
        return cname

    def rw_expr(self, e, env, vcount=None, arg_layouts=None):
        if vcount is None:
            vcount = [0]
        if arg_layouts is None:
            arg_layouts = {}
        tag = e[0]
        if tag == "num":
            return e
        if tag == "name":
            nm = e[1]
            if nm in env:
                return ("name", env[nm])
            if nm in self.sp.consts:
                return ("name", self.use_const(nm))
            if nm in BUILTINS:
                return e
            raise ValueError(f"unknown identifier `{nm}` while canonicalizing")
        if tag == "not":
            return ("not", self.rw_expr(e[1], env, vcount, arg_layouts))
        if tag == "bin":
            return ("bin", e[1],
                    self.rw_expr(e[2], env, vcount, arg_layouts),
                    self.rw_expr(e[3], env, vcount, arg_layouts))
        if tag == "ifx":
            return ("ifx",
                    self.rw_expr(e[1], env, vcount, arg_layouts),
                    self.rw_expr(e[2], env, vcount, arg_layouts),
                    self.rw_expr(e[3], env, vcount, arg_layouts))
        if tag == "index":
            return ("index",
                    self.rw_expr(e[1], env, vcount, arg_layouts),
                    self.rw_expr(e[2], env, vcount, arg_layouts))
        if tag == "slice":
            return ("slice",
                    self.rw_expr(e[1], env, vcount, arg_layouts),
                    self.rw_expr(e[2], env, vcount, arg_layouts),
                    self.rw_expr(e[3], env, vcount, arg_layouts))
        if tag == "field":
            base_orig = e[1][1] if e[1][0] == "name" else None
            base_rw = self.rw_expr(e[1], env, vcount, arg_layouts)
            fld = e[2]
            if base_orig in arg_layouts:
                lay_orig = arg_layouts[base_orig]
                fld = self.field_map.get((lay_orig, fld), fld)
            else:
                fld = self._alloc(self.rec_field_map, "r", fld)
            return ("field", base_rw, fld)
        if tag == "with":
            base_rw = self.rw_expr(e[1], env, vcount, arg_layouts)
            places = [(self.rw_expr(i, env, vcount, arg_layouts),
                       self.rw_expr(v, env, vcount, arg_layouts)) for i, v in e[2]]
            return ("with", base_rw, places)
        if tag == "list":
            return ("list", [self.rw_expr(x, env, vcount, arg_layouts) for x in e[1]])
        if tag == "each":
            _, body, var, a, b = e
            ca = self.rw_expr(a, env, vcount, arg_layouts)
            cb = self.rw_expr(b, env, vcount, arg_layouts)
            cv = f"v{vcount[0]}"
            vcount[0] += 1
            env2 = dict(env)
            env2[var] = cv
            cbody = self.rw_expr(body, env2, vcount, arg_layouts)
            return ("each", cbody, cv, ca, cb)
        if tag == "the":
            _, which, var, among, cond = e
            if among[0] == "range":
                camong = ("range",
                          self.rw_expr(among[1], env, vcount, arg_layouts),
                          self.rw_expr(among[2], env, vcount, arg_layouts))
            else:
                camong = among
            cv = f"v{vcount[0]}"
            vcount[0] += 1
            env2 = dict(env)
            env2[var] = cv
            ccond = self.rw_expr(cond, env2, vcount, arg_layouts)
            return ("the", which, cv, camong, ccond)
        if tag == "record":
            return (
                "record",
                [(self._alloc(self.rec_field_map, "r", k), self.rw_expr(v, env, vcount, arg_layouts)) for k, v in e[1]],
            )
        if tag == "call":
            fn, args = e[1], e[2]
            if fn in BUILTINS:
                cfn = fn
            elif fn in self.sp.fns:
                cfn = self.use_fn(fn)
            elif fn in self.sp.seqs:
                cfn = self.use_seq(fn)
            elif fn in self.sp.machines:
                cfn = self.use_mach(fn)
            else:
                raise ValueError(f"unknown function `{fn}` while canonicalizing")
            cargs = [self.rw_expr(a, env, vcount, arg_layouts) for a in args]
            return ("call", cfn, cargs)
        raise ValueError(f"unsupported expr node {tag!r}")

    def canonical_contract(self, contract_name):
        c = self.sp.contracts[contract_name]
        if contract_name != _SENTINEL_NAME:
            self.glossary["contract"] = contract_name
        env = {}
        arg_layouts = {}
        # Expand user-defined `kind` aliases first.
        def expand_kind(k):
            toks = k.split()
            if len(toks) == 1 and toks[0] in self.sp.kinds:
                return expand_kind(self.sp.kinds[toks[0]])
            return k

        # Assign canonical argument names a0, a1, ... in parameter-list order.
        for i, (aname, _) in enumerate(c["args"]):
            ca = f"a{i}"
            env[aname] = ca
            self.glossary[ca] = aname

        cargs = []
        for i, (aname, akind) in enumerate(c["args"]):
            ca = env[aname]
            ek = expand_kind(akind)
            toks = ek.split()
            new_toks = []
            for t in toks:
                if t in env:
                    new_toks.append(env[t])
                elif t in self.sp.layouts:
                    arg_layouts[aname] = t
                    new_toks.append(self.use_layout(t))
                elif t in self.sp.consts:
                    new_toks.append(self.use_const(t))
                else:
                    new_toks.append(t)
            cargs.append((ca, " ".join(new_toks)))

        vcount = [0]
        clauses = []

        # 1. requires no_overlap(...) — sorted canonically by argument index.
        if c["no_overlap"]:
            no = sorted((env[x] for x in c["no_overlap"]), key=lambda s: int(s[1:]))
            clauses.append(f"requires no_overlap({', '.join(no)})")

        # 2. requires exprs (canonicalized, sorted deterministically)
        req_lines = []
        for ex in c["asks"]:
            req_lines.append("requires " + _fmt_expr(self.rw_expr(ex, env, vcount, arg_layouts)))
        for g in c["given"]:
            ci = f"v{vcount[0]}"
            vcount[0] += 1
            env2 = dict(env)
            env2[g["index"]] = ci
            cex = self.rw_expr(g["expr"], env2, vcount, arg_layouts)
            ca = self.rw_expr(g["each"][0], env, vcount, arg_layouts)
            cb = self.rw_expr(g["each"][1], env, vcount, arg_layouts)
            req_lines.append(f"requires {env[g['name']]}[{ci}] == {_fmt_expr(cex)} for {ci} in {_fmt_expr(ca)} .. {_fmt_expr(cb)}")
        clauses.extend(sorted(req_lines))

        # 3. writes (sorted)
        for sp_nm in sorted((env[x] for x in c["spoils"]), key=lambda s: int(s[1:])):
            clauses.append(f"writes {sp_nm}")

        # 4. returns
        if c["returns"] is not None:
            r = c["returns"]
            if r[0] == "name" and r[1] not in env and r[1] not in self.sp.consts and r[1] not in BUILTINS:
                # Abstract named return value (`returns r` with `ensures` / `result depends on`)
                env[r[1]] = "r"
                self.glossary["r"] = r[1]
                clauses.append("returns r")
            else:
                clauses.append("returns " + _fmt_expr(self.rw_expr(r, env, vcount, arg_layouts)))

        # 5. ensures (leaves + conditions)
        ens_lines = []
        for lf in c["leaves"]:
            an = env[lf["name"]]
            if lf["index"] is not None:
                ci = f"v{vcount[0]}"
                vcount[0] += 1
                env2 = dict(env)
                env2[lf["index"]] = ci
                cex = self.rw_expr(lf["expr"], env2, vcount, arg_layouts)
                ca = self.rw_expr(lf["each"][0], env, vcount, arg_layouts)
                cb = self.rw_expr(lf["each"][1], env, vcount, arg_layouts)
                s = f"ensures {an}[{ci}] = {_fmt_expr(cex)} for {ci} in {_fmt_expr(ca)} .. {_fmt_expr(cb)}"
            elif lf["part"] is not None:
                pa = self.rw_expr(lf["part"][0], env, vcount, arg_layouts)
                pb = self.rw_expr(lf["part"][1], env, vcount, arg_layouts)
                cex = self.rw_expr(lf["expr"], env, vcount, arg_layouts)
                s = f"ensures {an}[{_fmt_expr(pa)} .. {_fmt_expr(pb)}] = {_fmt_expr(cex)}"
            else:
                cex = self.rw_expr(lf["expr"], env, vcount, arg_layouts)
                s = f"ensures {an} = {_fmt_expr(cex)}"
            if lf["cond"] is not None:
                s += " if " + _fmt_expr(self.rw_expr(lf["cond"], env, vcount, arg_layouts))
            ens_lines.append(s)
        for cond, guard in c["conditions"]:
            s = "ensures " + _fmt_expr(self.rw_expr(cond, env, vcount, arg_layouts))
            if guard is not None:
                s += " if " + _fmt_expr(self.rw_expr(guard, env, vcount, arg_layouts))
            ens_lines.append(s)
        clauses.extend(sorted(ens_lines))

        # 6. trace depends on (sorted)
        trace_items = sorted((env[x] for x in c["trace"]), key=lambda s: int(s[1:]))
        trace_exprs = sorted(_fmt_expr(self.rw_expr(e, env, vcount, arg_layouts)) for e in c["trace_exprs"])
        if trace_items or trace_exprs:
            clauses.append("trace depends on " + ", ".join(trace_items + trace_exprs))

        # 7. result depends on (sorted)
        if c["result_dep"] is not None:
            rdeps = sorted((env[x] for x in c["result_dep"]), key=lambda s: int(s[1:]))
            clauses.append("result depends on " + ", ".join(rdeps))

        # 8. needs (sorted)
        needs_lines = []
        for feat, cond in c["needs"]:
            if cond is None:
                needs_lines.append(f"needs {feat}")
            else:
                needs_lines.append(f"needs {feat} if {_fmt_expr(self.rw_expr(cond, env, vcount, arg_layouts))}")
        clauses.extend(sorted(needs_lines))

        # 9. decreases
        if c["decreases"] is not None:
            clauses.append("decreases " + _fmt_expr(self.rw_expr(c["decreases"], env, vcount, arg_layouts)))

        # 10. stack
        st = c["stack"]
        if isinstance(st, int):
            clauses.append(f"stack {st}")
        elif isinstance(st, tuple) and st[0] == "grows":
            clauses.append("stack " + _fmt_expr(self.rw_expr(st[1], env, vcount, arg_layouts)))
        else:
            raise ValueError(f"unsupported stack form: {st!r}")

        # Format top-level declarations in deterministic order: consts, layouts, seqs, defs, contract.
        blocks = []
        for item in self.order:
            kind = item[0]
            if kind == "const":
                _, cname, e = item
                blocks.append(f"const {cname} = {_fmt_expr(e)}")
            elif kind == "layout":
                _, cname, size, fields = item
                flines = []
                for cf, fm in fields:
                    cnt = f"[{fm['count']}]" if fm["count"] is not None else ""
                    bel = f" below {fm['below']}" if fm["below"] is not None else ""
                    flines.append(f"    {cf}{cnt}: {fm['kind']} at {fm['at']}{bel}")
                blocks.append(f"layout {cname} {size} {{\n" + "\n".join(flines) + "\n}")
            elif kind == "seq":
                _, cname, cparams, cfirst, cnxt = item
                blocks.append(
                    f"sequence {cname}({', '.join(cparams)}) {{\n"
                    f"    h[0] = {_fmt_expr(cfirst)}\n"
                    f"    h[i + 1] = {_fmt_expr(cnxt)}\n"
                    f"}}"
                )
            elif kind == "mach":
                _, cname, cparams, cstates, cinits, cloop, cturn = item
                init_s = f" = {', '.join(_fmt_expr(x) for x in cinits)}" if cinits is not None else ""
                if cloop[0] == "while":
                    lh = f"while {_fmt_expr(cloop[1])}"
                else:
                    lh = f"for {cloop[1]} in {_fmt_expr(cloop[2])} .. {_fmt_expr(cloop[3])}"
                tlines = "\n".join(f"        {st} = {_fmt_expr(ex)}" for st, ex in cturn)
                blocks.append(
                    f"machine {cname}({', '.join(cparams)}) on {', '.join(cstates)}{init_s} {{\n"
                    f"    {lh}\n"
                    f"    turn {{\n{tlines}\n    }}\n"
                    f"}}"
                )
            elif kind == "fn":
                _, cname, cparams, cbody = item
                blines = []
                for stmt in cbody:
                    st_k = stmt[0]
                    if st_k == "set":
                        blines.append(f"    let {stmt[1]} = {_fmt_expr(stmt[2])}")
                    elif st_k == "first":
                        blines.append(f"    let {stmt[1]}[0] = {_fmt_expr(stmt[2])}")
                    elif st_k == "next":
                        blines.append(f"    let {stmt[1]}[{stmt[2]} + 1] = {_fmt_expr(stmt[3])}")
                    elif st_k == "fails":
                        blines.append(f"    fails {_fmt_expr(stmt[1])} if {_fmt_expr(stmt[2])}")
                    elif st_k == "expr":
                        blines.append(_fmt_body_expr(stmt[1], 4))
                blocks.append(f"def {cname}({', '.join(cparams)}) {{\n" + "\n".join(blines) + "\n}")

        # Emit definitions in dependency order (consts -> layouts -> seqs -> defs), then the nameless contract.
        header = ", ".join(f"{a}: {k}" for a, k in cargs)
        cblock = f"contract ({header}) {{\n" + "\n".join(f"    {cl}" for cl in clauses) + "\n}"
        blocks.append(cblock)
        return "\n\n".join(blocks) + "\n"


def canonicalize(spec_text, contract_name=None):
    """Canonicalize an `.ocl` / `.spec` contract text.

    Returns a dict:
      - `canonical`: canonical nameless `.ocl` UTF-8 text (zero comments, alpha-renamed, closed)
      - `contract_id`: 52-char lowercase RFC 4648 base-32 BLAKE3-256 digest of `canonical`
      - `symbol`: `ode_<contract_id>` (56-char linker symbol)
      - `glossary`: dict mapping canonical names (`f0`, `a0`, `C0`, ...) to the author's names
    """
    sp, is_nameless = _parse_any(spec_text)
    if contract_name is None:
        if len(sp.contracts) != 1:
            raise ValueError(
                f"expected 1 contract when contract_name is omitted, found {len(sp.contracts)}: "
                f"{', '.join(sorted(sp.contracts))}"
            )
        contract_name = next(iter(sp.contracts))
    elif contract_name not in sp.contracts:
        raise ValueError(f"contract `{contract_name}` not found (have: {', '.join(sorted(sp.contracts))})")

    # Run canonicalization to a strict fixed point (at most 2 passes when sorted clauses
    # reorder first-mention numbering of helper functions), composing the glossary cleanly.
    c1 = _Canon(sp)
    canon_text = c1.canonical_contract(contract_name)
    glossary = dict(c1.glossary)
    for _ in range(3):
        sp_next, _ = _parse_any(canon_text)
        c_next = _Canon(sp_next)
        next_text = c_next.canonical_contract(_SENTINEL_NAME)
        if next_text == canon_text:
            break
        # Compose glossary: new_canon_name -> old_canon_name -> author_orig_name
        composed = {}
        if "contract" in glossary:
            composed["contract"] = glossary["contract"]
        for new_k, mid_k in c_next.glossary.items():
            composed[new_k] = glossary.get(mid_k, mid_k)
        glossary = composed
        canon_text = next_text
    cid = blake3_b32(canon_text.encode("utf-8"))
    return {
        "canonical": canon_text,
        "contract_id": cid,
        "symbol": ode_symbol(cid),
        "glossary": glossary,
    }


def is_canonical(ocl_text):
    """Return True iff `ocl_text` is already byte-for-byte in canonical `.ocl` form."""
    try:
        res = canonicalize(ocl_text)
        return res["canonical"] == ocl_text
    except Exception:
        return False


def render_with_glossary(canonical_text, glossary):
    """Render a canonical `.ocl` contract using a reader-chosen glossary (purely cosmetic)."""
    if not glossary:
        return canonical_text
    # Replace whole-word canonical identifiers (C0, L0, S0, f0, a0, ...) with glossary entries.
    # Never mutate reserved keywords or collide two distinct canonical names to the same word.
    safe = {}
    used = set(BUILTINS) | BUILTIN_KINDS | {"const", "layout", "sequence", "def", "contract",
                                            "let", "if", "then", "else", "for", "in", "with",
                                            "requires", "ensures", "returns", "writes", "stack",
                                            "trace", "depends", "on", "result", "needs", "decreases",
                                            "no_overlap", "at", "below", "the", "least", "greatest",
                                            "power", "of", "two", "fails"}
    for k, v in glossary.items():
        if k == "contract" or "." in k:
            continue
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", v):
            continue
        if v in used:
            continue
        used.add(v)
        safe[k] = v
    if not safe:
        return canonical_text
    pat = re.compile(r"\b(" + "|".join(sorted(safe.keys(), key=len, reverse=True)) + r")\b")
    return pat.sub(lambda m: safe[m.group(1)], canonical_text)
