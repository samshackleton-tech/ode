#!/usr/bin/env python3
"""table: the instruction table (x86.tab) read, and a row's effect worked out on numbers.

    python3 table.py            lists the rows

A row's EFFECT is a few assignments over the primitives below. Each primitive has one meaning, on whole
numbers, given here in a line or two (CONC). The comparison with a processor (cross.py) uses exactly this
meaning; the verifier's reading of the same rows on symbols must agree with it wherever it answers."""
import os, re

HERE = os.path.dirname(os.path.abspath(__file__))
M64, M32 = (1 << 64) - 1, (1 << 32) - 1
UNKNOWN = "unknown"


def ror32(x, n): n %= 32; return ((x >> n) | (x << (32 - n))) & M32


# The primitives: what each means on numbers. Lanes are tuples of four 32-bit numbers, lane 0 the lowest.
CONC = {
    "add64": lambda a, b: (a + b) & M64, "sub64": lambda a, b: (a - b) & M64,
    "and64": lambda a, b: a & b & M64, "or64": lambda a, b: (a | b) & M64,
    "shl64": lambda a, n: (a << n) & M64, "shr64": lambda a, n: (a & M64) >> n,
    "equal": lambda a, b: int(a & M64 == b & M64), "below": lambda a, b: int(a & M64 < b & M64),
    "low8": lambda a: a & 0xFF, "sub8": lambda a, b: (a - b) & 0xFF,
    "setlow8": lambda a, b: (a & ~0xFF & M64) | (b & 0xFF),
    "add32": lambda a, b: (a + b) & M32, "xor32": lambda a, b: a ^ b, "ror32": ror32,
    "each32": lambda f, a, b: tuple(f(x, y) for x, y in zip(a, b if isinstance(b, tuple) else (b,) * 4)),
    "lanes": lambda a, b, c, d: (a, b, c, d),
    "lanes_of64": lambda a: (a & M32, (a >> 32) & M32, 0, 0),
    "pick4": lambda a, b, i: (a[i & 3], a[(i >> 2) & 3], b[(i >> 4) & 3], b[(i >> 6) & 3]),
    "blend4": lambda a, b, i: tuple(b[k] if (i >> k) & 1 else a[k] for k in range(4)),
}
SIZES = {"mem8": 1, "mem64": 8, "mem128": 16}


class Row:
    def __init__(self, name, asm, row, effect):
        self.name, self.asm, self.row, self.text = name, asm, row, effect
        self.effect = [statement(s) for s in effect.split(";")]

    def holders(self):
        """The placeholders of this row's ASM: which registers, immediates and displacements an instance fixes."""
        return sorted(set(re.findall(r"\b([DSB])(?:64|32|8)\b|xmm([XYZ])\b|\b([IN])\b", self.asm)), key=str)


def tokens(text):
    return re.findall(r"[A-Za-z_][A-Za-z_0-9]*|\d+|[().,=]", text)


def statement(text):
    t = tokens(text); at = t.index("=")
    return expression(t[:at]), expression(t[at + 1:])


def expression(t):
    def one(i):
        if t[i].isdigit(): return ("number", int(t[i])), i + 1
        name = t[i]; i += 1
        if i < len(t) and t[i] == "(":
            args, i = [], i + 1
            while t[i] != ")":
                a, i = one(i); args.append(a)
                if t[i] == ",": i += 1
            return ("call", name, args), i + 1
        if i < len(t) and t[i] == ".": return ("lane", name, int(t[i + 1])), i + 2
        return ("name", name), i
    e, i = one(0)
    if i != len(t): raise ValueError(f"cannot read {' '.join(t)}")
    return e


def read(path=os.path.join(HERE, "x86.tab")):
    rows = []
    with open(path) as f:
        for line in f:
            line = line.split("#")[0].strip()
            if not line: continue
            parts = [p.strip() for p in line.split("|")]
            if len(parts) != 4: raise ValueError(f"a row that is not NAME | ASM | ROW | EFFECT: {line}")
            rows.append(Row(*parts))
    return rows


class State:
    """Numbers in registers and memory. g: the sixteen general registers by name; x: vector registers' low
    128 bits as four lanes; mem: {address: byte}; zf, cf."""
    def __init__(self, g, x, mem, zf, cf): self.g, self.x, self.mem, self.zf, self.cf = dict(g), dict(x), dict(mem), zf, cf


def run(row, bind, s):
    """The state after one instance of ROW (bind: placeholder -> register name, vector number or number)
    from state S. A part the row says nothing of is UNKNOWN afterwards."""
    def value(e):
        if e[0] == "number": return e[1]
        if e[0] == "lane": return s.x[bind[e[1]]][e[2]]
        if e[0] == "name":
            n = e[1]
            if n == UNKNOWN: return UNKNOWN
            if n in CONC: return CONC[n]
            if n in ("D", "S", "B"): return s.g[bind[n]]
            if n in ("X", "Y", "Z"): return s.x[bind[n]]
            if n in ("I", "N"): return bind[n] & M64
            if n in ("zf", "cf"): return getattr(s, n)
            return s.g[n]
        name, args = e[1], [value(a) for a in e[2]]
        if name in SIZES:
            at = (args[0] + args[1]) & M64
            raw = int.from_bytes(bytes(s.mem[at + k] for k in range(SIZES[name])), "little")
            return tuple((raw >> (32 * k)) & M32 for k in range(4)) if name == "mem128" else raw
        return CONC[name](*args)
    for lhs, rhs in row.effect:
        v = value(rhs)
        if lhs[0] == "call":
            at = (value(lhs[2][0]) + value(lhs[2][1])) & M64
            raw = sum(w << (32 * k) for k, w in enumerate(v)) if lhs[1] == "mem128" else v
            for k in range(SIZES[lhs[1]]): s.mem[at + k] = (raw >> (8 * k)) & 0xFF
        elif lhs[1] in ("D", "S", "B"): s.g[bind[lhs[1]]] = v
        elif lhs[1] in ("X", "Y", "Z"): s.x[bind[lhs[1]]] = v
        elif lhs[1] in ("zf", "cf"): setattr(s, lhs[1], v)
        else: s.g[lhs[1]] = v
    return s


if __name__ == "__main__":
    for r in read(): print(f"{r.name:11} {r.asm:32} {r.text}")
