#!/usr/bin/env python3
"""table: the instruction table (x86.tab) read, and a row's effect worked out on numbers.

    python3 table.py            lists the rows

A row's EFFECT is a few statements over the primitives below. Each primitive has one meaning, on whole
numbers, given here in a line or two (CONC). The comparison with a processor (cross.py) uses exactly this
meaning; the verifier's reading of the same rows on symbols (step.py) must agree with it wherever it answers.

Statements, run left to right:
    PLACE = EXPRESSION          a register, a flag (zf, cf) or bytes of memory (mem8/mem32/mem64/mem128(base, displacement))
    jump TARGET [if [not] FLAG] the next instruction is at TARGET (if the flag says so)
    call TARGET                 a call of the function there
    return                      the function returns
    nothing"""
import os, re

HERE = os.path.dirname(os.path.abspath(__file__))
M64, M32 = (1 << 64) - 1, (1 << 32) - 1
UNKNOWN = "unknown"
REGISTERS, VECTORS, NUMBERS = ("D", "S", "B", "P"), ("X", "Y", "Z"), ("I", "J", "K", "L", "N")
WIDE, MASKS = {"X512": "X", "Y512": "Y", "Z512": "Z"}, ("M",)      # a vector register's whole 512 bits as sixteen lanes; a mask register's sixteen bits


def ror32(x, n): n %= 32; return ((x >> n) | (x << (32 - n))) & M32


def shuffle_bytes(a, b):
    """Each byte of the result is the byte of a that the same byte of b names by its low four bits, or zero where that byte of b has its top bit set."""
    src = b"".join(w.to_bytes(4, "little") for w in a); by = b"".join(w.to_bytes(4, "little") for w in b)
    out = bytes(0 if m & 0x80 else src[m & 15] for m in by)
    return tuple(int.from_bytes(out[4 * k:4 * k + 4], "little") for k in range(4))


def blend_halves(a, b, i):
    """Each 16-bit half of the result is b's where the bit of i for it is set, else a's."""
    pick = lambda k: ((b if (i >> k) & 1 else a)[k // 2] >> (16 * (k % 2))) & 0xFFFF
    return tuple(pick(2 * k) | pick(2 * k + 1) << 16 for k in range(4))


# The primitives: what each means on numbers. Lanes are tuples of 32-bit numbers, lane 0 the lowest.
CONC = {
    "add64": lambda a, b: (a + b) & M64, "sub64": lambda a, b: (a - b) & M64,
    "and64": lambda a, b: a & b & M64, "or64": lambda a, b: (a | b) & M64,
    "shl64": lambda a, n: (a << n) & M64, "shr64": lambda a, n: (a & M64) >> n,
    "low32": lambda a: a & M32, "at": lambda a, n: (a + n) & M64,
    "equal": lambda a, b: int(a & M64 == b & M64), "below": lambda a, b: int(a & M64 < b & M64),
    "low8": lambda a: a & 0xFF, "sub8": lambda a, b: (a - b) & 0xFF,
    "setlow8": lambda a, b: (a & ~0xFF & M64) | (b & 0xFF),
    "add32": lambda a, b: (a + b) & M32, "xor32": lambda a, b: a ^ b, "ror32": ror32,
    "shl32": lambda a, n: (a << n) & M32, "shr32": lambda a, n: a >> n, "or32": lambda a, b: a | b,
    "each32": lambda f, a, b: tuple(f(x, y) for x, y in zip(a, b if isinstance(b, tuple) else (b,) * len(a))),
    "lanes": lambda a, b, c, d: (a, b, c, d), "words": lambda *numbers: tuple(n & M32 for n in numbers),
    "lanes_of64": lambda a: (a & M32, (a >> 32) & M32, 0, 0),
    "pick4": lambda a, b, i: (a[i & 3], a[(i >> 2) & 3], b[(i >> 4) & 3], b[(i >> 6) & 3]),
    "blend4": lambda a, b, i: tuple(b[k] if (i >> k) & 1 else a[k] for k in range(4)),
    "shuffle_bytes": shuffle_bytes, "blend_halves": blend_halves,
    # sixteen lanes
    "lane32": lambda a: a & M32, "spread16": lambda a: (a,) * 16, "zeros16": lambda: (0,) * 16,
    "words16": lambda n: tuple((n >> (32 * k)) & M32 for k in range(16)),
    "ult32": lambda a, b: int(a < b), "choose16": lambda k, a, b: tuple(p if c else q for c, p, q in zip(k, a, b)),
    # within each quarter of the register (four lanes): lanes picked from the first's quarter (0 to 3) and the second's (4 to 7)
    "in_quarters": lambda a, b, *pick: sum((tuple((a[q:q + 4] + b[q:q + 4])[p] for p in pick) for q in (0, 4, 8, 12)), ()),
    # quarters picked: two of the first register, then two of the second
    "quarters": lambda a, b, i: a[4 * (i % 4):][:4] + a[4 * (i // 4 % 4):][:4] + b[4 * (i // 16 % 4):][:4] + b[4 * (i // 64 % 4):][:4],
}
# bytes of memory at base + displacement (+ index). mem512a: sixty-four bytes on a 64-byte boundary (the instruction faults elsewhere)
SIZES = {"mem8": 1, "mem32": 4, "mem64": 8, "mem128": 16, "mem512": 64, "mem512a": 64}


def parse_row(text):
    """A decoded instruction as nested lists: `.mov 64 (.reg .rax) (.imm 0x4)` -> [".mov", "64", [".reg", ".rax"], [".imm", "0x4"]]."""
    stack = [[]]
    for t in re.findall(r"[()]|[^\s()]+", text):
        if t == "(": stack.append([])
        elif t == ")": done = stack.pop(); stack[-1].append(done)
        else: stack[-1].append(t)
    if len(stack) != 1: raise ValueError(f"brackets do not close in {text}")
    return stack[0]


def unify(pattern, ins, bind):
    """Whether the decoded instruction INS is an instance of the row's PATTERN; BIND gets what each placeholder is:
    a register's name, a vector register's number, or a number's text as the decoder wrote it."""
    if isinstance(pattern, list): return isinstance(ins, list) and len(pattern) == len(ins) and all(unify(p, x, bind) for p, x in zip(pattern, ins))
    if not isinstance(ins, str): return False
    if pattern[:1] == "." and pattern[1:] in REGISTERS:
        if not ins.startswith(".") or pattern == ".P" and ins == ".rsp": return False
        new = ins[1:]
    elif pattern in VECTORS or pattern in MASKS:
        if not ins.isdigit(): return False
        new = int(ins)
    elif pattern in NUMBERS: new = ins
    else: return pattern == ins
    key = pattern.lstrip(".")
    if bind.setdefault(key, new) != new: return False          # a placeholder written twice: the same thing both times
    return True


class Row:
    def __init__(self, name, asm, row, effect):
        self.name, self.asm, self.row, self.text = name, asm, row, effect
        self.pattern = parse_row(row)
        self.effect = [statement(s) for s in effect.split(";")]

    def match(self, ins):
        bind = {}
        return bind if unify(self.pattern, ins, bind) else None


def tokens(text):
    return re.findall(r"[A-Za-z_][A-Za-z_0-9]*|\d+|[().,=]", text)


def statement(text):
    t = tokens(text)
    if "=" in t:
        at = t.index("=")
        return ("set", expression(t[:at]), expression(t[at + 1:]))
    if t[0] == "jump":
        if "if" not in t: return ("jump", expression(t[1:]), None)
        at = t.index("if"); want = t[at + 1] != "not"
        flag = t[at + 1] if want else t[at + 2]
        if flag not in ("zf", "cf") or len(t) != at + (2 if want else 3): raise ValueError(f"cannot read {text}")
        return ("jump", expression(t[1:at]), (flag, want))
    if t[0] == "call": return ("call", expression(t[1:]))
    if t in (["return"], ["nothing"]): return (t[0],)
    raise ValueError(f"cannot read {text}")


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


def by_head(rows):
    """The rows under the first word of their ROW, in the table's order: the first that matches an instruction is its row."""
    heads = {}
    for row in rows: heads.setdefault(row.pattern[0], []).append(row)
    return heads


def find(heads, ins):
    """(the row this decoded instruction is an instance of, what its placeholders are), or (None, None)."""
    for row in heads.get(ins[0], ()):
        bind = row.match(ins)
        if bind is not None: return row, bind
    return None, None


class State:
    """Numbers in registers and memory. g: the sixteen general registers by name; x: the vector registers,
    each sixteen 32-bit lanes; k: the mask registers, each sixteen bits; mem: {address: byte}; zf, cf; after a
    row has run, `to`: where a jump goes (None: the next instruction), `called`: the target of a call, `returned`."""
    def __init__(self, g, x, mem, zf, cf, k=()):
        self.g, self.x, self.mem, self.zf, self.cf, self.k = dict(g), dict(x), dict(mem), zf, cf, dict(k)
        self.to, self.called, self.returned = None, None, False


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
            if n in REGISTERS: return s.g[bind[n]]
            if n in VECTORS: return s.x[bind[n]][:4]
            if n in WIDE: return s.x[bind[WIDE[n]]]
            if n in MASKS: return s.k[bind[n]]
            if n in NUMBERS: return bind[n] & M64
            if n in ("zf", "cf"): return getattr(s, n)
            return s.g[n]
        name, args = e[1], [value(a) for a in e[2]]
        if name in SIZES:
            at, size = sum(args) & M64, SIZES[name]
            raw = int.from_bytes(bytes(s.mem[at + k] for k in range(size)), "little")
            return tuple((raw >> (32 * k)) & M32 for k in range(size // 4)) if size >= 16 else raw
        return CONC[name](*args)
    for st in row.effect:
        if st[0] == "jump":
            if st[2] is None or bool(getattr(s, st[2][0])) == st[2][1]: s.to = value(st[1])
            continue
        if st[0] == "call": s.called = value(st[1]); continue
        if st[0] == "return": s.returned = True; continue
        if st[0] == "nothing": continue
        _, lhs, rhs = st
        v = value(rhs)
        if lhs[0] == "call":
            at, size = sum(value(a) for a in lhs[2]) & M64, SIZES[lhs[1]]
            raw = sum(w << (32 * k) for k, w in enumerate(v)) if size >= 16 else v
            for k in range(size): s.mem[at + k] = (raw >> (8 * k)) & 0xFF
        elif lhs[1] in REGISTERS: s.g[bind[lhs[1]]] = v if v == UNKNOWN else v & M64
        elif lhs[1] in VECTORS: s.x[bind[lhs[1]]] = tuple(v) + (UNKNOWN,) * 12        # of the bits above 127 the row says nothing
        elif lhs[1] in WIDE: s.x[bind[WIDE[lhs[1]]]] = tuple(v)
        elif lhs[1] in MASKS: s.k[bind[lhs[1]]] = tuple(v)
        elif lhs[1] in ("zf", "cf"): setattr(s, lhs[1], v)
        elif lhs[1] == "above128":
            for r in range(16): s.x[r] = tuple(s.x[r][:4]) + (v,) * 12
        else: s.g[lhs[1]] = v if v == UNKNOWN else v & M64
    return s


if __name__ == "__main__":
    for r in read(): print(f"{r.name:13} {r.asm:36} {r.text}")
