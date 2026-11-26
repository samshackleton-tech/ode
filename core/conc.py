#!/usr/bin/env python3
"""conc: what each primitive of the table means on whole numbers, and a row's effect worked out on them.

Each primitive has one meaning, given here in a line or two (CONC). The comparison of the rows with a
processor (cross.py) uses exactly this meaning; the verifier's rules on symbols (step.py) must agree with
it wherever they answer (meaning.py). No verification loads this file."""
from table import M64, M32, UNKNOWN, REGISTERS, VECTORS, NUMBERS, WIDE, MASKS, SIZES, MOVES


class Fault(Exception):
    """The processor faults here: the row has no state after it."""


def on16(a):
    """The number, where it is a multiple of 16 (AArch64's stack pointer as the base of a load or store); a fault where it is not."""
    if a % 16: raise Fault("a stack pointer that is no multiple of 16 is the base of a load or store")
    return a


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
    "low8": lambda a: a & 0xFF, "sub8": lambda a, b: (a - b) & 0xFF, "on16": on16,
    "setlow8": lambda a, b: (a & ~0xFF & M64) | (b & 0xFF),
    "add32": lambda a, b: (a + b) & M32, "xor32": lambda a, b: a ^ b, "and32": lambda a, b: a & b, "ror32": ror32,
    "shl32": lambda a, n: (a << n) & M32, "shr32": lambda a, n: a >> n, "or32": lambda a, b: a | b,
    "each32": lambda f, a, b: tuple(f(x, y) for x, y in zip(a, b if isinstance(b, tuple) else (b,) * len(a))),
    "lanes": lambda a, b, c, d: (a, b, c, d), "words": lambda *numbers: tuple(n & M32 for n in numbers),
    "lanes_of64": lambda a: (a & M32, (a >> 32) & M32, 0, 0),
    "shuffle_bytes": shuffle_bytes, "blend_halves": blend_halves,
    # sixteen lanes
    "lane32": lambda a: a & M32, "spread16": lambda a: (a,) * 16, "zeros16": lambda: (0,) * 16,
    "words16": lambda n: tuple((n >> (32 * k)) & M32 for k in range(16)),
    "ult32": lambda a, b: int(a < b), "choose16": lambda k, a, b: tuple(p if c else q for c, p, q in zip(k, a, b)),
} | MOVES


class State:
    """Numbers in registers and memory. g: the sixteen general registers by name; x: the vector registers,
    each sixteen 32-bit lanes; k: the mask registers, each sixteen bits; mem: {address: byte}; zf, cf; after a
    row has run, `to`: where a jump or a return by a register goes (None: the next instruction), `called`: the
    target of a call, `returned`. (A call that puts the address to come back to in a register leaves that
    register UNKNOWN here: where the instruction lies is not part of this state.)"""
    def __init__(self, g, x, mem, zf, cf, k=()):
        self.g, self.x, self.mem, self.zf, self.cf, self.k = dict(g), dict(x), dict(mem), zf, cf, dict(k)
        self.to, self.called, self.returned = None, None, False


def run(row, bind, s, trace=None):
    """The state after one instance of ROW (bind: placeholder -> register name, vector number or number)
    from state S. A part the row says nothing of is UNKNOWN afterwards. If `trace` is a list, each memory
    read or write appends ("R"|"W", address, size)."""
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
            if n in NUMBERS: return bind[n] if not isinstance(bind[n], int) or bind[n] > M64 else bind[n] & M64         # (a number of sixteen words is whole)
            if n in ("zf", "cf"): return getattr(s, n)
            return s.g[n]
        name, args = e[1], [value(a) for a in e[2]]
        if name in SIZES:
            at, size = sum(args) & M64, SIZES[name]
            if trace is not None: trace.append(("R", at, size))
            raw = int.from_bytes(bytes(s.mem[at + k] for k in range(size)), "little")
            return tuple((raw >> (32 * k)) & M32 for k in range(size // 4)) if size >= 16 else raw
        return CONC[name](*args)
    for st in row.effect:
        if st[0] == "jump":
            if st[2] is None or (((not bool(s.cf)) and (not bool(s.zf))) if st[2][0] == "hi" else bool(getattr(s, st[2][0]))) == st[2][1]:
                s.to = value(st[1])
            continue
        if st[0] == "call":
            s.called = value(st[1])
            if len(st) == 3: s.g[st[2]] = UNKNOWN
            continue
        if st[0] == "return":
            s.returned = True
            if len(st) == 2: s.to = s.g[st[1]]
            continue
        if st[0] == "nothing": continue
        _, lhs, rhs = st
        v = value(rhs)
        if lhs[0] == "call":
            at, size = sum(value(a) for a in lhs[2]) & M64, SIZES[lhs[1]]
            if trace is not None: trace.append(("W", at, size))
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
