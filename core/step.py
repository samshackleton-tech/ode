#!/usr/bin/env python3
"""step: one instruction by the table, on symbols.

`step(m)` does what the instruction at m.pc does to the machine m (kcheck/kfn.py's or kbyte.py's: its
registers, flags, facts and memory, in their forms of value), and it knows no instruction: it finds the
instruction's row in the table (x86.tab), reads the row's EFFECT, and answers each primitive of the effect
with a rule on symbols. A rule is partial (it refuses what it has no answer for: Fail, "not shown"), and
where it answers it must agree with the primitive's meaning on numbers (table.CONC): sym.py and sym64.py
try that on random values.

What is here, then, is of three kinds, none of them about one instruction:
- reading an effect (`run`);
- the rules of the primitives on symbols (`rules`);
- what holds after every instruction (`after`): the stack pointer stays in the function's own frame, the
  stack used is counted, nothing is remembered below the stack pointer, a loop is not run for ever.
Memory, calls, places and the return are the machine's own rules (m.load, m.store, m.call, m.branch)."""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "kcheck")); sys.path.insert(0, HERE)
import kfn
from kterms import Fail, num, signed
from klin import Lin, lin
from kspec import plain, byte_term
import table

M64, M32 = table.M64, table.M32
HEADS = table.by_head(table.read(os.environ["ODE_TABLE"]) if os.environ.get("ODE_TABLE") else table.read())      # (ODE_TABLE: another table, for the tests' controls)
JUMP = {("zf", True): ".je", ("zf", False): ".jne", ("cf", False): ".jae", ("cf", True): ".jb"}      # the machine's names for the four conditions


def q(v):
    """A value as a 64-bit register holds it: a number, or a byte with zeros above it, or what it is."""
    if isinstance(v, int): return ("n", v & M64)
    if v[0] == "byte":
        src = v[1]
        if src[0] == "low": return ("p", ((0, (src[1],)),) + (0,) * 7)
        if src[0] == "p": return ("p", (src[1][0],) + (0,) * 7)
        raise Fail(f"the low byte of {src}")
    return v


def whole(v):
    """Lanes that are each a whole word (half of a rotation is only for the `or` that completes it, or to be moved)."""
    if any(isinstance(t, tuple) for t in v): raise Fail("a vector register holds half of a rotation")
    return v


def rules(m):
    """The primitives on symbols, for the machine m."""
    T = m.T

    def and64(x, y):
        x, y = q(x), q(y)
        # an address in the frame rounded down to a 64-byte boundary: a value of its own, which only the stack pointer may take (`after`)
        if m.BOUNDARY and m.wide is None and x[0] == "a" and x[1] == "frame" and isinstance(x[2], int) and y == ("n", M64 - 63): return ("aligned", x[2])
        if x[0] == "p" and y == ("n", 0xFF): return ("p", (x[1][0],) + (0,) * 7)                # a register's low byte taken
        return m.arith("and", x, y)

    def shr64(x, n):
        x = q(x)
        if x[0] == "p" and n % 8 == 0 and 0 < n < 64: return ("p", tuple(x[1][n // 8:]) + (0,) * (n // 8))      # bytes moved down by whole bytes
        return m.arith("shr", x, ("n", n))

    def setlow8(x, b):
        if not isinstance(b, int): raise Fail(f"a register's low byte set to {b}: not a plain number")
        return ("al", b & 0xFF)                                             # a count put in the low byte; of the rest nothing is said

    def sub8(b, n):
        if not (isinstance(b, tuple) and b[0] == "byte" and b[1][0] == "al" and isinstance(n, int)): raise Fail("a byte counted down that no number was put in")
        return (b[1][1] - n) & 0xFF

    def equal(x, y):
        if isinstance(x, tuple) and x[0] == "byte":
            if x[1][0] == "al" and y == 0: return ("zero", Lin.of(x[1][1]))
            raise Fail(f"a compare of the low byte of {x[1]} and {y}")
        x, y = q(x), q(y)
        if lin(x) is not None and lin(y) is not None: return ("zero", lin(x) - lin(y))
        if x[0] == "q" and y[0] == "n": return ("cond", (x[1], y[1]))        # is an unknown word this number? either way
        raise Fail(f"a compare of {x} and {y}")

    def below(x, y):
        x, y = q(x), q(y)
        return ("neg", lin(x) - lin(y)) if lin(x) is not None and lin(y) is not None else None

    def at(b, n):
        b = q(b)
        if b[0] != "a": raise Fail(f"an address from {b}")
        return ("a", b[1], plain(Lin.of(b[2]) + signed(n)))

    def each32(f, a, b): return tuple(f(x, y) for x, y in zip(a, b if isinstance(b, tuple) else (b,) * len(a)))

    def lane(f):
        def g(x, y):
            if isinstance(x, tuple) or isinstance(y, tuple): raise Fail("a vector register holds half of a rotation")
            return f(x, y)
        return g

    def ror32(x, n):
        if not 0 < n < 32: raise Fail("a rotation by nothing, or by the word's width")
        return T.ror(x, n)

    def half(kind):
        def g(x, n):
            if isinstance(x, tuple): raise Fail("a vector register holds half of a rotation")
            if not 0 < n < 32: raise Fail("a shift by nothing, or by the word's width")
            return (kind, x, n)
        return g

    def or32(p, r):
        # the two halves of a rotation: (x << (32 - n)) | (x >> n)
        if not (isinstance(p, tuple) and isinstance(r, tuple)): raise Fail("an or that is not of a rotation's halves")
        if p[0] == "shr": p, r = r, p
        if not (p[0] == "shl" and r[0] == "shr" and p[1] == r[1] and p[2] + r[2] == 32): raise Fail("an or that is not of a rotation's halves")
        return T.ror(r[1], r[2])

    def lanes(*them): return whole(them)

    def words(*numbers): return tuple(T.const(n & M32) for n in numbers)

    def lanes_of64(v):
        # the low 64 bits from a general register, zero above: a counter's two words; or bytes, each word a byte with zeros above it
        v = q(v)
        if v[0] == "pair": return (v[1], v[2], T.const(0), T.const(0))
        if v[0] == "p":
            if any(b != 0 for k, b in enumerate(v[1]) if k % 4): raise Fail(f"a register moved to a vector register whose words are not each a byte: {v}")
            return tuple(T.const(b) if isinstance(b, int) else byte_term(T, b) for b in (v[1][0], v[1][4])) + (T.const(0), T.const(0))
        raise Fail(f"a general register moved to a vector register: {v}")

    def shuffle_bytes(src, mask):
        # by a constant that rotates each word's bytes: a rotation of each word by whole bytes
        src, mask, out = whole(src), whole(mask), []
        for k, w in enumerate(mask):
            c = T.nodes[w]
            if c[0] != "c": raise Fail("a shuffle of bytes by something that is not a constant")
            idx = [(c[1] >> (8 * j)) & 0xFF for j in range(4)]
            r = idx[0] - 4 * k
            if not 0 <= r < 4 or any(idx[j] != 4 * k + (r + j) % 4 for j in range(4)): raise Fail("a shuffle of bytes that is not a rotation of each word")
            out.append(T.ror(src[k], 8 * r) if r else src[k])
        return tuple(out)

    def blend_halves(x, y, n):
        # by 16-bit halves: both halves of a word from one source, or this is no blend of words
        x, y = whole(x), whole(y)
        if any(((n >> (2 * j)) & 3) not in (0, 3) for j in range(4)): raise Fail("a blend that splits a word")
        return tuple(y[j] if (n >> (2 * j)) & 1 else x[j] for j in range(4))

    def lane32(v):
        # a 32-bit value of a general register or of memory, as a lane
        if v[0] == "t": return v[1]
        if v[0] == "n": return T.const(v[1])
        if v[0] == "p" and all(b == 0 for b in v[1][1:]): return byte_term(T, v[1][0])
        raise Fail(f"a word from {v}")

    wide = {"lane32": lane32, "spread16": lambda w: (w,) * 16, "zeros16": lambda: (T.const(0),) * 16,
            "words16": lambda n: tuple(T.const((n >> (32 * k)) & M32) for k in range(16)),
            "ult32": T.ult, "choose16": lambda k, a, b: tuple(T.ite(c, p, old) for c, p, old in zip(k, a, b)),
            "in_quarters": table.CONC["in_quarters"], "quarters": table.CONC["quarters"]}
    return wide | {
        "add64": lambda x, y: m.arith("add", q(x), q(y)), "sub64": lambda x, y: m.arith("sub", q(x), q(y)),
        "or64": lambda x, y: m.arith("or", q(x), q(y)), "and64": and64,
        "shl64": lambda x, n: m.arith("shl", q(x), ("n", n)), "shr64": shr64,
        "low32": lambda x: m.low32(q(x)), "low8": lambda x: ("byte", q(x)), "setlow8": setlow8, "sub8": sub8,
        "equal": equal, "below": below, "at": at, "data": lambda w: ("a", "rodata", w),
        "each32": each32, "add32": lane(T.add), "xor32": lane(T.xor), "ror32": lane(ror32), "shl32": half("shl"), "shr32": half("shr"), "or32": or32,
        "lanes": lanes, "words": words, "lanes_of64": lanes_of64, "shuffle_bytes": shuffle_bytes, "blend_halves": blend_halves,
        "pick4": lambda a, b, i: table.CONC["pick4"](whole(a), whole(b), i), "blend4": lambda a, b, i: table.CONC["blend4"](whole(a), whole(b), i & 15),
    }


def split(flags):
    """The machine's one record of the flags, as the two the table speaks of: (zf, cf)."""
    if flags is None: return None, None
    if flags[0] == "numbers": return ("zero", flags[1]), (None if len(flags) > 2 else ("neg", flags[1]))
    return ("cond", flags[1]), None


def join(zf, cf):
    if zf is None: return None                                              # (a carry known beside an unknown zero flag: no row leaves that)
    if zf[0] == "cond": return ("unknown", zf[1])
    return ("numbers", zf[1]) if cf == ("neg", zf[1]) else ("numbers", zf[1], "zero")


def run(m, row, bind):
    """The row's effect on m. Returns where the next instruction is (None: the function has returned)."""
    R = rules(m)
    nxt = m.rows[m.pc][0]
    zf, cf = split(m.flags)
    wrote = flagged = False

    def address(b, n, index=None):
        b = q(b)
        if b[0] != "a": raise Fail(f"an address from {b}")
        off = Lin.of(b[2]) + signed(n)
        if index is not None:
            if lin(index) is None: raise Fail(f"an index that is not a number: {index}")
            off = off + lin(index)
        return b[1], plain(off)

    def place(name, args):
        """(region, offset, bytes) of the memory an effect names."""
        where = address(*[value(a) for a in args])
        if name == "mem512a" and where[0] != "wide": raise Fail(f"an aligned read or write of 64 bytes at {where[0]} + {where[1]}: not known to be on a 64-byte boundary")
        return where + (table.SIZES[name],)

    def value(e):
        if e[0] == "number": return e[1]
        if e[0] == "lane": return m.halves(bind[e[1]])[e[2]]
        if e[0] == "name":
            n = e[1]
            if n in R: return R[n]
            if n in table.REGISTERS: return m.g[bind[n]]
            if n in table.VECTORS: return m.halves(bind[n])
            if n in table.WIDE: return m.vec(bind[table.WIDE[n]])
            if n in table.MASKS:
                if ("k", bind[n]) not in m.x: raise Fail(f"k{bind[n]} read before it is written")
                return m.x[("k", bind[n])]
            if n in table.NUMBERS: return num(bind[n])
            if n == table.UNKNOWN: return None
            return m.g[n]                                                   # a register by its own name
        if e[1] in table.SIZES: return m.load(*place(e[1], e[2]))
        return R[e[1]](*[value(a) for a in e[2]])

    try:
        for st in row.effect:
            if st[0] == "jump":
                if st[2] is None or m.branch(JUMP[st[2]]): nxt = value(st[1])
            elif st[0] == "call": m.call(bind[st[1][1]]); wrote = True
            elif st[0] == "return":
                if m.g["rsp"] != ("a", "frame", 0) or m.mem["frame"].get(0) != (8, "q", ("q", "return address")): raise Fail("a return to somewhere else")
                nxt = None
            elif st[0] == "set":
                _, lhs, rhs = st
                v = value(rhs)
                if lhs[0] == "call":                                        # bytes of memory
                    region, off, size = place(lhs[1], lhs[2])
                    if size == 1: v = ("n", v & 0xFF) if isinstance(v, int) else v[1] if v[0] == "byte" else v
                    m.store(region, off, size, whole(v) if size == 16 else v if size == 64 else q(v))
                elif lhs[1] in table.VECTORS: m.x[bind[lhs[1]]] = tuple(v)
                elif lhs[1] in table.WIDE: m.x[bind[table.WIDE[lhs[1]]]] = tuple(v)
                elif lhs[1] in table.MASKS: m.x[("k", bind[lhs[1]])] = tuple(v)
                elif lhs[1] == "zf": zf = v; flagged = True
                elif lhs[1] == "cf": cf = v; flagged = True
                elif lhs[1] == "above128":
                    for r in range(16):
                        if r in m.x: m.x[r] = m.x[r][:4]
                else: m.g[bind[lhs[1]] if lhs[1] in table.REGISTERS else lhs[1]] = q(v)
                wrote = True
    except kfn.Fork:
        if wrote: raise Fail("a path would split after part of an instruction is done")
        raise
    if flagged: m.flags = join(zf, cf)
    return nxt


def after(m, nxt):
    """What holds after every instruction, whatever it was."""
    if nxt is not None and nxt <= m.pc:
        m.back[nxt] = m.back.get(nxt, 0) + 1
        if m.back[nxt] > kfn.TURNS: raise Fail(f"a loop has turned {kfn.TURNS} times on one path: not a loop this verifier runs")
    sp = m.g["rsp"]
    if sp[0] == "aligned":
        # the stack pointer rounded down to a 64-byte boundary: from here it is in a part of the frame of its
        # own ("wide"), whose top is 0 to 63 bytes below where the stack pointer was
        m.wide = sp[1]; m.g["rsp"] = sp = ("a", "wide", 0); m.mem["wide"] = {}
    # The stack pointer is in the function's own frame, a plain number of bytes not above where it was at entry.
    if m.wide is not None and sp[0] == "a" and sp[1] == "frame": m.wide = None; del m.mem["wide"]         # back in the frame as it was
    if sp[0] != "a" or sp[1] != ("frame" if m.wide is None else "wide") or not isinstance(sp[2], int) or sp[2] > 0: raise Fail(f"the stack pointer leaves the function's own frame: {sp}")
    m.low = min(m.low, sp[2] if m.wide is None else m.wide - 63 + sp[2])
    # Nothing is remembered of the stack below the stack pointer: a call writes there, and so may whatever interrupts the program.
    floor = m.floor()
    for o in [o for o in m.mem["frame"] if o < floor]: del m.mem["frame"][o]
    if m.wide is not None:
        for o in [o for o in m.mem["wide"] if o < sp[2]]: del m.mem["wide"][o]
    m.steps += 1; m.pc = nxt


def step(m):
    """The instruction at m.pc, by the table."""
    if m.pc not in m.rows: raise Fail(f"no instruction at 0x{m.pc:X}")
    ins = m.rows[m.pc][1]
    row, bind = table.find(HEADS, ins)
    if row is None: raise Fail(f"an instruction the table has no row for: {' '.join(map(str, ins))}")
    after(m, run(m, row, bind))
