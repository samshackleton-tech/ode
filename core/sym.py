#!/usr/bin/env python3
"""sym: the table's primitives on symbols, and the test that each agrees with its meaning on numbers.

    python3 sym.py [CASES]       the test: every symbolic rule against table.CONC on random values

A row's EFFECT is read on symbols with SYM in place of table.CONC. A 32-bit lane is a term of
kcheck/kterms.py (interned: equal terms are one number; sums and xors flat, sorted, folded), which is what
the specification's side compares by identity. A symbolic rule may refuse (it raises: "not shown"); where
it answers, its answer under any values for the unknowns must be the primitive's meaning on those values.
That is what the test tries, on random terms and random values.

So far: the rules for vectors of 32-bit lanes. The rules for 64-bit registers (numbers, addresses, packed
bytes) come next."""
import os, random, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "kcheck"))
import kterms
import table

M32 = table.M32


class Refuse(Exception):
    """A symbolic rule has no answer here: not shown."""


def whole(f):
    """f for lanes that hold whole terms: half of a rotation is refused."""
    def g(x, y):
        if isinstance(x, tuple) or isinstance(y, tuple): raise Refuse("half of a rotation where a whole word is wanted")
        return f(x, y)
    return g


def half(kind):
    def g(x, n):
        if isinstance(x, tuple) or not 0 < n < 32: raise Refuse("a shift of half a rotation, or by nothing, or by the word's width")
        return (kind, x, n)
    return g


def rotation(T):
    """The or of a word shifted left by 32 - n and the same word shifted right by n: the word rotated right by n."""
    def g(p, q):
        if not (isinstance(p, tuple) and isinstance(q, tuple)): raise Refuse("an or that is not of a rotation's halves")
        if p[0] == "shr": p, q = q, p
        if not (p[0] == "shl" and q[0] == "shr" and p[1] == q[1] and p[2] + q[2] == 32): raise Refuse("an or that is not of a rotation's halves")
        return T.ror(q[1], q[2])
    return g


def pair_lanes(T, v):
    """A 64-bit register moved into a vector register: answered for a counter held as its two words."""
    if not (isinstance(v, tuple) and v[0] == "pair"): raise Refuse("a general register moved to a vector register that is not a counter's two words")
    return (v[1], v[2], T.const(0), T.const(0))


def rules(T):
    """The symbolic rules over the terms T. Immediates stay numbers."""
    return {
        "add32": whole(T.add), "xor32": whole(T.xor), "ror32": whole(lambda x, n: T.ror(x, n % 32) if n % 32 else x),
        "shl32": half("shl"), "shr32": half("shr"), "or32": rotation(T),
        "each32": lambda f, a, b: tuple(f(x, y) for x, y in zip(a, b if isinstance(b, tuple) else (b,) * 4)),
        "lanes": lambda a, b, c, d: (a, b, c, d),
        "lanes_of64": lambda v: pair_lanes(T, v),
        "pick4": table.CONC["pick4"], "blend4": table.CONC["blend4"],
    }


def value(T, t, env):
    """What the term t is when each unknown has its value in env."""
    if isinstance(t, tuple): return (value(T, t[1], env) << t[2]) & M32 if t[0] == "shl" else value(T, t[1], env) >> t[2]
    k = T.nodes[t]
    if k[0] == "c": return k[1]
    if k[0] == "v": return env[k[1:]]
    if k[0] == "add": return sum(value(T, x, env) for x in k[1:]) & M32
    if k[0] == "xor":
        out = 0
        for x in k[1:]: out ^= value(T, x, env)
        return out
    if k[0] == "ror": return table.ror32(value(T, k[1], env), k[2])
    raise ValueError(f"a term this test does not know: {k}")


def term(T, rng, depth=3):
    """A random term over a few unknowns."""
    if depth == 0 or rng.random() < 0.3:
        return T.const(rng.getrandbits(32)) if rng.random() < 0.2 else T.var("u", rng.randrange(6))
    op = rng.choice(["add", "xor", "ror"])
    if op == "ror": return T.ror(term(T, rng, depth - 1), rng.randrange(1, 32))
    return getattr(T, op)(term(T, rng, depth - 1), term(T, rng, depth - 1))


def test(cases=2000, seed=1):
    rng = random.Random(seed)
    T = kterms.Terms(); S = rules(T); bad = 0
    for _ in range(cases):
        env = {("u", i): rng.getrandbits(32) for i in range(6)}
        a = tuple(term(T, rng) for _ in range(4)); b = tuple(term(T, rng) for _ in range(4))
        na = tuple(value(T, t, env) for t in a); nb = tuple(value(T, t, env) for t in b)
        i = rng.randrange(256)
        for name, sym, conc in (
                ("each32 add32", lambda: S["each32"](S["add32"], a, b), lambda: table.CONC["each32"](table.CONC["add32"], na, nb)),
                ("each32 xor32", lambda: S["each32"](S["xor32"], a, b), lambda: table.CONC["each32"](table.CONC["xor32"], na, nb)),
                ("each32 ror32", lambda: S["each32"](S["ror32"], a, i), lambda: table.CONC["each32"](table.CONC["ror32"], na, i)),
                ("pick4", lambda: S["pick4"](a, b, i), lambda: table.CONC["pick4"](na, nb, i)),
                ("a rotation in halves", lambda: S["each32"](S["or32"], S["each32"](S["shl32"], a, 32 - (i % 31 + 1)), S["each32"](S["shr32"], a, i % 31 + 1)),
                 lambda: table.CONC["each32"](table.CONC["ror32"], na, i % 31 + 1)),
                ("each32 shl32", lambda: S["each32"](S["shl32"], a, i % 31 + 1), lambda: table.CONC["each32"](table.CONC["shl32"], na, i % 31 + 1)),
                ("blend4", lambda: S["blend4"](a, b, i), lambda: table.CONC["blend4"](na, nb, i)),
                ("lanes", lambda: S["lanes"](a[0], b[1], a[2], b[3]), lambda: (na[0], nb[1], na[2], nb[3]))):
            if tuple(value(T, t, env) for t in sym()) != tuple(conc()):
                bad += 1; print(f"DIFFERS: {name}")
    print(f"sym: {cases} cases of 8 rules, {bad} differ from the meaning on numbers")
    return bad


if __name__ == "__main__":
    sys.exit(1 if test(int(sys.argv[1]) if len(sys.argv) > 1 else 2000) else 0)
