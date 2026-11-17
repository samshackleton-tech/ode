#!/usr/bin/env python3
"""sym64: today's rules for 64-bit registers (kcheck/kfn.py's `arith`) against the meaning on numbers.

    python3 sym64.py [CASES]

The table's rows of 64-bit registers say `D = add64(D, S)` and the like; on symbols the present verifier
answers them with `kfn.Machine.arith`, a list of special cases over a few forms of value, refusing the
rest. Those cases had no test of their own. Here each form of value is given its meaning as a number
(under random values of the unknowns that satisfy the facts in play), random pairs of values are put to
`arith`, and wherever it answers, the answer's meaning must be table.CONC's result on the two meanings.

Forms tried: ("n", k) a known number; ("l", Lin) a number that depends on unknowns; ("a", region, offset)
an address; ("t", term) a 32-bit word, zeros above; ("pair", lo, hi) two words side by side. Not tried yet:
packed bytes ("p"), and the byte forms. Exit 1 if any answer differs."""
import os, random, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "kcheck")); sys.path.insert(0, HERE)
import kfn, klin, kterms
import sym, table

M64 = table.M64
OPS = {"add": "add64", "sub": "sub64", "and": "and64", "or": "or64", "shl": "shl64", "shr": "shr64"}
BASES = {"r": 0x7F0000001000, "s": 0x7F0000100000}
QUOTIENTS = {}          # the name of a quotient the rules introduce -> (what is divided, by what)
SEEN = {}               # (operation, form of the first value, form of the second) -> how many answers were compared
# every case of the rules that these forms can reach: a run that compares none of one is not a test of it
CASES = [("add", "t", "pair"), ("add", "a", "l"), ("add", "a", "n"), ("add", "l", "a"), ("add", "n", "a"), ("add", "l", "l"), ("add", "l", "n"), ("add", "n", "n"),
         ("sub", "a", "l"), ("sub", "a", "n"), ("sub", "l", "l"), ("sub", "l", "n"), ("sub", "n", "n"), ("shl", "t", "n"), ("shl", "l", "n"), ("shl", "n", "n"),
         ("shr", "n", "n"), ("shr", "pair", "n"), ("shr", "l", "n"), ("and", "n", "n"), ("and", "l", "n"), ("or", "n", "n"), ("or", "l", "n"), ("or", "n", "l")]
_halved = kfn.halved


def halved(facts, x, d):
    q = _halved(facts, x, d)
    if isinstance(q, klin.Lin) and len(q.c) == 1 and q.c[0][0] not in QUOTIENTS and q.c[0][0].endswith(f")/{d}"): QUOTIENTS[q.c[0][0]] = (klin.Lin.of(x), d)
    return q


kfn.halved = halved


class Stub:
    """As much of a machine as `arith` and `number` use: the facts and the terms."""
    RULE = staticmethod(kfn.Machine.arith)          # the rules under test (a test's control puts wrong ones here)
    def __init__(self, facts, T): self.facts, self.T = facts, T
    def number(self, d): return kfn.Machine.number(self, d)
    def arith(self, op, x, y): return Stub.RULE(self, op, x, y)


def meaning(T, v, env):
    """The number a register holding v holds, when each unknown has its value in env."""
    def name(s):
        if s not in env: x, d = QUOTIENTS[s]; env[s] = of(x) // d            # a quotient the rules made: its dividend, divided
        return env[s]
    def of(x): x = klin.Lin.of(x); return sum(a * name(s) for s, a in x.c) + x.k
    if v[0] == "n": return v[1] & M64
    if v[0] == "l": return of(v[1]) & M64
    if v[0] == "a": return (BASES[v[1]] + of(v[2])) & M64
    if v[0] == "t": return sym.value(T, v[1], env)
    if v[0] == "pair": return sym.value(T, v[1], env) | sym.value(T, v[2], env) << 32
    raise ValueError(f"a form this test does not know: {v}")


def some(T, rng):
    """A random value of one of the forms."""
    kind = rng.choice(["n", "n", "l", "l", "a", "t", "pair"])
    small = lambda: klin.Lin([(f"u{rng.randrange(3)}", rng.randrange(1, 9))], rng.randrange(0, 4096))
    if kind == "n": return ("n", rng.choice([rng.getrandbits(64), rng.randrange(0, 70000), 1, 0]))
    if kind == "l": return ("l", small())
    if kind == "a": return ("a", rng.choice("rs"), rng.choice([rng.randrange(0, 512), small()]))
    if kind == "t": return ("t", sym.term(T, rng, 2))
    return ("pair", rng.choice([T.const(0), sym.term(T, rng, 1)]), sym.term(T, rng, 1))


def test(cases=3000, seed=1):
    rng = random.Random(seed); SEEN.clear()
    T = kterms.Terms(); F = klin.Facts()
    for i in range(3):
        F.add(klin.sym(f"u{i}")); F.add(klin.Lin([(f"u{i}", -1)], 1 << 20))          # 0 <= u_i <= 2^20
    m = Stub(F, T); answered, bad, per = 0, 0, {}; base = F
    for _ in range(cases):
        env = {f"u{i}": rng.randrange(0, (1 << 20) + 1) for i in range(3)}
        env.update({("u", i): rng.getrandbits(32) for i in range(6)})
        op = rng.choice(list(OPS)); x = some(T, rng)
        y = ("n", rng.choice([1, 4, 8, 16, 32, rng.randrange(1, 64)])) if op in ("shl", "shr") else some(T, rng)
        m.facts = base.clone()
        try: z = m.arith(op, x, y)
        except (kterms.Fail, kfn.Fork): continue
        answered += 1; per[op] = per.get(op, 0) + 1; SEEN[(op, x[0], y[0])] = SEEN.get((op, x[0], y[0]), 0) + 1
        want = table.CONC[OPS[op]](meaning(T, x, env), y[1] if op in ("shl", "shr") else meaning(T, y, env))
        if meaning(T, z, env) != want:
            bad += 1
            if bad <= 8: print(f"DIFFERS: {op} of {x} and {y} is said to be {z}")
    missed = [c for c in CASES if not SEEN.get(c)]
    print(f"sym64: {cases} cases, {answered} answered ({', '.join(f'{k} {v}' for k, v in sorted(per.items()))}), {bad} differ from the meaning on numbers"
          + (f"; NOT TRIED: {missed}" if missed else f"; each of the {len(CASES)} cases of the rules was compared"))
    return bad + len(missed)


if __name__ == "__main__":
    sys.exit(1 if test(int(sys.argv[1]) if len(sys.argv) > 1 else 3000) else 0)
