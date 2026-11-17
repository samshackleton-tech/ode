#!/usr/bin/env python3
"""meaning: every rule of step.py on symbols, against its primitive's meaning on numbers.

    python3 meaning.py [CASES]

A row of the table says `D = add64(D, S)`. On numbers add64 has one meaning (conc.CONC), and that is what
is compared with a processor. On symbols step.py answers it with a rule over the verifier's forms of value,
refusing what it has no answer for. Here each form is given its meaning as a number (or as some bits of a
number, for a form that says only some) under random values of the unknowns that satisfy the facts in
play; random values of every form are put to every rule; and wherever a rule answers, the answer's meaning
must be the primitive's result on the arguments' meanings. A rule that never answered was not tested: that
fails too. Exit 1 on either.

The machine here is kcheck/kfn.py's, and then kbyte.py's (whose rules for numbers answer more), with
nothing in it but the facts and the terms: the rules use no more of it."""
import os, random, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "kcheck")); sys.path.insert(0, HERE)
import kbyte, kfn, klin, kterms
import conc, step, table

M64, M32 = table.M64, table.M32
BASES = {"frame": 0x7FFC00001238, "r": 0x7F0000001000, "s": 0x7F0000100040}
QUOTIENTS = {}          # the name of a quotient the rules introduce -> (what is divided, by what)
TWO, ONE = ("add64", "sub64", "and64", "or64", "below"), ("shl64", "shr64", "low32", "low8", "at", "lanes_of64", "lane32")
FORMS = {}              # (a rule of 64-bit registers, the forms of its arguments) -> how many answers were compared
_halved = kfn.halved


def halved(facts, x, d):
    q = _halved(facts, x, d)
    if isinstance(q, klin.Lin) and len(q.c) == 1 and q.c[0][0] not in QUOTIENTS and q.c[0][0].endswith(f")/{d}"): QUOTIENTS[q.c[0][0]] = (klin.Lin.of(x), d)
    return q


kfn.halved = kbyte.halved = halved
# every case of the rules for 64-bit registers: a run that compares no answer of one is not a test of it
CASES = [(name,) + tuple(forms.split("/")) for name, all_forms in (
    ("add64", "a/l a/n l/a l/l l/n n/a n/l n/n p/p t/pair"), ("sub64", "a/l a/n l/l l/n n/l n/n"), ("and64", "a/n l/n n/n p/n"),
    ("or64", "l/n n/l n/n n/p p/n p/p"), ("below", "l/l l/n n/l n/n"), ("shl64", "l lowt n p t"), ("shr64", "l n p pair"),
    ("low32", "n p pair t"), ("low8", "low p"), ("at", "a"), ("lanes_of64", "p pair"), ("lane32", "n p pair t")) for forms in all_forms.split()]


def machine(kind, facts, T):
    """A machine of the verifier's with nothing in it but the facts and the terms."""
    m = kind.__new__(kind)
    m.facts, m.T, m.halves, m.secret, m.g = facts, T, [], set(), {"rsp": ("a", "frame", -8)}
    return m


def term_value(T, t, env):
    """What a 32-bit term (or half of a rotation) is when each unknown has its value in env."""
    if isinstance(t, tuple): return (term_value(T, t[1], env) << t[2]) & M32 if t[0] == "shl" else term_value(T, t[1], env) >> t[2]
    k = T.nodes[t]
    if k[0] == "c": return k[1]
    if k[0] == "v": return env[k[1:]]
    if k[0] == "add": return sum(term_value(T, x, env) for x in k[1:]) & M32
    if k[0] == "xor":
        out = 0
        for x in k[1:]: out ^= term_value(T, x, env)
        return out
    if k[0] == "ror": return conc.ror32(term_value(T, k[1], env), k[2])
    if k[0] == "ult": return int(term_value(T, k[1], env) < term_value(T, k[2], env))
    if k[0] == "ite": return term_value(T, k[2] if term_value(T, k[1], env) else k[3], env)
    if k[0] == "orb": return byte_value((k[1], k[2]), env)
    raise ValueError(f"a term this test does not know: {k}")


def byte_value(b, env):
    if isinstance(b, int): return b
    out = b[0]
    for name in b[1]: out |= env[name]
    return out


def number_of(x, env):
    def name(s):
        if s not in env: d, by = QUOTIENTS[s]; env[s] = number_of(d, env) // by           # a quotient the rules made: its dividend, divided
        return env[s]
    x = klin.Lin.of(x)
    return sum(a * name(s) for s, a in x.c) + x.k


def meaning(T, v, env):
    """(which bits of a 64-bit register the form v speaks of, what they are)."""
    if isinstance(v, int): return M64, v & M64
    if v[0] == "n": return M64, v[1] & M64
    if v[0] == "l": return M64, number_of(v[1], env) & M64
    if v[0] == "a": return M64, (BASES[v[1]] + number_of(v[2], env)) & M64
    if v[0] == "aligned": return M64, (BASES["frame"] + v[1]) & ~63 & M64
    if v[0] == "t": return M64, term_value(T, v[1], env)
    if v[0] == "lowt": return M32, term_value(T, v[1], env)
    if v[0] == "pair": return M64, term_value(T, v[1], env) | term_value(T, v[2], env) << 32
    if v[0] == "p": return M64, sum(byte_value(b, env) << (8 * k) for k, b in enumerate(v[1]))
    if v[0] == "low": return 0xFF, env[v[1]]
    if v[0] == "al": return 0xFF, v[1]
    if v[0] == "q": return M64, env[("q", v[1])]
    if v[0] == "byte": return 0xFF, meaning(T, v[1], env)[1] & 0xFF
    raise ValueError(f"a form this test does not know: {v}")


def some_term(T, rng, depth=2):
    if depth == 0 or rng.random() < 0.3: return T.const(rng.getrandbits(32)) if rng.random() < 0.2 else T.var("u", rng.randrange(6))
    op = rng.choice(["add", "xor", "ror"])
    if op == "ror": return T.ror(some_term(T, rng, depth - 1), rng.randrange(1, 32))
    return getattr(T, op)(some_term(T, rng, depth - 1), some_term(T, rng, depth - 1))


def some_byte(rng): return rng.choice([0, 0, rng.randrange(1, 256), (rng.choice([0, 0, 64]), (f"b{rng.randrange(4)}",))])


def some(T, rng, kinds="n n l l a t pair p low al q lowt"):
    """A random value of one of the forms a 64-bit register holds."""
    kind = rng.choice(kinds.split())
    small = lambda: klin.Lin([(f"u{rng.randrange(3)}", rng.randrange(1, 9))], rng.randrange(0, 4096))
    if kind == "n": return ("n", rng.choice([rng.getrandbits(64), rng.getrandbits(32), rng.randrange(0, 70000), 1, 0, 0xFF, M64 - 63]))
    if kind == "l": return ("l", small())
    if kind == "a": return ("a", "frame", -8 * rng.randrange(0, 64)) if rng.random() < 0.4 else ("a", rng.choice("rs"), rng.choice([rng.randrange(0, 512), small()]))
    if kind == "t": return ("t", some_term(T, rng))
    if kind == "lowt": return ("lowt", some_term(T, rng))
    if kind == "pair": return ("pair", rng.choice([T.const(0), some_term(T, rng, 1)]), some_term(T, rng, 1))
    if kind == "p":
        shape = rng.randrange(4)
        b = [some_byte(rng) for _ in range(8)]
        if shape == 1: b[1:] = [0] * 7
        if shape == 2: b = [b[0], 0, 0, 0, b[4], 0, 0, 0]
        if shape == 3: b[4:] = [0] * 4
        return ("p", tuple(b))
    if kind == "low": return ("low", f"b{rng.randrange(4)}")
    if kind == "al": return ("al", rng.randrange(256))
    return ("q", f"w{rng.randrange(2)}")


def test(cases=4000, seed=1, rules=step.rules, say=True, of=kfn.Machine):
    rng = random.Random(seed); FORMS.clear()
    T = kterms.Terms(); base = klin.Facts()
    for i in range(3): base.add(klin.sym(f"u{i}")); base.add(klin.Lin([(f"u{i}", -1)], 1 << 20))          # 0 <= u_i <= 2^20
    m = machine(of, base, T); C = conc.CONC
    seen, bad, shown = {}, 0, 0

    for _ in range(cases):
        m.facts, m.halves = base.clone(), []
        R = rules(m)
        env = {f"u{i}": rng.randrange(0, (1 << 20) + 1) for i in range(3)}
        env.update({("u", i): rng.getrandbits(32) for i in range(6)}); env.update({f"b{i}": rng.randrange(256) for i in range(4)})
        env.update({("q", f"w{i}"): rng.choice([rng.getrandbits(64), 5, 0]) for i in range(2)})
        fill = rng.getrandbits(64)                                               # the bits a form says nothing of

        def num(v):
            mask, bits = meaning(T, v, env)
            return bits | (fill & ~mask & M64)
        def lanes(n=4): return tuple(some_term(T, rng) for _ in range(n))
        def lv(v): return tuple(term_value(T, t, env) for t in v)
        x, y = some(T, rng), some(T, rng)
        if x[0] == "p" and rng.random() < 0.3: y = ("n", 0xFF)
        m.g["rsp"] = ("a", "frame", -8 * rng.randrange(0, 64))
        if x[:2] == ("a", "frame") and rng.random() < 0.3: y = ("n", M64 - 63); m.g["rsp"] = x          # the stack pointer's own value, rounded down
        if x[0] == "l" and rng.random() < 0.3: y = ("n", (1 << rng.randrange(1, 12)) - 1)                  # a mask
        if x[0] == "l" and rng.random() < 0.2: x, y = ("l", x[1].scale(16)), ("n", rng.randrange(16))         # a multiple of sixteen, and less than sixteen
        n = rng.choice([0, 1, 4, 8, 16, 24, 32, 40, rng.randrange(64)])
        i = rng.randrange(256); r = i % 32
        a, b = lanes(), lanes(); wa, wb = lanes(16), lanes(16)
        k = tuple(T.ult(p, q) for p, q in zip(lanes(16), lanes(16)))
        rot = [rng.randrange(4) for _ in range(4)]
        rotate = tuple(T.const(sum((4 * lane + (rot[lane] + j) % 4) << (8 * j) for j in range(4))) for lane in range(4))
        whole = sum((3 if rng.random() < 0.5 else 0) << (2 * j) for j in range(4))
        al = ("al", rng.randrange(256))
        quarter = rng.choice([(0, 4, 1, 5), (2, 6, 3, 7), (0, 1, 4, 5), (2, 3, 6, 7)])
        numbers = [rng.getrandbits(32) for _ in range(4)]
        big = rng.getrandbits(512)
        disp = rng.choice([rng.randrange(0, 256), M64 - rng.randrange(0, 256)])
        # (the rule's name, how the answer is to be read, the rule on symbols, the primitive on numbers)
        probes = [
            ("add64", "q", lambda: R["add64"](x, y), lambda: C["add64"](num(x), num(y))),
            ("sub64", "q", lambda: R["sub64"](x, y), lambda: C["sub64"](num(x), num(y))),
            ("and64", "q", lambda: R["and64"](x, y), lambda: C["and64"](num(x), num(y))),
            ("or64", "q", lambda: R["or64"](x, y), lambda: C["or64"](num(x), num(y))),
            ("shl64", "q", lambda: R["shl64"](x, n), lambda: C["shl64"](num(x), n)),
            ("shr64", "q", lambda: R["shr64"](x, n), lambda: C["shr64"](num(x), n)),
            ("low32", "q", lambda: R["low32"](x), lambda: C["low32"](num(x))),
            ("low8", "q", lambda: step.q(R["low8"](x)), lambda: C["low8"](num(x))),
            ("setlow8", "q", lambda: R["setlow8"](x, i), lambda: C["setlow8"](num(x), i)),
            ("sub8", "n", lambda: R["sub8"](R["low8"](al), 1), lambda: C["sub8"](C["low8"](num(al)), 1)),
            ("equal", "f", lambda: R["equal"](x, y), lambda: C["equal"](num(x), num(y))),
            ("equal", "f", lambda: R["equal"](R["low8"](al), 0), lambda: C["equal"](C["low8"](num(al)), 0)),
            ("below", "f", lambda: R["below"](x, y), lambda: C["below"](num(x), num(y))),
            ("at", "q", lambda: R["at"](x, disp), lambda: C["at"](num(x), disp)),
            ("add32", "v", lambda: R["each32"](R["add32"], a, b), lambda: C["each32"](C["add32"], lv(a), lv(b))),
            ("xor32", "v", lambda: R["each32"](R["xor32"], a, b), lambda: C["each32"](C["xor32"], lv(a), lv(b))),
            ("ror32", "v", lambda: R["each32"](R["ror32"], a, r), lambda: C["each32"](C["ror32"], lv(a), r)),
            ("shl32", "v", lambda: R["each32"](R["shl32"], a, r), lambda: C["each32"](C["shl32"], lv(a), r)),
            ("shr32", "v", lambda: R["each32"](R["shr32"], a, r), lambda: C["each32"](C["shr32"], lv(a), r)),
            ("or32", "v", lambda: R["each32"](R["or32"], R["each32"](R["shl32"], a, 32 - r), R["each32"](R["shr32"], a, r)),
             lambda: C["each32"](C["or32"], C["each32"](C["shl32"], lv(a), 32 - r), C["each32"](C["shr32"], lv(a), r))),
            ("each32", "v", lambda: R["each32"](R["add32"], wa, wb), lambda: C["each32"](C["add32"], lv(wa), lv(wb))),
            ("lanes", "v", lambda: R["lanes"](a[0], b[1], a[2], b[3]), lambda: C["lanes"](lv(a)[0], lv(b)[1], lv(a)[2], lv(b)[3])),
            ("words", "v", lambda: R["words"](*numbers), lambda: C["words"](*numbers)),
            ("lanes_of64", "v", lambda: R["lanes_of64"](x), lambda: C["lanes_of64"](num(x))),
            ("pick4", "v", lambda: R["pick4"](a, b, i), lambda: C["pick4"](lv(a), lv(b), i)),
            ("blend4", "v", lambda: R["blend4"](a, b, i), lambda: C["blend4"](lv(a), lv(b), i)),
            ("shuffle_bytes", "v", lambda: R["shuffle_bytes"](a, rotate), lambda: C["shuffle_bytes"](lv(a), lv(rotate))),
            ("blend_halves", "v", lambda: R["blend_halves"](a, b, whole), lambda: C["blend_halves"](lv(a), lv(b), whole)),
            ("lane32", "v", lambda: (R["lane32"](R["low32"](x)),), lambda: (C["lane32"](C["low32"](num(x))),)),
            ("spread16", "v", lambda: R["spread16"](a[0]), lambda: C["spread16"](lv(a)[0])),
            ("zeros16", "v", lambda: R["zeros16"](), lambda: C["zeros16"]()),
            ("words16", "v", lambda: R["words16"](big), lambda: C["words16"](big)),
            ("ult32", "v", lambda: R["each32"](R["ult32"], wa, wb), lambda: C["each32"](C["ult32"], lv(wa), lv(wb))),
            ("choose16", "v", lambda: R["choose16"](k, wa, wb), lambda: C["choose16"](lv(k), lv(wa), lv(wb))),
            ("in_quarters", "v", lambda: R["in_quarters"](wa, wb, *quarter), lambda: C["in_quarters"](lv(wa), lv(wb), *quarter)),
            ("quarters", "v", lambda: R["quarters"](wa, wb, i), lambda: C["quarters"](lv(wa), lv(wb), i)),
        ]
        for name, kind, on_symbols, on_numbers in probes:
            try: got = on_symbols()
            except (kterms.Fail, kfn.Fork): continue
            want = on_numbers()
            if kind == "q": mask, bits = meaning(T, got, env); ok = want & mask == bits
            elif kind == "n": ok = got == want
            elif kind == "v": ok = lv(got) == tuple(want)
            elif got is None: continue                                           # a flag of which the rule says nothing
            else: ok = bool(want) == (number_of(got[1], env) == 0 if got[0] == "zero" else number_of(got[1], env) < 0 if got[0] == "neg" else env[("q", got[1][0])] == got[1][1])
            seen[name] = seen.get(name, 0) + 1
            if name in TWO or name in ONE: key = (name, x[0]) + ((y[0],) if name in TWO else ()); FORMS[key] = FORMS.get(key, 0) + 1
            if not ok:
                bad += 1; shown += 1
                if say and shown <= 8: print(f"DIFFERS: {name}: the rule says {got}, the meaning on numbers is {want}; x = {x}, y = {y}, n = {n}")
    # (kbyte.py's machine has no frame on a 64-byte boundary: it does not answer an address rounded down)
    never = sorted(set(R) - set(seen) - {"data"}) + ["/".join(c) for c in CASES if not FORMS.get(c) and (of.BOUNDARY or c != ("and64", "a", "n"))]
    if say:
        print(f"meaning ({of.__module__}): {cases} cases; {sum(seen.values())} answers of {len(seen)} rules compared, {bad} differ from the meaning on numbers"
              + (f"; NEVER ANSWERED: {', '.join(never)}" if never else f"; every rule answered (but `data`, which has no meaning on numbers here), and each case of the rules for 64-bit registers ({len(CASES)} are listed)"))
    return bad + len(never)


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 4000
    sys.exit(1 if test(n) + test(n, of=kbyte.Machine) else 0)
