#!/usr/bin/env python3
"""What a definition means in Contract.lean (`evalSpec`) against what it means to ../kcheck/ode.py.

    python3 test_spec.py        (skipped where Lean's `lake` is not installed)

The theorem in SoundTop.lean says what a function returns by `evalSpec`. The reader's own tools (the tester
that runs a binary beside its specification, ../kcheck/refute.py) take a definition's meaning from ode.py.
Here both work out the same expressions on the same numbers and runs of bytes:

- uses of the definitions below, and of ../kcheck/programs/common/common.spec's, on random values: both
  must give the same value, or both none (an index outside its run, a difference below zero, a definition
  that comes to no end);
- random expressions over the operators Contract.lean has: wherever `evalSpec` gives a value, ode.py must
  give the same. (ode.py has values for more: it compares runs of bytes, which `evalSpec` does not.)"""
import os, random, shutil, subprocess, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "kcheck"))
sys.path.insert(0, HERE)
import ode
import statement
from statement import sexp
import built

LAKE = shutil.which("lake") or (os.path.expanduser("~/.elan/bin/lake") if os.path.exists(os.path.expanduser("~/.elan/bin/lake")) else None)
DEFINITIONS = """
def alike(a, b, at) { if at == len(a) then at else if a[at] != b[at] then at else alike(a, b, at + 1) }
def common(a, b) { alike(a, b, 0) }
def gap(x, y) { if x <= y then y - x else x - y }
def under(x, y) { x - y }
def mix(a, k) { if k < len(a) then a[k] * 3 + k else k - len(a) }
def count(a, at, b) { if at >= len(a) then 0 else (if a[at] == b then 1 else 0) + count(a, at + 1, b) }
def total(a, at) { if at == len(a) then 0 else a[at] + total(a, at + 1) }
def never(x) { 1 + never(x) }
def past(a) { a[len(a)] }
def order(x, y) { if x > y then 2 else if x >= y then 1 else 0 }
def rest(x, y) { x % y }
def share(x, y) { x / y }
def digits(x) { if x < 10 then 1 else 1 + digits(x / 10) }
def fold(a, at, s) { if at == len(a) then s else fold(a, at + 1, (s + a[at]) % 251) }
def varint(v) { if v < 128 then [v] else [128 + v % 128] ++ varint(v / 128) }
def pair(x, y) { [x, y] ++ [x + y] }
def spread(a, at) { if at == len(a) then [] else [a[at], at] ++ spread(a, at + 1) }
def odd(x) { [x - 3, x] }
"""
KINDS = {"alike": "bbn", "common": "bb", "gap": "nn", "under": "nn", "mix": "bn", "count": "bnn", "total": "bn", "never": "n", "past": "b", "order": "nn",
         "rest": "nn", "fold": "bnn", "share": "nn", "digits": "n", "varint": "n", "pair": "nn", "spread": "bn", "odd": "n"}
LISTS = ("varint", "pair", "spread", "odd")            # the definitions whose value is a list


def value(kind, rng, like=None):
    if kind == "n": return rng.choice([0, 1, rng.randrange(0, 14), rng.randrange(0, 300)])
    n = len(like) if like is not None and rng.random() < 0.8 else rng.randrange(0, 13)
    out = [rng.randrange(256) for _ in range(n)]
    if like is not None:                                             # runs that are alike for a while
        for i in range(min(n, len(like), rng.randrange(0, 13))): out[i] = like[i]
    return out


def expression(rng, names, depth):
    """A random expression as ode.py holds one: over the names (and what kind each is), the operators, the definitions."""
    numbers, runs = [n for n, k in names.items() if k == "n"], [n for n, k in names.items() if k == "b"]
    def number(d):
        pick = rng.randrange(10 if d > 0 else 3)
        if pick == 0: return ("num", rng.choice([0, 1, 2, 7, 255, 1000]))
        if pick in (1, 2): return ("name", rng.choice(numbers))
        if pick in (3, 4, 5): return ("bin", rng.choice("+-*%/"), number(d - 1), number(d - 1))
        if pick == 6: return ("ifx", truth(d - 1), number(d - 1), number(d - 1))
        if pick == 7: return ("index", ("name", rng.choice(runs)), number(d - 1))
        if pick == 8: return ("call", "len", [("name", rng.choice(runs))])
        f = rng.choice([f for f in KINDS if f != "never" and f not in LISTS])
        return ("call", f, [("name", rng.choice(runs)) if k == "b" else number(d - 1) for k in KINDS[f]])
    def truth(d): return ("bin", rng.choice(["==", "!=", "<", "<=", ">", ">="]), number(d), number(d))
    return number(depth) if rng.random() < 0.8 else truth(depth)


@unittest.skipUnless(LAKE, "Lean's lake is not installed")
class Spec(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        env = dict(os.environ, PATH=os.path.dirname(LAKE) + os.pathsep + os.environ["PATH"])
        built.built("odespec")
        cls.dir = tempfile.mkdtemp(prefix="odespec-")
        cls.spec = ode.Spec(DEFINITIONS)
        cls.defs = os.path.join(cls.dir, "defs")
        with open(cls.defs, "w") as f:
            for name, (params, body) in cls.spec.fns.items(): f.write(" ".join(["def", name] + params + ["=", sexp(body[0][1])]) + "\n")

    @classmethod
    def tearDownClass(cls): shutil.rmtree(cls.dir)

    def lean(self, cases, defs=None):
        """What evalSpec says of each (expression, {name: value}): a number, True or False, a list of bytes, or None."""
        path = os.path.join(self.dir, "cases")
        with open(path, "w") as f:
            for e, env in cases:
                f.write(" ".join(f"{n}=b:{bytes(v).hex()}" if isinstance(v, list) else f"{n}=i:{v}" for n, v in env.items()) + " | " + sexp(e) + "\n")
        out = subprocess.run([os.path.join(HERE, ".lake", "build", "bin", "odespec"), defs or self.defs, path], capture_output=True, text=True, check=True).stdout.split("\n")[:len(cases)]
        self.assertEqual(len(out), len(cases))
        def read(line):
            w = line.split()
            if w == ["none"]: return None
            self.assertIn(w[0], ("int", "bool", "bytes", "list"), line)
            if w[0] == "list": return [int(x) for x in w[1:]]
            return int(w[1]) if w[0] == "int" else w[1] == "1" if w[0] == "bool" else list(bytes.fromhex(w[1] if len(w) > 1 else ""))
        return [read(l) for l in out]

    def reference(self, spec, e, env):
        try: return spec.eval(ode.Numbers(), e, dict(env))
        except (ode.Err, ode.Fails, RecursionError, TypeError, ZeroDivisionError): return None      # (a remainder by 0 has no value)

    def test_uses_of_definitions_mean_the_same(self):
        rng = random.Random(1)
        cases = []
        for f, kinds in KINDS.items():
            for _ in range(150):
                env, like = {}, None
                for i, k in enumerate(kinds):
                    env[f"v{i}"] = value(k, rng, like)
                    if k == "b": like = env[f"v{i}"]
                cases.append((("call", f, [("name", n) for n in env]), env))
        got = self.lean(cases)
        valued = 0
        for (e, env), g in zip(cases, got):
            want = self.reference(self.spec, e, env)
            self.assertTrue(type(want) is type(g) and want == g, (e, env, want, g))
            valued += g is not None
        self.assertGreater(valued, 800)
        self.assertLess(valued, len(cases) - 150)                      # and some have none: `never`, `past`, differences below zero
        print(f"\nspec: {len(cases)} uses of {len(KINDS)} definitions: evalSpec and ode.py say the same ({valued} have a value)", file=sys.stderr)

    def test_lists_mean_the_same(self):
        """Lists written out and joined (the value of an `ensures`): evalSpec and ode.py give the same list, or
        both none (a thing of the list has no value)."""
        rng = random.Random(3)
        cases = []
        for _ in range(600):
            a = value("b", rng)
            env = {"x": rng.choice([0, 1, 127, 128, 129, rng.randrange(0, 300), rng.randrange(0, 1 << 64)]), "y": value("n", rng), "a": a}
            pick = rng.randrange(8)
            x, y = ("name", "x"), ("name", "y")
            e = [("call", "varint", [x]), ("call", "pair", [x, y]), ("call", "spread", [("name", "a"), ("num", rng.randrange(0, 4))]),
                 ("call", "odd", [y]), ("list", []), ("list", [x, ("bin", "%", x, ("num", 256)), ("bin", "/", x, ("num", 3))]),
                 ("bin", "++", ("call", "varint", [x]), ("list", [y, ("num", 7)])),
                 ("bin", "++", ("list", [("bin", "-", y, ("num", 5))]), ("call", "varint", [y]))][pick]
            cases.append((e, env))
        got = self.lean(cases)
        valued = 0
        for (e, env), g in zip(cases, got):
            want = self.reference(self.spec, e, env)
            self.assertTrue(type(want) is type(g) and want == g, (e, env, want, g))
            valued += g is not None
        self.assertGreater(valued, 400)
        self.assertLess(valued, len(cases) - 30)                       # and some have none: a difference below zero in a list, a place past a run
        print(f"\nspec: {len(cases)} lists: evalSpec and ode.py say the same ({valued} have a value)", file=sys.stderr)

    def test_wherever_evalspec_gives_a_value_ode_gives_the_same(self):
        rng = random.Random(2)
        names = {"x": "n", "y": "n", "k": "n", "a": "b", "b": "b"}
        cases = []
        for _ in range(4000):
            a = value("b", rng)
            env = {"x": value("n", rng), "y": value("n", rng), "k": rng.randrange(0, 14), "a": a, "b": value("b", rng, a)}
            cases.append((expression(rng, names, rng.randrange(1, 5)), env))
        got = self.lean(cases)
        valued, more = 0, 0
        for (e, env), g in zip(cases, got):
            want = self.reference(self.spec, e, env)
            if g is not None:
                self.assertTrue(type(want) is type(g) and want == g, (e, env, want, g)); valued += 1
            elif want is not None: more += 1
        self.assertGreater(valued, 1500)
        print(f"\nspec: {len(cases)} random expressions: {valued} have a value by evalSpec, each the same by ode.py; {more} have one by ode.py alone", file=sys.stderr)

    def test_the_shipped_definitions(self):
        with open(os.path.join(HERE, "..", "kcheck", "programs", "common", "common.spec")) as f: spec = ode.Spec(f.read())
        defs = os.path.join(self.dir, "common.defs")
        with open(defs, "w") as f:
            for name, (params, body) in spec.fns.items(): f.write(" ".join(["def", name] + params + ["=", sexp(body[0][1])]) + "\n")
        rng = random.Random(3)
        cases = []
        for _ in range(400):
            a = value("b", rng); b = value("b", rng, a)
            b = (b + [0] * len(a))[:len(a)]                              # the contract's two runs are as long as each other
            cases.append((("call", "common", [("name", "a"), ("name", "b")]), {"a": a, "b": b}))
        for (e, env), g in zip(cases, self.lean(cases, defs)):
            want = self.reference(spec, e, env)
            self.assertTrue(want is not None and type(want) is type(g) and want == g, (env, want, g))


    def test_a_sequence_means_the_definition_it_is_written_as(self):
        # the Adler-32 specification's two sequences, as statement.py writes them for Lean, against ode.py on the sequences
        folder = os.path.join(HERE, "..", "kcheck", "programs", "adler32")
        with open(os.path.join(folder, "adler32.spec")) as f: text = f.read()
        spec = ode.Spec(text)
        seqs = statement.sequences(spec)
        self.assertEqual(seqs, {"s1": 1, "s2": 1})
        defs = os.path.join(self.dir, "adler.defs")
        with open(defs, "w") as f:
            f.write("".join(l + "\n" for l in statement.statement(text, [(os.path.join(folder, "odeadler32.o"), "ode_adler32")]) if l.startswith("def ")))
        rng = random.Random(4)
        asked, cases = [], []
        for _ in range(300):
            a = [rng.choice([0, 1, 255, rng.randrange(256)]) for _ in range(rng.randrange(0, 40))]
            k = rng.randrange(0, len(a) + 3)                               # (past the last place there is no value)
            which = rng.choice(["s1", "s2", "adler32"])
            e = ("call", "adler32", [("name", "a")]) if which == "adler32" else ("index", ("call", which, [("name", "a")]), ("num", k))
            asked.append((e, {"a": a}))
        path = os.path.join(self.dir, "cases")
        with open(path, "w") as f:
            for e, env in asked: f.write(f"a=b:{bytes(env['a']).hex()} | " + sexp(e, seqs) + "\n")
        out = subprocess.run([os.path.join(HERE, ".lake", "build", "bin", "odespec"), defs, path], capture_output=True, text=True, check=True).stdout.split("\n")[:len(asked)]
        valued = 0
        for (e, env), line in zip(asked, out):
            want = self.reference(spec, e, env)
            got = None if line.split() == ["none"] else int(line.split()[1])
            self.assertEqual(want, got, (e, env))
            valued += got is not None
        self.assertGreater(valued, 200); self.assertLess(valued, len(asked))
        # Adler-32 of "Wikipedia" is 0x11E60398
        self.assertEqual(self.reference(spec, ("call", "adler32", [("name", "a")]), {"a": list(b"Wikipedia")}), 0x11E60398)
        print(f"\nspec: {len(asked)} places of Adler-32's sequences and whole sums: the definitions written for them and ode.py say the same ({valued} have a value)", file=sys.stderr)


if __name__ == "__main__":
    unittest.main()
