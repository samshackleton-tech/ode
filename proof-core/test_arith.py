#!/usr/bin/env python3
"""The arithmetic rule in Lean (Arithmetic.lean, with the theorem that its yes is right) against the
verifier's own (../kcheck/varith.py): of every proof of arithmetic the shipped files carry both say that it
adds up, and of some thousands of proofs changed in one place the two say the same, proof by proof.

    python3 test_arith.py        (skipped where Lean's `lake` is not installed)

A proof goes to the Lean program as text (ArithMain.lean says how). A step there also names the number it
divides by; here that is the greatest number dividing the step's multiples, which is what varith.py divides by."""
import glob, json, os, random, shutil, subprocess, sys, time, unittest
from math import gcd
HERE = os.path.dirname(os.path.abspath(__file__))
KCHECK = os.path.join(HERE, "..", "kcheck")
sys.path.insert(0, KCHECK)
import kdecode, kproof, varith
import built

SHIPPED = [os.path.join(KCHECK, "b3hashr.o")] + sorted(glob.glob(os.path.join(KCHECK, "programs", "*", "ode*.o")))
LAKE = shutil.which("lake") or (os.path.expanduser("~/.elan/bin/lake") if os.path.exists(os.path.expanduser("~/.elan/bin/lake")) else None)


def text(proof):
    """A proof (rows it starts from, steps) as the Lean program reads it."""
    starts, steps = proof
    names = sorted({n for c, _ in starts for n in c})
    out = [" ".join(["r", str(k)] + [str(c.get(n, 0)) for n in names]) for c, k in starts]
    rows = [(dict(c), k) for c, k in starts]
    for i, a, j, b in steps:
        d = 1
        if rows is not None and all(isinstance(x, int) for x in (i, a, j, b)) and a > 0 and b > 0 and 0 <= i < len(rows) and 0 <= j < len(rows):
            g = 0
            for n in set(rows[i][0]) | set(rows[j][0]): g = gcd(g, abs(a * rows[i][0].get(n, 0) + b * rows[j][0].get(n, 0)))
            d = max(g, 1)
            rows.append(varith.combine(rows[i], a, rows[j], b))
        else: rows = None                  # a step that is no step: whatever follows it is not reached
        out.append(f"s {i} {a} {j} {b} {d}")
    return "\n".join(out + ["q"]) + "\n"


def first_says(proof):
    starts, steps = proof
    try: return varith.refutes({varith.key(r) for r in starts}, proof)
    except Exception: return False


class ProofOrder(unittest.TestCase):
    def test_first_possible_derivation_does_not_depend_on_hash_order(self):
        # Each system has two contradictions. The first pair in input order wins,
        # including after the prover uses an equality to replace x with y.
        program = """
import json
import prove
from klin import sym
from kprove import derive
x, y = sym('x'), sym('y')
print(json.dumps([derive([x - 4, x - 5, 3 - x]),
                  prove.derive_eq([x - y, y - x, x - 4, y - 5, 3 - y])]))
"""
        expected = [
            [[[{'x': 1}, -4], [{'x': -1}, 3]], [[0, 1, 1, 1]]],
            [[[{'x': 1}, -4], [{'x': -1, 'y': 1}, 0], [{'y': -1}, 3]], [[0, 1, 1, 1], [3, 1, 2, 1]]],
        ]
        for seed in ("0", "1", "2", "3", "random"):
            with self.subTest(seed=seed):
                r = subprocess.run([sys.executable, "-c", program], cwd=HERE,
                                   env=dict(os.environ, PYTHONHASHSEED=seed),
                                   capture_output=True, text=True, timeout=10, check=True)
                self.assertEqual(json.loads(r.stdout), expected)


class Lean(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.exe = None
        if LAKE:
            env = dict(os.environ, PATH=os.path.dirname(LAKE) + os.pathsep + os.environ["PATH"])
            built.built("arith")
            cls.exe = os.path.join(HERE, ".lake", "build", "bin", "arith")

    def setUp(self):
        if self.exe is None: self.skipTest("no Lean (lake) here")

    def says(self, proofs):
        r = subprocess.run([self.exe], input="".join(text(p) for p in proofs), capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stderr[-500:])
        letters = r.stdout.split()
        self.assertEqual(len(letters), len(proofs))
        return letters

    def proofs(self):
        out = []
        for path in SHIPPED:
            carried = kproof.carried(kdecode.Elf(path).bytes_of(".ode.proof"))
            for name, blob in sorted(carried["files"].items()):
                if name.endswith(".arith.z"):
                    for proofs in varith.unpack(blob).values(): out += proofs
        return out

    def test_the_shipped_files(self):
        proofs = self.proofs()
        self.assertGreater(len(proofs), 7000)
        t = time.time()
        letters = self.says(proofs)
        took = time.time() - t
        self.assertEqual(letters.count("y"), len(proofs))
        self.assertTrue(all(first_says(p) for p in proofs))
        print(f"\n{len(proofs)} proofs of arithmetic, {sum(len(s) for _, s in proofs)} steps, {sum(len(text(p)) for p in proofs)} bytes as text: all add up, in {took:.2f} s", file=sys.stderr)

    def test_the_two_say_the_same_of_changed_proofs(self):
        rng = random.Random(20261118)
        proofs = self.proofs()
        changed, kinds = [], {}
        for starts, steps in rng.sample(proofs, 3000):
            starts = [(dict(c), k) for c, k in starts]; steps = [tuple(s) for s in steps]
            kind = rng.choice(["multiplier", "which", "number", "multiple", "left out", "another", "as it is", "zero", "name gone", "row gone"])
            if kind == "multiplier" and steps:
                s = rng.randrange(len(steps)); i, a, j, b = steps[s]; d = rng.choice([1, -1, 2, a])
                steps[s] = (i, a + d, j, b) if rng.random() < 0.5 else (i, a, j, b + d)
            elif kind == "zero" and steps:
                s = rng.randrange(len(steps)); i, a, j, b = steps[s]; steps[s] = rng.choice([(i, 0, j, b), (i, a, j, 0), (i, -a, j, b), (i, a, j, -b)])
            elif kind == "which" and steps:
                s = rng.randrange(len(steps)); i, a, j, b = steps[s]; n = len(starts) + len(steps)
                steps[s] = (rng.randrange(-1, n + 1), a, j, b) if rng.random() < 0.5 else (i, a, rng.randrange(-1, n + 1), b)
            elif kind == "number":
                r = rng.randrange(len(starts)); starts[r] = (starts[r][0], starts[r][1] + rng.choice([1, -1, 2, 255, -(1 << 64), 1 << 64]))
            elif kind == "multiple" and any(c for c, _ in starts):
                r = rng.choice([x for x in range(len(starts)) if starts[x][0]]); n = rng.choice(sorted(starts[r][0]))
                c = dict(starts[r][0]); c[n] += rng.choice([1, -1, c[n]]); starts[r] = ({k: v for k, v in c.items() if v}, starts[r][1])
            elif kind == "name gone" and any(c for c, _ in starts):
                r = rng.choice([x for x in range(len(starts)) if starts[x][0]]); c = dict(starts[r][0]); c.pop(rng.choice(sorted(c))); starts[r] = (c, starts[r][1])
            elif kind == "row gone" and len(starts) > 1: starts.pop(rng.randrange(len(starts)))
            elif kind == "left out" and steps: steps.pop(rng.randrange(len(steps)))
            elif kind == "another": steps = [tuple(s) for s in rng.choice(proofs)[1]]
            kinds[kind] = kinds.get(kind, 0) + 1
            changed.append((starts, steps))
        first = ["y" if first_says(p) else "n" for p in changed]
        lean = self.says(changed)
        differ = [k for k, (a, b) in enumerate(zip(first, lean)) if a != b]
        self.assertEqual(differ, [], f"the two differ on {len(differ)} of {len(changed)}; the first of them: {changed[differ[0]] if differ else None}")
        self.assertGreater(first.count("y"), 100); self.assertGreater(first.count("n"), 1000)
        self.assertGreater(len(kinds), 8)
        print(f"\n{len(changed)} changed proofs: {first.count('y')} still add up, {first.count('n')} do not; the two verifiers say the same of each", file=sys.stderr)

    def test_the_smallest_proofs_and_what_is_no_proof(self):
        def one(lines): return subprocess.run([self.exe], input=lines, capture_output=True, text=True).stdout.split()
        self.assertEqual(one("r -1\nq\n"), ["y"])                                        # -1 >= 0
        self.assertEqual(one("r 0 1\nr -1 -1\ns 0 1 1 1 1\nq\n"), ["y"])                 # x >= 0 and -x - 1 >= 0
        self.assertEqual(one("r -1 2\nr 1 -2\ns 0 1 0 1 4\ns 2 2 1 1 1\nq\n"), ["y"])    # 2x >= 1 rounds to x >= 1; with 1 >= 2x
        self.assertEqual(one("r -1 2\nr 2 -2\ns 0 1 0 1 4\ns 2 2 1 1 1\nq\n"), ["n"])    # 2x >= 1 and 2 >= 2x: x = 1
        self.assertEqual(one("r -1 2\nr 1 -2\ns 0 1 0 1 8\ns 2 2 1 1 1\nq\n"), ["n"])    # 8 does not divide 4
        self.assertEqual(one("r -1 2\nr 1 -2\ns 0 1 0 1 0\nq\n"), ["n"])                 # divided by nothing
        self.assertEqual(one("r -1 1\nq\n"), ["n"])                                      # a name is left
        self.assertEqual(one("q\n"), ["n"])                                              # no row
        self.assertEqual(one("r -1\nx\nq\nr -1\nq\n"), ["n", "y"])                       # a line that is none of the three
        self.assertEqual(one("r -1 0.5\nq\n"), ["n"])
        self.assertEqual(one("r 0 1\nr -1 -1\ns 0 1 1 -1 1\nq\n"), ["n"])
        self.assertEqual(one("r 0 1\nr -1 -1\ns 0 1 2 1 1\nq\n"), ["n"])                 # a row that is not there yet


if __name__ == "__main__":
    unittest.main()
