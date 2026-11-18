#!/usr/bin/env python3
"""The low half and the low byte of a register, in the verifier in Lean (Core.lean, `symPrim1`): `ode_low` of
examples/low adds the low byte of one number to the low half of another, by the rows `movzx eax, dil` and
`mov ecx, esi`. The verifier takes each as the remainder of the one division of that number it knows of, so
the code's low byte and the specification's `a % 256` are one unknown.

With the function or its contract changed in one place it does not say `shown`, nor does the prover find a
proof; each case names what the verifier then lacks. With a line of the proof left out it does not say
`shown`.

    python3 test_low.py        (skipped where Lean's `lake` is not installed)"""
import os, shutil, subprocess, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "lang"))
import lean_verify, odec, prove
LOW = os.path.join(HERE, "examples", "low")
LAKE = lean_verify.LAKE

RANGE = "need entail"                 # the sum is to be shown below 2^64, and the prover has no proof of it
RETURNS = "need spec"                 # what is returned is to be shown the contract's number, and nothing the proof can say shows it
# (what is changed, the source as it is, the source changed, what the verifier then lacks)
SOURCES = [
    ("the whole second number is added", "  mov ecx, esi\n", "  mov rcx, rsi\n", RANGE),
    ("the low byte of the second number is taken", "  movzx eax, dil\n", "  movzx eax, sil\n", RETURNS),
    ("the low half of the first number is taken", "  mov ecx, esi\n", "  mov ecx, edi\n", RETURNS),
    ("the low half is taken where the low byte is to be", "  movzx eax, dil\n", "  mov eax, edi\n", RETURNS),
]
# (what is changed, the specification as it is, the specification changed, what the verifier then lacks)
SPECS = [
    ("the contract takes the low seven bits", "a % 256", "a % 128", RETURNS),
    ("the contract takes the low 31 bits", "b % 4294967296", "b % 2147483648", RETURNS),
    ("the contract takes the whole second number", "b % 4294967296", "b", RETURNS),
    ("the contract takes the low byte of the second number", "a % 256", "b % 256", RETURNS),
]


@unittest.skipUnless(LAKE, "Lean's lake is not installed")
class Low(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        env = dict(os.environ, PATH=os.path.dirname(LAKE) + os.pathsep + os.environ["PATH"])
        r = subprocess.run([LAKE, "build", "odeverify"], cwd=HERE, capture_output=True, text=True, env=env)
        if r.returncode != 0: raise AssertionError("lake build failed:\n" + r.stdout[-2000:] + r.stderr[-2000:])
        cls.dir = tempfile.mkdtemp(prefix="odelow-")
        cls.obj = os.path.join(LOW, "odelow.o")
        with open(os.path.join(LOW, "low.spec")) as f: cls.spec = f.read()
        with open(os.path.join(LOW, "low.ode")) as f: cls.source = f.read()
        cls.kept = os.path.join(HERE, "proofs", "ode_low.proof")

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.dir)

    def path(self, name): return os.path.join(self.dir, name)

    def found(self, spec, obj, name="try"):
        """The prover's numbers; or, where it finds no proof, the verifier's last word."""
        try: return prove.prove(spec, [(obj, "ode_low", "")], self.path(name + ".statement"), self.path(name + ".proof"))
        except SystemExit as e:
            said = str(e)
            self.assertTrue(said.startswith("prove: no proof of ode_low"), said[:200])
            return said.split("\n", 1)[1]

    def test_the_example_is_made_from_its_source(self):
        odec.build(os.path.join(LOW, "low.ode"), "low", self.path("made.o"))
        with open(self.path("made.o"), "rb") as f, open(self.obj, "rb") as g: self.assertEqual(f.read(), g.read())

    def test_shown_and_the_kept_proof_is_what_the_prover_finds(self):
        numbers = self.found(self.spec, self.obj, "shown")
        self.assertEqual(list(numbers), ["ode_low"])
        self.assertEqual(lean_verify.verify(self.spec, [(self.obj, "ode_low")], self.kept), (True, "shown"))
        with open(self.kept) as f, open(self.path("shown.proof")) as g: self.assertEqual(f.read(), g.read())
        with open(self.path("shown.statement")) as f: rows = f.read()
        self.assertIn(".movzx8 .rax (.reg .rdi)", rows)                 # the two rows this is about
        self.assertIn(".mov 32 (.reg .rcx) (.reg .rsi)", rows)

    def test_the_function_changed_in_one_place(self):
        for what, old, new, why in SOURCES:
            with self.subTest(what=what):
                self.assertEqual(self.source.count(old), 1)
                with open(self.path("changed.ode"), "w") as f: f.write(self.source.replace(old, new))
                odec.build(self.path("changed.ode"), "low", self.path("changed.o"))
                self.assertFalse(lean_verify.verify(self.spec, [(self.path("changed.o"), "ode_low")], self.kept)[0], what)
                last = self.found(self.spec, self.path("changed.o"))
                self.assertIsInstance(last, str, what)                  # no proof is found
                self.assertIn(why, last, what)

    def test_the_contract_changed_in_one_place(self):
        for what, old, new, why in SPECS:
            with self.subTest(what=what):
                self.assertEqual(self.spec.count(old), 1)
                spec = self.spec.replace(old, new)
                self.assertFalse(lean_verify.verify(spec, [(self.obj, "ode_low")], self.kept)[0], what)
                last = self.found(spec, self.obj)
                self.assertIsInstance(last, str, what)
                self.assertIn(why, last, what)

    def test_a_line_of_the_proof_left_out(self):
        with open(self.kept) as f: lines = f.read().splitlines()
        for k in range(1, len(lines)):                                  # (the first line names the function)
            with self.subTest(line=k):
                with open(self.path("less.proof"), "w") as f: f.write("".join(l + "\n" for l in lines[:k] + lines[k + 1:]))
                self.assertFalse(lean_verify.verify(self.spec, [(self.obj, "ode_low")], self.path("less.proof"))[0], lines[k])


if __name__ == "__main__":
    unittest.main()
