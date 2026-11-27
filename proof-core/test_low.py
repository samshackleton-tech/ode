#!/usr/bin/env python3
"""The low half and the low byte of a register, in the verifier in Lean (Core.lean, `symPrim1`): `ode_low` of
examples/low adds the low byte of one number to the low half of another, by the rows `movzx eax, dil` and
`mov ecx, esi`. The verifier takes each as the remainder of the one division of that number it knows of, so
the code's low byte and the specification's `a % 256` are one unknown. And a quotient in a specification
(`sdiv`): `ode_eighth` of the same folder shifts a number right by three, against `a / 8`.

With the function or its contract changed in one place it does not say `shown`, nor does the prover find a
proof; each case names what the verifier then lacks. With a line of the proof left out it does not say
`shown`.

    python3 test_low.py        (skipped where Lean's `lake` is not installed)"""
import os, shutil, subprocess, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "lang"))
import lean_verify, odec, prove
import built
LOW = os.path.join(HERE, "examples", "low")
LAKE = lean_verify.LAKE

RANGE = "need entail"                 # the sum is to be shown below 2^64, and the prover has no proof of it
RETURNS = "need entail"               # what is returned is to be shown the contract's number, and the prover has no proof of it
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
# the same of ode_eighth
EIGHTH_SOURCES = [
    ("the shift is by two", "  shr rax, 3\n", "  shr rax, 2\n", RETURNS),
    ("the shift is by four", "  shr rax, 3\n", "  shr rax, 4\n", RETURNS),
    ("nothing is shifted", "  shr rax, 3\n", "", RETURNS),
]
EIGHTH_SPECS = [
    ("the contract divides by nine", "a / 8", "a / 9", RETURNS),
    ("the contract divides by four", "a / 8", "a / 4", RETURNS),
    ("the contract takes the remainder", "a / 8", "a % 8", RETURNS),
]


@unittest.skipUnless(LAKE, "Lean's lake is not installed")
class Low(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        env = dict(os.environ, PATH=os.path.dirname(LAKE) + os.pathsep + os.environ["PATH"])
        built.built("odeverify")
        cls.dir = tempfile.mkdtemp(prefix="odelow-")
        cls.obj = os.path.join(LOW, "odelow.o")
        with open(os.path.join(LOW, "low.spec")) as f: cls.spec = f.read()
        with open(os.path.join(LOW, "low.ode")) as f: cls.source = f.read()
        cls.kept = os.path.join(HERE, "proofs", "ode_low.proof")
        cls.eighth, cls.kept_eighth = os.path.join(LOW, "odeeighth.o"), os.path.join(HERE, "proofs", "ode_eighth.proof")

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.dir)

    def path(self, name): return os.path.join(self.dir, name)

    def found(self, spec, obj, name="try", symbol="ode_low"):
        """The prover's numbers; or, where it finds no proof, the verifier's last word."""
        try: return prove.prove(spec, [(obj, symbol, "")], self.path(name + ".statement"), self.path(name + ".proof"))
        except SystemExit as e:
            said = str(e)
            self.assertTrue(said.startswith("prove: no proof of " + symbol), said[:200])
            return said.split("\n", 1)[1]

    def test_the_examples_are_made_from_their_source(self):
        for fn, obj in (("low", self.obj), ("eighth", self.eighth)):
            odec.build(os.path.join(LOW, "low.ode"), fn, self.path("made.o"))
            with open(self.path("made.o"), "rb") as f, open(obj, "rb") as g: self.assertEqual(f.read(), g.read(), fn)

    def test_shown_and_the_kept_proof_is_what_the_prover_finds(self):
        numbers = self.found(self.spec, self.obj, "shown")
        self.assertEqual(list(numbers), ["ode_low"])
        self.assertEqual(lean_verify.verify(self.spec, [(self.obj, "ode_low")], self.kept), (True, "shown"))
        with open(self.kept) as f, open(self.path("shown.proof")) as g: self.assertEqual(f.read(), g.read())
        with open(self.path("shown.statement")) as f: rows = f.read()
        self.assertIn(".movzx8 .rax (.reg .rdi)", rows)                 # the two rows this is about
        self.assertIn(".mov 32 (.reg .rcx) (.reg .rsi)", rows)

    def test_a_function_changed_in_one_place(self):
        for fn, kept, cases in (("low", self.kept, SOURCES), ("eighth", self.kept_eighth, EIGHTH_SOURCES)):
            for what, old, new, why in cases:
                with self.subTest(what=what):
                    self.assertEqual(self.source.count(old), 1)
                    with open(self.path("changed.ode"), "w") as f: f.write(self.source.replace(old, new))
                    odec.build(self.path("changed.ode"), fn, self.path("changed.o"))
                    self.assertFalse(lean_verify.verify(self.spec, [(self.path("changed.o"), "ode_" + fn)], kept)[0], what)
                    last = self.found(self.spec, self.path("changed.o"), symbol="ode_" + fn)
                    self.assertIsInstance(last, str, what)                  # no proof is found
                    self.assertIn(why, last, what)

    def test_a_contract_changed_in_one_place(self):
        for fn, obj, kept, cases in (("low", self.obj, self.kept, SPECS), ("eighth", self.eighth, self.kept_eighth, EIGHTH_SPECS)):
            for what, old, new, why in cases:
                with self.subTest(what=what):
                    self.assertEqual(self.spec.count(old), 1)
                    spec = self.spec.replace(old, new)
                    self.assertFalse(lean_verify.verify(spec, [(obj, "ode_" + fn)], kept)[0], what)
                    last = self.found(spec, obj, symbol="ode_" + fn)
                    self.assertIsInstance(last, str, what)
                    self.assertIn(why, last, what)

    def test_the_quotient_is_shown_and_the_kept_proof_is_what_the_prover_finds(self):
        numbers = self.found(self.spec, self.eighth, "eighth", symbol="ode_eighth")
        self.assertEqual(list(numbers), ["ode_eighth"])
        self.assertEqual(lean_verify.verify(self.spec, [(self.eighth, "ode_eighth")], self.kept_eighth), (True, "shown"))
        with open(self.kept_eighth) as f, open(self.path("eighth.proof")) as g: self.assertEqual(f.read(), g.read())
        with open(self.path("eighth.statement")) as f: self.assertIn("(bin / (name a) (num 8))", f.read())

    def test_a_line_of_a_proof_left_out(self):
        for obj, symbol, kept in ((self.obj, "ode_low", self.kept), (self.eighth, "ode_eighth", self.kept_eighth)):
            with open(kept) as f: lines = f.read().splitlines()
            for k in range(1, len(lines)):                                  # (the first line names the function)
                with self.subTest(symbol=symbol, line=k):
                    with open(self.path("less.proof"), "w") as f: f.write("".join(l + "\n" for l in lines[:k] + lines[k + 1:]))
                    self.assertFalse(lean_verify.verify(self.spec, [(obj, symbol)], self.path("less.proof"))[0], lines[k])


if __name__ == "__main__":
    unittest.main()
