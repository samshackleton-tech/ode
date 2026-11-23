#!/usr/bin/env python3
"""Which numbers the verifier in Lean takes as negative (Core.lean, `signed`). A register holds a number
from 0 to 2^64 - 1 and the processor adds modulo 2^64, so adding 2^64 - 8 is taking 8 away. The verifier
follows an addition or a subtraction as one of whole numbers, and shows that the result lies from 0 to
2^64 - 1; for that it must take each number of the text one way: as it stands, or as the negative number
that is the same modulo 2^64. It takes a number nearer 2^64 than 2^63 (3 * 2^62 or more) as negative,
and a number below that as it stands. Both ways are sound: the result shown in range is the machine's.

Three functions of examples/far: `ode_far` adds 2^63 to a number below 2^63; `ode_near` takes 2^63 from a
number of 2^63 or more; `ode_less` takes 8 away by adding 2^64 - 8. Before this, 2^63 was taken as negative,
and the first two were not shown; the hash adds 2^63 to a message's address, and takes it from the
message's length, where the left part of a message has 2^53 chunks (test_doubling.py).

With a function or its contract changed in one place, so that what is stated is false, it is not shown,
nor does the prover find a proof; each case names what the verifier then lacks.

One true statement is refused, and is kept here as a limit: `ode_far`'s instructions also take 2^63 from
a number of 2^63 or more (the sum passes 2^64 and comes round), and of that contract the function is not
shown, since 2^63 is taken as it stands. (A way to follow both: the proof says which way a number is to
be taken. Not built.)

The three contracts have no `trace depends on` line: each function runs the same instructions whatever x
is, and touches no memory except its return address. A returned number computed from x does not require
naming x in `trace depends on`; a caller that branches on the returned number must name x (or the returned
expression) in its own `trace depends on` line.

    python3 test_far.py        (skipped where Lean's `lake` is not installed)"""
import os, shutil, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "lang"))
import lean_verify, odec, prove
import built
FAR = os.path.join(HERE, "examples", "far")
LAKE = lean_verify.LAKE

RANGE = "need entail"                 # the sum or difference is to be shown from 0 to 2^64 - 1, and the prover has no proof of it
RETURNS = "need entail"               # what is returned is to be shown the contract's number, and it is not
# function -> (what is changed, the source as it is, the source changed, what the verifier then lacks)
SOURCES = {
    "far": [("2^62 is added", "  mov rax, 1\n  shl rax, 63\n", "  mov rax, 1\n  shl rax, 62\n", RETURNS),
            ("the number is added twice", "  add rax, rdi\n", "  add rax, rdi\n  add rax, rdi\n", RANGE)],
    "near": [("2^62 is taken away", "  mov rcx, 1\n  shl rcx, 63\n", "  mov rcx, 1\n  shl rcx, 62\n", RETURNS),
             ("the number is taken from 2^63", "  mov rax, rdi\n  sub rax, rcx\n", "  mov rax, rcx\n  sub rax, rdi\n", RANGE)],
    "less": [("9 is taken away", "  add rax, -8\n", "  add rax, -9\n", RANGE),
             ("8 is added", "  add rax, -8\n", "  add rax, 8\n", RANGE)],
}
# function -> (what is changed, the specification as it is, the specification changed, what the verifier then lacks)
SPECS = {
    "far": [("the number may be 2^63: the sum is then 2^64, and the register holds 0", "x <= 9223372036854775807", "x <= 9223372036854775808", RANGE),
            ("the contract adds one more", "returns x + 9223372036854775808", "returns x + 9223372036854775809", RETURNS)],
    "near": [("the number may be one less than 2^63", "x >= 9223372036854775808", "x >= 9223372036854775807", RANGE),
             ("the contract takes one less away", "returns x - 9223372036854775808", "returns x - 9223372036854775807", RETURNS)],
    "less": [("the number may be 7", "x >= 8", "x >= 7", RANGE),
             ("the contract takes 9 away", "returns x - 8", "returns x - 9", RETURNS)],
}
# The limit: `ode_far`'s contract changed in two places to one its instructions also meet.
LIMIT = [("    requires x <= 9223372036854775807\n    returns x + 9223372036854775808\n",
          "    requires x >= 9223372036854775808\n    returns x - 9223372036854775808\n")]


@unittest.skipUnless(LAKE, "Lean's lake is not installed")
class Far(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.dir = tempfile.mkdtemp(prefix="odefar-")
        with open(os.path.join(FAR, "far.spec")) as f: cls.spec = f.read()
        with open(os.path.join(FAR, "far.ode")) as f: cls.source = f.read()

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.dir)

    def path(self, name): return os.path.join(self.dir, name)
    def obj(self, fn): return os.path.join(FAR, "ode" + fn + ".o")
    def kept(self, fn): return os.path.join(HERE, "proofs", "ode_" + fn + ".proof")

    def found(self, spec, obj, fn, name="try"):
        """The prover's numbers; or, where it finds no proof, the verifier's last word."""
        try: return prove.prove(spec, [(obj, "ode_" + fn, "")], self.path(name + ".statement"), self.path(name + ".proof"))
        except SystemExit as e:
            said = str(e)
            self.assertTrue(said.startswith("prove: no proof of ode_" + fn), said[:200])
            return said.split("\n", 1)[1]

    def test_the_examples_are_made_from_their_source(self):
        for fn in ("far", "near", "less"):
            odec.build(os.path.join(FAR, "far.ode"), fn, self.path("made.o"))
            with open(self.path("made.o"), "rb") as f, open(self.obj(fn), "rb") as g: self.assertEqual(f.read(), g.read(), fn)

    def test_shown_and_the_kept_proofs_are_what_the_prover_finds(self):
        for fn in ("far", "near", "less"):
            with self.subTest(fn=fn):
                numbers = self.found(self.spec, self.obj(fn), fn, fn)
                self.assertEqual(list(numbers), ["ode_" + fn])
                self.assertEqual(lean_verify.verify(self.spec, [(self.obj(fn), "ode_" + fn)], self.kept(fn)), (True, "shown"))
                with open(self.kept(fn)) as f, open(self.path(fn + ".proof")) as g: self.assertEqual(f.read(), g.read())
        with open(self.path("less.statement")) as f: self.assertIn(".add 64 (.reg .rax) (.imm 0xFFFFFFFFFFFFFFF8)", f.read())      # 2^64 - 8 is what is added

    def test_a_function_changed_in_one_place(self):
        for fn, cases in SOURCES.items():
            for what, old, new, why in cases:
                with self.subTest(fn=fn, what=what):
                    self.assertEqual(self.source.count(old), 1)
                    with open(self.path("changed.ode"), "w") as f: f.write(self.source.replace(old, new))
                    odec.build(self.path("changed.ode"), fn, self.path("changed.o"))
                    self.assertFalse(lean_verify.verify(self.spec, [(self.path("changed.o"), "ode_" + fn)], self.kept(fn))[0], what)
                    last = self.found(self.spec, self.path("changed.o"), fn)
                    self.assertIsInstance(last, str, what)                  # no proof is found
                    self.assertIn(why, last, what)

    def test_a_contract_changed_in_one_place(self):
        for fn, cases in SPECS.items():
            for what, old, new, why in cases:
                with self.subTest(fn=fn, what=what):
                    self.assertEqual(self.spec.count(old), 1)
                    spec = self.spec.replace(old, new)
                    self.assertFalse(lean_verify.verify(spec, [(self.obj(fn), "ode_" + fn)], self.kept(fn))[0], what)
                    last = self.found(spec, self.obj(fn), fn)
                    self.assertIsInstance(last, str, what)
                    self.assertIn(why, last, what)

    def test_a_limit_a_true_statement_that_is_refused(self):
        """`ode_far`'s instructions add 2^63. For a number of 2^63 or more the sum passes 2^64, and the
        register then holds the number less 2^63: so the function also meets `requires x >= 2^63`,
        `returns x - 2^63`. The verifier takes 2^63 as it stands, asks that the sum be below 2^64, and
        does not show that contract. A LIMIT, kept here so that it is seen."""
        spec = self.spec
        for old, new in LIMIT:
            self.assertEqual(spec.count(old), 1)
            spec = spec.replace(old, new)
        last = self.found(spec, self.obj("far"), "far")
        self.assertIsInstance(last, str)
        self.assertIn(RANGE, last)

    def test_no_trace_line_is_needed_for_a_returned_number(self):
        """Each function runs the same instructions whatever x is, and touches no memory except its return
        address: its trace depends on nothing. Its contract has no `trace depends on` line and is shown."""
        self.assertFalse(any(ln.strip().startswith("trace depends on") for ln in self.spec.splitlines()))
        for fn in ("far", "near", "less"):
            with self.subTest(fn=fn):
                self.assertEqual(lean_verify.verify(self.spec, [(self.obj(fn), "ode_" + fn)], self.kept(fn)), (True, "shown"))


if __name__ == "__main__":
    unittest.main()
