#!/usr/bin/env python3
"""The lowest byte of a register has a mark of its own: `ode_rounds` (examples/lowbyte) keeps a count of
three in the lowest byte of `rax` while the other bytes of `rax` hold a byte of the hidden run `m`:

    movzx eax, byte ptr [rdi + 0]      a hidden byte
    shl rax, 8                         now the second byte of rax
    mov al, 3                          the lowest byte: a count
  @again:
    dec al
    jne @again                         a jump decided by the lowest byte alone

Its contract has no `trace` line: which instructions run may depend on no byte of `m`, and not on the
number `n`. They do not: the jump is decided by the count of three. The hash's two one-block kernels count
their seven rounds in this way.

The formal model (Machine.lean) marks what may depend on something hidden. A general register has two
marks there: one for the register, and one for its lowest byte, looked at only where the register is
marked. `mov al, 3` leaves the register marked and its lowest byte not marked; `dec al` and the flag it
sets are worked out of the lowest byte alone. Before this, the model had one mark a register, and the
verifier refused this function at the jump: a true statement refused.

    python3 test_lowbyte.py        (needs Lean's `lake`; the tests are skipped where it is not installed)

The function and its contract are shown, with the function's name alone as the proof. With the function
changed in one place so that the jump does depend on the hidden byte, nothing is shown, and each case
names what the verifier refuses. Changes that keep the statement true are shown. One true statement is
refused and kept as a limit.

A number given is hidden as a run's bytes are, unless `trace depends on` names it: with the function
changed so that it reads the run's last byte, at an address made of `n`, nothing is shown; with `n` named,
the same function is shown."""
import os, shutil, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, "..", "lang"))
import built, lean_verify, odec, prove

LOWBYTE = os.path.join(HERE, "examples", "lowbyte")
NAME = "ode_rounds"
LAKE = lean_verify.LAKE
# Why the verifier refuses.
JUMP = "refused: a jump on a flag that may depend on values kept out of the trace: which instructions run would depend on them"
ADDRESS = "refused: an address may depend on values kept out of the trace: what can be observed of the run would depend on them"
LOOP = "\n  jne @again\n"
# Changed so that which instructions run depends on the hidden byte, or which address is read on the hidden
# count: (what, the source as it is, changed, what the verifier says)
SOURCES = [
    ("the count is the hidden byte itself", "  shl rax, 8\n  mov al, 3\n", "", JUMP),
    ("the hidden byte is shifted back into the lowest byte", "  mov al, 3\n", "  mov al, 3\n  shr rax, 8\n", JUMP),
    # (one instruction more is run where the hidden byte is not 0)
    ("a jump on the whole register after the loop", LOOP, LOOP + "  cmp rax, 256\n  jb @skip\n  mov rcx, rcx\n@skip:\n", JUMP),
    # (the address read depends on the count of the run's bytes, a number the contract hides)
    ("the last byte of the run is read, at an address made of its count", "  movzx eax, byte ptr [rdi + 0]\n",
     "  mov rcx, rsi\n  sub rcx, 1\n  add rcx, rdi\n  movzx eax, byte ptr [rcx + 0]\n", ADDRESS),
    # (r10 holds no argument: it holds what a caller left there, of which the contract says nothing)
    ("a jump on a register that holds no argument", "  mov al, 3\n", "  mov al, 3\n  cmp r10, 0\n  je @left\n  mov rcx, rcx\n@left:\n", JUMP),
]
# Changed and still true: (what, the source as it is, changed)
STILL_TRUE = [
    ("the count is five", "  mov al, 3\n", "  mov al, 5\n"),
    ("the lowest byte is copied to another register, and a jump is decided there", "  mov al, 3\n",
     "  mov al, 3\n  movzx ecx, al\n  cmp rcx, 4\n  jb @skip\n  mov rcx, rcx\n@skip:\n"),
]
# A changed function that is still true and is refused: the register is doubled, so its lowest byte is 6
# whatever the other bytes are. The verifier has the whole register as set from something hidden.
DOUBLED = ("  mov al, 3\n", "  mov al, 3\n  add rax, rax\n")
# Contracts changed so that what is stated is false: (what, the text as it is, changed, what the verifier lacks:
# an inequality that the prover has no proof of)
CONTRACTS = [
    ("1 is said to be returned", "returns 0", "returns 1", "need entail"),
    ("the run may be empty: the byte read may be none of its bytes", "    requires n >= 1\n", "", "need entail"),
]


@unittest.skipUnless(LAKE, "Lean's lake is not installed")
class LowByte(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.dir = tempfile.mkdtemp(prefix="odelowbyte-")
        cls.obj = os.path.join(LOWBYTE, "odelowbyte.o")
        with open(os.path.join(LOWBYTE, "lowbyte.contract")) as f: cls.spec = f.read()
        with open(os.path.join(LOWBYTE, "lowbyte.ode")) as f: cls.source = f.read()
        cls.kept = os.path.join(HERE, "proofs", NAME + ".proof")

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.dir)

    def path(self, name): return os.path.join(self.dir, name)

    def found(self, spec, obj, name="try"):
        """The prover's numbers; or, where it finds no proof, the verifier's last word."""
        try: return prove.prove(spec, [(obj, NAME, "")], self.path(name + ".statement"), self.path(name + ".proof"))
        except SystemExit as e:
            said = str(e)
            self.assertTrue(said.startswith("prove: no proof of " + NAME), said[:200])
            return said.split("\n", 1)[1]

    def changed(self, old, new, source=None):
        """The object file of the source with `old`, which stands in it once, replaced by `new`."""
        source = self.source if source is None else source
        self.assertEqual(source.count(old), 1, old)
        with open(self.path("changed.ode"), "w") as f: f.write(source.replace(old, new))
        odec.build(self.path("changed.ode"), "rounds", self.path("changed.o"))
        return self.path("changed.o")

    def test_the_example_is_made_from_its_source(self):
        odec.build(os.path.join(LOWBYTE, "lowbyte.ode"), "rounds", self.path("made.o"))
        with open(self.path("made.o"), "rb") as f, open(self.obj, "rb") as g: self.assertEqual(f.read(), g.read())

    def test_shown_and_the_kept_proof_is_what_the_prover_finds(self):
        self.assertEqual(list(self.found(self.spec, self.obj, "shown")), [NAME])
        self.assertEqual(lean_verify.verify(self.spec, [(self.obj, NAME)], self.kept), (True, "shown"))
        with open(self.kept) as f, open(self.path("shown.proof")) as g: self.assertEqual(f.read(), g.read())
        with open(self.path("shown.statement")) as f: rows = f.read()
        self.assertIn(".mov 8 (.reg .rax) (.imm 0x3)", rows)            # the rows this is about
        self.assertIn(".decb .rax", rows)
        self.assertIn("hidden m", rows)                                 # the run is hidden, and the count: no `trace` line
        self.assertIn("hidden n", rows)

    def test_a_function_changed_so_that_the_hidden_byte_shows(self):
        for what, old, new, why in SOURCES:
            with self.subTest(what=what):
                obj = self.changed(old, new)
                self.assertFalse(lean_verify.verify(self.spec, [(obj, NAME)], self.kept)[0], what)
                last = self.found(self.spec, obj)
                self.assertIsInstance(last, str, what)                  # no proof is found
                self.assertIn(why, last, what)

    def test_the_same_jump_is_shown_where_the_contract_lets_the_trace_depend_on_the_run(self):
        # The third changed function, with a contract that says `trace depends on m`: now a true statement.
        what, old, new, _ = SOURCES[2]
        obj = self.changed(old, new)
        spec = self.spec.replace("    returns 0\n", "    returns 0\n    trace depends on m\n")
        self.assertNotEqual(spec, self.spec)
        self.assertEqual(list(self.found(spec, obj)), [NAME], what)

    def test_the_same_read_is_shown_where_the_contract_lets_the_trace_depend_on_the_count(self):
        # The fourth changed function, with a contract that says `trace depends on n`: now a true statement.
        what, old, new, _ = SOURCES[3]
        obj = self.changed(old, new)
        spec = self.spec.replace("    returns 0\n", "    returns 0\n    trace depends on n\n")
        self.assertNotEqual(spec, self.spec)
        self.assertEqual(list(self.found(spec, obj)), [NAME], what)

    def test_a_changed_function_that_is_still_true_is_shown(self):
        for what, old, new in STILL_TRUE:
            with self.subTest(what=what):
                self.assertEqual(list(self.found(self.spec, self.changed(old, new))), [NAME], what)

    def test_a_contract_changed_in_one_place(self):
        for what, old, new, why in CONTRACTS:
            with self.subTest(what=what):
                self.assertEqual(self.spec.count(old), 1)
                spec = self.spec.replace(old, new)
                self.assertFalse(lean_verify.verify(spec, [(self.obj, NAME)], self.kept)[0], what)
                last = self.found(spec, self.obj)
                self.assertIsInstance(last, str, what)
                self.assertIn(why, last, what)

    def test_limits_a_true_statement_is_refused(self):
        last = self.found(self.spec, self.changed(*DOUBLED))
        self.assertIsInstance(last, str)
        self.assertIn(JUMP, last)


if __name__ == "__main__":
    unittest.main()
