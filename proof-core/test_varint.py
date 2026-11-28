#!/usr/bin/env python3
"""Memory written for the caller, in the verifier in Lean: `ode_varint` of ../kcheck/programs/varint writes a
number's bytes into the ten bytes its caller gives it, and the verifier shows

    contract ode_varint(out: 10 bytes, v: number) { returns r   ensures out[0 .. r] = varint(v)   stack 24 }

by three rules: a byte stored into a run given to write (Core.lean, the `out` case of a store, `keepWrote`),
a list of the specification thing by thing (`slist`), and an `ensures` at the return (`symEnsure`). The
function has no place: its loop turns ten times at most, each turn its own path.

With the function or its contract changed in one place it does not say `shown`, nor does the prover find a
proof; each case names what the verifier then lacks. With a line of the proof left out or changed it does
not say `shown`. And statement.py, which writes what is to be shown, refuses a contract that writes one run
and reads another without asking its caller that they do not overlap.

    python3 test_varint.py        (skipped where Lean's `lake` is not installed)"""
import os, shutil, subprocess, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "lang"))
import lean_verify, odec, prove, statement
import built
VARINT = os.path.join(HERE, "..", "kcheck", "programs", "varint")
LAKE = lean_verify.LAKE
SYMBOL = "ode_varint"
STATEMENT = ("fn", "i", "arg", "returns", "result", "ensures", "stack", "def")    # the kinds of line that say what is to be shown

WRITTEN = "a byte of the run is not known written"      # an `ensures` speaks of a place nothing was stored at
ENTAIL = "need entail"                                  # something is to be shown of numbers, and the prover has no proof of it
BELOW = "need below"                                    # the specification asks which of two numbers is less, and the path does not say
READ = "a read of a run given only to write"
# (what is changed, the source as it is, the source changed, what the verifier then lacks)
SOURCES = [
    ("the last byte is not written", "  add rcx, r12\n  mov byte ptr [rcx], al\n  mov rax, r12\n", "  add rcx, r12\n  mov rax, r12\n", WRITTEN),
    ("a byte of the loop is written one place on", "  add rcx, r12\n  mov byte ptr [rcx], al\n  // v = v >> 7",
     "  add rcx, r12\n  add rcx, 1\n  mov byte ptr [rcx], al\n  // v = v >> 7", WRITTEN),
    ("127 is added where 128 is to be", "  mov rax, 128\n", "  mov rax, 127\n", ENTAIL),
    ("the count returned is one more", "  mov rax, r12\n  add rax, 1\n  pop r12", "  mov rax, r12\n  add rax, 2\n  pop r12", ENTAIL),
    ("the number is shifted by eight", "  shr rax, 7\n", "  shr rax, 8\n", ENTAIL),
    ("the low eight bits are taken", "  and rcx, 127\n", "  and rcx, 255\n", ENTAIL),
    ("the loop goes on while 128 < v", "  mov rax, 127\n", "  mov rax, 128\n", ENTAIL),
    ("what was written is read", "  mov byte ptr [rcx], al\n  mov rax, r12\n", "  mov byte ptr [rcx], al\n  movzx eax, byte ptr [rcx]\n  mov rax, r12\n", READ),
]
# (what is changed, the specification as it is, the specification changed, what the verifier then lacks)
SPECS = [
    ("the run is nine bytes", "out: 10 bytes", "out: 9 bytes", ENTAIL),              # (the tenth byte is then stored outside the run)
    ("the specification divides by 127", "varint(v / 128)", "varint(v / 127)", ENTAIL),
    ("the specification adds 127", "[128 + v % 128]", "[127 + v % 128]", ENTAIL),
    ("the specification ends below 127", "if v < 128", "if v < 127", ENTAIL),
    ("the bytes are said from place one", "out[0 .. r]", "out[1 .. r]", ENTAIL),
    ("one byte less is said", "out[0 .. r]", "out[0 .. r - 1]", ENTAIL),
    ("the stack is sixteen bytes", "stack 24", "stack 16", ENTAIL),                  # (the third push is not shown to stay in memory)
]


@unittest.skipUnless(LAKE, "Lean's lake is not installed")
class Varint(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.dir = tempfile.mkdtemp(prefix="odevarint-")
        cls.obj = os.path.join(VARINT, "odevarint.o")
        with open(os.path.join(VARINT, "varint.spec")) as f: cls.spec = f.read()
        with open(os.path.join(VARINT, "varint.ode")) as f: cls.source = f.read()
        cls.kept = os.path.join(HERE, "proofs", SYMBOL + ".proof")

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.dir)

    def path(self, name): return os.path.join(self.dir, name)

    def found(self, spec, obj, name="try"):
        """The prover's numbers; or, where it finds no proof, the verifier's last word."""
        try: return prove.prove(spec, [(obj, SYMBOL, "")], self.path(name + ".statement"), self.path(name + ".proof"))
        except SystemExit as e:
            said = str(e)
            self.assertTrue(said.startswith("prove: no proof of " + SYMBOL), said[:200])
            return said.split("\n", 1)[1]

    def test_shown_and_the_kept_proof_is_what_the_prover_finds(self):
        numbers = self.found(self.spec, self.obj, "shown")
        self.assertEqual(list(numbers), [SYMBOL])
        self.assertEqual(lean_verify.verify(self.spec, [(self.obj, SYMBOL)], self.kept), (True, "shown"))
        with open(self.kept) as f, open(self.path("shown.proof")) as g: self.assertEqual(f.read(), g.read())
        with open(self.path("shown.statement")) as f: lines = f.read().splitlines()
        # what is to be shown says the run is written, names the number returned, and has the `ensures`
        self.assertIn("arg out out 10", lines)
        self.assertIn("result r", lines)
        self.assertIn("ensures out (num 0) (name r) (call varint (name v))", lines)
        self.assertIn("i 58 60 .mov 8 (.mem .rcx 0x0) (.reg .rax)", lines)             # the store this is about
        self.assertFalse([l for l in lines if l.startswith("returns")])

    def test_a_function_changed_in_one_place(self):
        for what, old, new, why in SOURCES:
            with self.subTest(what=what):
                self.assertEqual(self.source.count(old), 1)
                with open(self.path("changed.ode"), "w") as f: f.write(self.source.replace(old, new))
                odec.build(self.path("changed.ode"), "varint", self.path("changed.o"))
                self.assertFalse(lean_verify.verify(self.spec, [(self.path("changed.o"), SYMBOL)], self.kept)[0], what)
                last = self.found(self.spec, self.path("changed.o"))
                self.assertIsInstance(last, str, what)                      # no proof is found
                self.assertIn(why, last.split("\n")[0], what)

    def test_a_contract_changed_in_one_place(self):
        for what, old, new, why in SPECS:
            with self.subTest(what=what):
                self.assertEqual(self.spec.count(old), 1)
                spec = self.spec.replace(old, new)
                self.assertFalse(lean_verify.verify(spec, [(self.obj, SYMBOL)], self.kept)[0], what)
                last = self.found(spec, self.obj)
                self.assertIsInstance(last, str, what)
                self.assertIn(why, last.split("\n")[0], what)

    def test_the_proof_changed(self):
        with open(self.kept) as f: proof = f.read().splitlines()
        with open(self.path("s.statement"), "w") as f: f.write("\n".join(statement.statement(self.spec, [(self.obj, SYMBOL)])) + "\n")
        kinds = {}
        for k in range(1, len(proof)):                                     # (the first line names the function)
            l = proof[k]
            trials = [("left out", None)]
            if l in ("t lt", "t ge"): trials.append(("the other order", "t ge" if l == "t lt" else "t lt"))
            if l in ("t live", "t dead"): trials.append(("the other way", "t dead" if l == "t live" else "t live"))
            if l.startswith("s "): w = l.split(); trials.append(("a step's multiplier", " ".join(w[:2] + [str(int(w[2]) + 1)] + w[3:])))
            for kind, new in trials:
                lines = list(proof)
                if new is None: del lines[k]
                else: lines[k] = new
                with open(self.path("c.proof"), "w") as f: f.write("".join(x + "\n" for x in lines))
                r = subprocess.run([lean_verify.EXE, lean_verify.TABLE, self.path("s.statement"), self.path("c.proof")], capture_output=True, text=True)
                self.assertEqual(r.returncode == 0, r.stdout == "shown\n", r.stdout[:200])
                self.assertNotEqual(r.stdout, "shown\n", (k, l, kind))
                kinds[kind] = kinds.get(kind, 0) + 1
        print(f"\nthe proof of {SYMBOL} changed in one place: {kinds}", file=sys.stderr)
        self.assertEqual(kinds.get("left out", 0), len(proof) - 1)
        self.assertGreater(len(proof), 60)

    def test_a_line_of_the_statement_in_the_proof_is_refused(self):
        with open(self.kept) as f: proof = f.read()
        with open(self.path("s.statement"), "w") as f: f.write("\n".join(statement.statement(self.spec, [(self.obj, SYMBOL)])) + "\n")
        for line in ("ensures out (num 0) (num 0) (list)", "result v", "arg out out 10"):
            with open(self.path("more.proof"), "w") as f: f.write(line + "\n" + proof)
            r = subprocess.run([lean_verify.EXE, lean_verify.TABLE, self.path("s.statement"), self.path("more.proof")], capture_output=True, text=True)
            self.assertIn("refused: a line of the statement in the proof", r.stdout, line)

    def test_what_is_written_and_what_is_read_must_be_asked_apart(self):
        """statement.py: a contract that writes one run and reads another says `requires no_overlap` of them, or
        is refused; and what it then writes says so of the two runs."""
        both = self.spec.replace("out: 10 bytes, v: number", "out: 10 bytes, v: number, input: n bytes, n: number").replace(
            "    stack 24", "    trace depends on input\n    stack 24")
        self.assertNotEqual(both, self.spec)
        with self.assertRaises(SystemExit) as e: statement.statement(both, [(self.obj, SYMBOL)])
        self.assertIn("requires disjoint(out, input, 1)", str(e.exception))
        asked = both.replace("    returns r", "    requires disjoint(out, input, 1)\n    returns r")
        lines = statement.statement(asked, [(self.obj, SYMBOL)])
        self.assertIn("arg out out 10", lines)
        self.assertIn("arg input bytes n", lines)
        # a run written is not also named as one the trace depends on; two arguments have two names
        named = self.spec.replace("    stack 24", "    trace depends on out\n    stack 24")
        with self.assertRaises(SystemExit) as e: statement.statement(named, [(self.obj, SYMBOL)])
        self.assertIn("the trace depends on a run it writes", str(e.exception))
        twice = self.spec.replace("out: 10 bytes, v: number", "out: 10 bytes, v: number, v: number")
        with self.assertRaises(SystemExit) as e: statement.statement(twice, [(self.obj, SYMBOL)])
        self.assertIn("two arguments of one name", str(e.exception))


if __name__ == "__main__":
    unittest.main()
