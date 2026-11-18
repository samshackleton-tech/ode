#!/usr/bin/env python3
"""A call, in the verifier in Lean (Core.lean): `ode_equal` of examples/equal calls `ode_common` of the shipped
../kcheck/programs/common/odecommon.o. Both are in one statement, the called function first; the verifier
shows it, and then takes the call by its contract alone. With the caller, a contract or the statement's
order changed in one place it does not say `shown`, nor does the prover find a proof; each such case names
what the verifier then lacks or refuses, so that a case which stops short of the call is told. Two other
ways of writing the caller are shown too.

    python3 test_call.py        (skipped where Lean's `lake` is not installed)"""
import os, shutil, subprocess, sys, tempfile, time, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "lang"))
import lean_verify, odec, prove, statement
import built
COMMON = os.path.join(HERE, "..", "kcheck", "programs", "common")
EQUAL = os.path.join(HERE, "examples", "equal")
LAKE = lean_verify.LAKE

NOT_WHOLE = "a called function is given a run of bytes that is not one this function was given, whole"
UNDECIDED = "need compare"            # which of two numbers is the greater is asked, and the prover has no proof either way
# (what is changed, the caller's source as it is, the source changed, what the verifier then lacks or refuses):
# each is built again from the changed source
SOURCES = [
    ("the count is kept in a register a call may change", "  mov rbx, rdx\n  call ode_common\n  cmp rax, rbx\n", "  mov r10, rdx\n  call ode_common\n  cmp rax, r10\n", UNDECIDED),
    # (this one stops before the call: the verifier lets nothing be written below the stack pointer, so no call can write over what is held)
    ("the count is put below the stack pointer, where the call writes the address to come back to", "  mov rbx, rdx\n  call ode_common\n",
     "  mov [rsp - 8], rdx\n  call ode_common\n  mov rbx, [rsp - 8]\n", "a write that is not eight bytes of the frame in use"),
    ("the count handed over is 0", "  call ode_common\n", "  mov rdx, 0\n  call ode_common\n", NOT_WHOLE),
    ("the count is handed over as a run", "  call ode_common\n", "  mov rdi, rdx\n  call ode_common\n", NOT_WHOLE),
    ("the first run is handed over twice", "  call ode_common\n", "  mov rsi, rdi\n  call ode_common\n", UNDECIDED),
    ("the stack pointer is moved down before the call", "  call ode_common\n", "  sub rsp, 16\n  call ode_common\n  add rsp, 16\n",
     "a call needs more stack than this function's contract allows"),
    ("the stack pointer is above the frame at the call", "  mov rbx, rdx\n  call ode_common\n", "  mov rbx, rdx\n  add rsp, 16\n  call ode_common\n  sub rsp, 16\n",
     "the stack pointer leaves the frame the contract allows"),
    ("rbx is not given back", "  pop rbx\n  ret\n", "  pop rcx\n  ret\n", "a register a callee keeps does not hold what it held at entry"),
    ("1 is returned where the runs differ", "@differ:\n  xor eax, eax\n", "@differ:\n  mov rax, 1\n", UNDECIDED),
    ("the result is compared with another number", "  cmp rax, rbx\n", "  cmp rax, rdi\n", UNDECIDED),
    ("what a call leaves in rcx is used", "  cmp rax, rbx\n", "  cmp rax, rcx\n", UNDECIDED),
]
# other ways of writing the caller, each shown: (what, the lines as they are, the lines changed)
OTHER_WAYS = [
    ("the count is kept in another register a callee keeps",
     ("  push rbx\n  mov rbx, rdx\n", "  cmp rax, rbx\n", "  pop rbx\n  ret\n"), ("  push r12\n  mov r12, rdx\n", "  cmp rax, r12\n", "  pop r12\n  ret\n")),
    ("the count is kept in the frame, at the stack pointer",
     ("  push rbx\n  mov rbx, rdx\n", "  cmp rax, rbx\n", "  pop rbx\n  ret\n"), ("  sub rsp, 8\n  mov [rsp], rdx\n", "  mov rcx, [rsp]\n  cmp rax, rcx\n", "  add rsp, 8\n  ret\n")),
]
# (what is changed, the specification as it is, the specification changed, the function then not shown, what the verifier lacks or refuses)
SPECS = [
    ("the caller's contract allows less stack", "    stack 56\n", "    stack 48\n", "ode_equal", "a call needs more stack than this function's contract allows"),
    ("both contracts allow less stack, the caller's just what the call then takes", ("    stack 40\n", "    stack 56\n"), ("    stack 32\n", "    stack 48\n"), "ode_common", "need entail"),
    ("the called function's contract returns one less", "    returns common(a, b)\n", "    returns common(a, b) - 1\n", "ode_common", UNDECIDED),
    ("the caller's contract says 1 for runs that differ", "if common(a, b) == len(a) then 1 else 0", "if common(a, b) == len(a) then 1 else 1", "ode_equal", UNDECIDED),
    ("the called function needs an instruction set that the caller's contract does not name", "    stack 40\n", "    stack 40\n    needs sse41\n", "ode_equal",
     "a called function needs of the processor what this function's contract does not say it needs"),
    ("the caller's contract compares with another length", "if common(a, b) == len(a) then 1 else 0", "if common(a, b) == len(a) + 1 then 1 else 0", "ode_equal", UNDECIDED),
]


# the caller's contract written another way, each shown: (what, as it is, changed)
SPEC_WAYS = [
    ("the two sides exchanged", "if common(a, b) == len(a) then 1 else 0", "if len(a) == common(a, b) then 1 else 0"),
    ("by what differs", "if common(a, b) == len(a) then 1 else 0", "if common(a, b) != len(a) then 0 else 1"),
    ("both contracts name the instruction set the called function needs", ("    stack 40\n", "    stack 56\n"), ("    stack 40\n    needs sse41\n", "    stack 56\n    needs sse41\n")),
]


def changed(text, old, new):
    """`text` with each `old` (one, or several) put as `new`; each must be there once."""
    for o, n in zip(*((old, new) if isinstance(old, tuple) else ((old,), (new,)))):
        assert text.count(o) == 1, o
        text = text.replace(o, n)
    return text


@unittest.skipUnless(LAKE, "Lean's lake is not installed")
class Call(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        env = dict(os.environ, PATH=os.path.dirname(LAKE) + os.pathsep + os.environ["PATH"])
        built.built("odeverify")
        cls.dir = tempfile.mkdtemp(prefix="odecall-")
        cls.common, cls.equal = os.path.join(COMMON, "odecommon.o"), os.path.join(EQUAL, "odeequal.o")
        with open(os.path.join(EQUAL, "equal.spec")) as f: cls.spec = f.read()
        with open(os.path.join(EQUAL, "equal.ode")) as f: cls.source = f.read()
        with open(os.path.join(COMMON, "common.proof")) as f: cls.places = f.read()
        cls.kept = os.path.join(HERE, "proofs", "ode_equal.proof")

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.dir)

    def path(self, name): return os.path.join(self.dir, name)

    def found(self, spec, equal_obj, name="try"):
        """The prover's numbers for the two functions; or, where it finds no proof, the function it finds none
        for and the verifier's last word."""
        try: return prove.prove(spec, [(self.common, "ode_common", self.places), (equal_obj, "ode_equal", "")], self.path(name + ".statement"), self.path(name + ".proof"))
        except SystemExit as e:
            said = str(e)
            self.assertTrue(said.startswith("prove: no proof of "), said[:200])
            return said.split()[4], said.split("\n", 1)[1]

    def run_lines(self, lines, proof_path):
        with open(self.path("lines.statement"), "w") as f: f.write("".join(l + "\n" for l in lines))
        r = subprocess.run([prove.EXE, prove.TABLE, self.path("lines.statement"), proof_path], capture_output=True, text=True)
        self.assertEqual(r.returncode == 0, r.stdout == "shown\n", r.stdout[:200])
        return r.stdout

    def test_the_example_is_made_from_its_source(self):
        odec.build(os.path.join(EQUAL, "equal.ode"), "equal", self.path("made.o"))
        with open(self.path("made.o"), "rb") as f, open(self.equal, "rb") as g: self.assertEqual(f.read(), g.read())

    def test_shown(self):
        t = time.time()
        numbers = self.found(self.spec, self.equal, "shown")
        took = time.time() - t
        self.assertEqual(list(numbers), ["ode_common", "ode_equal"])               # the called function first
        with open(self.path("shown.proof")) as f: whole = f.read()
        part = whole[whole.index("for ode_equal\n"):]
        t = time.time()
        self.assertEqual(lean_verify.verify(self.spec, [(self.common, "ode_common"), (self.equal, "ode_equal")], self.path("shown.proof")), (True, "shown"))
        once = time.time() - t
        # the same whatever order the functions are asked in: the statement is written with the called function first
        self.assertEqual(lean_verify.verify(self.spec, [(self.equal, "ode_equal"), (self.common, "ode_common")], self.path("shown.proof")), (True, "shown"))
        print(f"\node_equal, which calls ode_common: both shown; ode_equal's part of the proof: {part.count(chr(10)) - 1} lines, {len(part)} bytes, "
              f"found in {numbers['ode_equal'][0]} runs of the verifier; the whole proof {len(whole)} bytes, found in {took:.1f} s; "
              f"one run from the files (with building the statement) {1000 * once:.0f} ms", file=sys.stderr)

    def test_the_kept_proof_shows_from_the_files(self):
        self.assertEqual(lean_verify.verify(self.spec, [(self.common, "ode_common"), (self.equal, "ode_equal")], self.kept), (True, "shown"))
        with open(self.kept) as f: kept = f.read()
        self.found(self.spec, self.equal, "again")
        with open(self.path("again.proof")) as f: self.assertEqual(f.read(), kept)  # and it is what the prover finds

    def test_the_caller_changed_in_one_place(self):
        for what, old, new, why in SOURCES:
            with self.subTest(what=what):
                with open(self.path("changed.ode"), "w") as f: f.write(changed(self.source, old, new))
                odec.build(self.path("changed.ode"), "equal", self.path("changed.o"))
                shown, said = lean_verify.verify(self.spec, [(self.common, "ode_common"), (self.path("changed.o"), "ode_equal")], self.kept)
                self.assertFalse(shown, what)
                self.assertTrue(said.endswith("\nin ode_equal"), (what, said[-100:]))     # the called function is shown as before
                where, last = self.found(self.spec, self.path("changed.o"))
                self.assertEqual(where, "ode_equal", what)
                self.assertIn(why, last, what)

    def test_the_caller_written_another_way(self):
        for what, old, new in OTHER_WAYS:
            with self.subTest(what=what):
                with open(self.path("other.ode"), "w") as f: f.write(changed(self.source, old, new))
                odec.build(self.path("other.ode"), "equal", self.path("other.o"))
                numbers = self.found(self.spec, self.path("other.o"), "other")
                self.assertEqual(list(numbers), ["ode_common", "ode_equal"], what)
                self.assertEqual(lean_verify.verify(self.spec, [(self.common, "ode_common"), (self.path("other.o"), "ode_equal")], self.path("other.proof")), (True, "shown"))

    def test_the_callers_contract_written_another_way(self):
        for what, old, new in SPEC_WAYS:
            with self.subTest(what=what):
                spec = changed(self.spec, old, new)
                self.assertEqual(list(self.found(spec, self.equal, "way")), ["ode_common", "ode_equal"], what)
                self.assertEqual(lean_verify.verify(spec, [(self.common, "ode_common"), (self.equal, "ode_equal")], self.path("way.proof")), (True, "shown"))

    def test_a_contract_changed_in_one_place(self):
        for what, old, new, unshown, why in SPECS:
            with self.subTest(what=what):
                spec = changed(self.spec, old, new)
                shown, said = lean_verify.verify(spec, [(self.common, "ode_common"), (self.equal, "ode_equal")], self.kept)
                self.assertFalse(shown, what)
                where, last = self.found(spec, self.equal)
                self.assertEqual(where, unshown, what)
                self.assertIn(why, last, what)

    def test_a_call_is_taken_only_by_a_function_shown_before(self):
        functions = [(self.common, "ode_common"), (self.equal, "ode_equal")]
        lines = statement.statement(self.spec, functions)
        self.assertEqual(self.run_lines(lines, self.kept), "shown\n")
        a, b = lines.index("fn ode_common"), lines.index("fn ode_equal")
        end = min(k for k, l in enumerate(lines) if l.startswith("def "))
        self.assertTrue(a < b < end)
        # the caller before the function it calls
        said = self.run_lines(lines[b:end] + lines[a:b] + lines[end:], self.kept)
        self.assertEqual(said, "refused: a call of ode_common, which is not a function shown before this one\nin ode_equal\n")
        # the called function not in the statement at all
        said = self.run_lines(lines[b:], self.kept)
        self.assertTrue(said.startswith("refused: the proof speaks of ode_common, which is no function of the statement"), said[:200])
        with open(self.kept) as f: kept = f.read()
        with open(self.path("part.proof"), "w") as f: f.write(kept[kept.index("for ode_equal\n"):])
        said = self.run_lines(lines[b:], self.path("part.proof"))
        self.assertEqual(said, "refused: a call of ode_common, which is not a function shown before this one\nin ode_equal\n")
        # a function that calls itself
        self.assertEqual(sum(l.endswith(".call ode_common") for l in lines), 1)
        said = self.run_lines([l.replace(".call ode_common", ".call ode_equal") for l in lines], self.kept)
        self.assertEqual(said, "refused: a call of ode_equal, which is not a function shown before this one\nin ode_equal\n")
        # two functions of one name: the second could be taken for the first
        said = self.run_lines(lines[:b] + lines[a:b] + lines[b:], self.kept)
        self.assertEqual(said, "refused: two functions are named ode_common\n")
        # and whoever writes the statement is told before the verifier is asked
        for wrong, why in (([(self.equal, "ode_equal")], "ode_equal calls ode_common, which is not among the functions to be shown"),
                           (functions + [(self.common, "ode_common")], "two functions are named ode_common")):
            with self.assertRaises(SystemExit) as e: statement.statement(self.spec, wrong)
            self.assertIn(why, str(e.exception))

    def test_a_name_from_the_file_cannot_put_a_line_into_the_statement(self):
        # the caller built with a long name for the function it calls; then that name, in the object's table of
        # names, made `ode_common`, a line break, and a line that would give the contract one more argument
        plain, crafted = b"ode_commonXXXXXXXXXXXXXX", b"ode_common\narg zz number"
        self.assertEqual(len(plain), len(crafted))
        with open(self.path("long.ode"), "w") as f: f.write(changed(self.source, "  call ode_common\n", f"  call {plain.decode()}\n"))
        odec.build(self.path("long.ode"), "equal", self.path("long.o"))
        with open(self.path("long.o"), "rb") as f: b = f.read()
        self.assertEqual(b.count(plain), 1)
        with open(self.path("crafted.o"), "wb") as f: f.write(b.replace(plain, crafted))
        with self.assertRaises(Exception) as e: statement.statement(self.spec, [(self.common, "ode_common"), (self.path("crafted.o"), "ode_equal")])
        self.assertIn("an instruction this verifier does not know", str(e.exception))      # the reader of code: no instance of the row
        # and were such a row's text ever to come through, the statement's writer refuses the line
        for line in ("i 4 9 .call ode_common\narg zz number", "i 4 9 .call ode_common\rarg zz number", "i 4 9 .call a\u2028b", ""):
            with self.assertRaises(SystemExit): statement.one_line(line)
        self.assertEqual(statement.one_line("i 4 9 .call ode_common"), "i 4 9 .call ode_common")
        with self.assertRaises(SystemExit) as e: statement.statement(self.spec, [(self.common, "ode_common\nstack 4000")])
        self.assertIn("no plain name", str(e.exception))

    def test_the_called_functions_proof_left_out(self):
        with open(self.kept) as f: kept = f.read()
        with open(self.path("part.proof"), "w") as f: f.write(kept[kept.index("for ode_equal\n"):])
        shown, said = lean_verify.verify(self.spec, [(self.common, "ode_common"), (self.equal, "ode_equal")], self.path("part.proof"))
        self.assertFalse(shown)
        self.assertTrue(said.endswith("\nin ode_common"), said[-100:])               # nothing is taken of it unshown


if __name__ == "__main__":
    built.same_every_run()          # the prover finds the same proof every run
    unittest.main()
