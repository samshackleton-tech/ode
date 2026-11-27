#!/usr/bin/env python3
"""A call of a function that reads constants, in the verifier in Lean: `ode_sum` and `ode_twice` of
examples/sum call `ode_third` of examples/table/odethird.o. Each of the two object files has a table of
numbers in its read-only data. `ode_third` reads the third prime from its file's table; `ode_sum` adds to
it the third square, read from its own file's table (whose address it keeps across the call); `ode_twice`
doubles it and takes no address in its own file's data.

The account of the machine has, for each object file of the program, the address at which that file's
read-only data lies (`State.data`). A statement gives each such file's bytes once (`piece`), and a function
that takes an address in its file's data says which file's it is (`data K`). What is shown holds wherever
the program is loaded (`Loaded` in Contract.lean): each file's bytes in memory at its address, and nothing
that a function may write lying over them or over the program's code. A contract says nothing of
constants, and any function may read them: so a call of a function that reads them is taken by its
contract alone, as any other call.

With a function, a contract or the statement changed in one place, so that what is stated is false,
nothing is shown, and each case names what the verifier then refuses or lacks. Statements that are still
true are shown: the two files' tables holding the same bytes, and the table's address taken after the call.

    python3 test_sum.py        (skipped where Lean's `lake` is not installed)"""
import os, shutil, subprocess, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
KCHECK = os.path.join(HERE, "..", "kcheck")
sys.path.insert(0, HERE); sys.path.insert(0, KCHECK); sys.path.insert(0, os.path.join(HERE, "..", "lang"))
import built, lean_verify, odec, prove, statement
SUM = os.path.join(HERE, "examples", "sum")
TABLE = os.path.join(HERE, "examples", "table")
LAKE = lean_verify.LAKE
THIRD = (os.path.join(TABLE, "odethird.o"), "ode_third")
# (the function in the source, its name in the file, its object)
FUNCTIONS = {"twice": ("ode_twice", os.path.join(SUM, "odetwice.o")), "sum": ("ode_sum", os.path.join(SUM, "odesum.o"))}
PRIMES = "".join(f"{p:02X}000000" for p in (2, 3, 5, 7, 11, 13, 17, 19))
SQUARES = "".join(f"{p:02X}000000" for p in (1, 4, 9, 16))

RETURNS = "need entail"               # what is returned is to be shown the contract's number, and it is another number
OUTSIDE = "refused: a read of the file's read-only data that is not one, four or eight bytes within it"
WRITTEN = "refused: a write to a run given only to read, or to no run given"
NOT_KEPT = "refused: at the return a register a callee keeps (rbx) does not hold what it held at entry"
STACK = "refused: a call needs more stack than this function's contract allows"
NOT_IN_DATA = "refused: the address of a place that is not in the file's read-only data"
NO_PIECE = "refused: no read-only data of that number stands before"
NOT_TO_WRITE = "refused: a called function is given to write what is not whole words of a run this function may read and write, each of them known"
DATA_LATE = "refused: `data` after an instruction of the function"
# (the function, what is changed, the source as it is, the source changed, what the verifier then says)
SOURCES = [
    ("sum", "another number of this file's table is read", "  mov ecx, DWORD PTR [rbx + 8]\n", "  mov ecx, DWORD PTR [rbx + 12]\n", RETURNS),
    ("sum", "the read is past the end of this file's table", "  mov ecx, DWORD PTR [rbx + 8]\n", "  mov ecx, DWORD PTR [rbx + 16]\n", OUTSIDE),
    ("sum", "the read is half past the end of this file's table", "  mov ecx, DWORD PTR [rbx + 8]\n", "  mov ecx, DWORD PTR [rbx + 14]\n", OUTSIDE),
    ("sum", "this file's table has another number there", "data squares = 1, 4, 9, 16", "data squares = 1, 4, 10, 16", RETURNS),
    ("sum", "this file's table is written to", "  mov ecx, DWORD PTR [rbx + 8]\n", "  mov [rbx + 8], rax\n  mov ecx, DWORD PTR [rbx + 8]\n", WRITTEN),
    ("sum", "what the called function returns is not added", "  add rax, rcx\n", "  mov rax, rcx\n", RETURNS),
    ("sum", "rbx is not given back", "  pop rbx\n  ret\n", "  pop rcx\n  ret\n", NOT_KEPT),
    ("twice", "what the called function returns is not doubled", "  add rax, rax\n", "", RETURNS),
]
# (the function, what is changed, the specification as it is, the specification changed, what the verifier then
# says, the function it says it of)
SPECS = [
    ("sum", "the contract says the sum made with the fourth prime", "    returns 14\n", "    returns 16\n", RETURNS, "ode_sum"),
    ("sum", "the called function's contract says the fourth prime", "    returns 5\n", "    returns 7\n", RETURNS, "ode_third"),
    ("sum", "the stack is said to be eight bytes", "    stack 16\n", "    stack 8\n", STACK, "ode_sum"),
    ("twice", "the contract says one more", "    returns 10\n", "    returns 11\n", RETURNS, "ode_twice"),
    ("twice", "the called function's contract says the fourth prime", "    returns 5\n", "    returns 7\n", RETURNS, "ode_third"),
]
# Changed so that what is stated is still true: (what, [(the source as it is, the source changed)], [(the
# specification as it is, the specification changed)]). Each is shown.
STILL_TRUE = [
    ("the two files' tables hold the same bytes: two copies, each where its own file is loaded",
     [("data squares = 1, 4, 9, 16", "data squares = 2, 3, 5, 7, 11, 13, 17, 19")], [("    returns 14\n", "    returns 10\n")]),
    ("the table's address is taken after the call, and nothing is kept across it",
     [("  push rbx\n  lea rbx, [rip + #squares]\n  call ode_third\n  mov ecx, DWORD PTR [rbx + 8]\n  add rax, rcx\n  pop rbx\n",
       "  call ode_third\n  lea rcx, [rip + #squares]\n  mov ecx, DWORD PTR [rcx + 8]\n  add rax, rcx\n")], [("    stack 16\n", "    stack 8\n")]),
]


def once(text, old, new):
    assert text.count(old) == 1, (old, text.count(old))
    return text.replace(old, new)


@unittest.skipUnless(LAKE, "Lean's lake is not installed")
class Sum(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.dir = tempfile.mkdtemp(prefix="odesum-")
        with open(os.path.join(SUM, "sum.spec")) as f: cls.spec = f.read()
        with open(os.path.join(SUM, "sum.ode")) as f: cls.source = f.read()

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.dir)

    def path(self, name): return os.path.join(self.dir, name)

    def found(self, spec, obj, symbol, name="try"):
        """The prover's numbers; or, where it finds no proof, the verifier's last word and the function it is of."""
        try: return prove.prove(spec, [(THIRD[0], THIRD[1], ""), (obj, symbol, "")], self.path(name + ".statement"), self.path(name + ".proof"))
        except SystemExit as e:
            said = str(e)
            self.assertTrue(said.startswith("prove: no proof of "), said[:200])
            return said.split("\n", 1)[1], said.split("\n", 1)[0][len("prove: no proof of "):].split()[0].rstrip(":,.")

    def kept(self, symbol):
        """The kept proofs of `ode_third` and of this function, in one file."""
        path = self.path("kept.proof")
        with open(path, "w") as out:
            for name in (THIRD[1], symbol):
                with open(os.path.join(HERE, "proofs", name + ".proof")) as f: out.write(f.read())
        return path

    def run_lines(self, lines, proof_path):
        with open(self.path("lines.statement"), "w") as f: f.write("".join(l + "\n" for l in lines))
        r = subprocess.run([prove.EXE, prove.TABLE, self.path("lines.statement"), proof_path], capture_output=True, text=True)
        self.assertEqual(r.returncode == 0, r.stdout == "shown\n", r.stdout[:200])
        return r.stdout + r.stderr

    def test_the_examples_are_made_from_their_source(self):
        for fn, (symbol, obj) in FUNCTIONS.items():
            odec.build(os.path.join(SUM, "sum.ode"), fn, self.path("made.o"))
            with open(self.path("made.o"), "rb") as f, open(obj, "rb") as g: self.assertEqual(f.read(), g.read(), fn)

    def test_the_statement_gives_each_files_data_once(self):
        lines = statement.statement(self.spec, [(FUNCTIONS["sum"][1], "ode_sum"), THIRD])
        # the called function first; its file's table is number 0, the caller's file's number 1
        self.assertEqual(lines[:4], ["piece 64 " + PRIMES, "piece 64 " + SQUARES, "fn ode_third", "data 0"])
        at = lines.index("fn ode_sum")
        self.assertEqual(lines[at + 1], "data 1")
        self.assertEqual(sum(l.startswith(("piece ", "data ")) for l in lines), 4)
        # a function that takes no address in its file's data: its file's data is not in the statement
        lines = statement.statement(self.spec, [THIRD, (FUNCTIONS["twice"][1], "ode_twice")])
        self.assertEqual([l for l in lines if l.startswith(("piece ", "data "))], ["piece 64 " + PRIMES, "data 0"])
        self.assertEqual(lines[lines.index("fn ode_twice") + 1], "i 0 5 .call ode_third")

    def test_shown_and_the_kept_proofs_are_what_the_prover_finds(self):
        for fn, (symbol, obj) in FUNCTIONS.items():
            with self.subTest(fn=fn):
                numbers = self.found(self.spec, obj, symbol, fn)
                self.assertEqual(list(numbers), [THIRD[1], symbol])
                self.assertEqual(lean_verify.verify(self.spec, [THIRD, (obj, symbol)], self.kept(symbol)), (True, "shown"))
                with open(self.path(fn + ".proof")) as f: found = f.read()
                with open(os.path.join(HERE, "proofs", symbol + ".proof")) as f: self.assertEqual(found[found.index("for " + symbol):], f.read())
                # control: the called function is not left out of what is to be shown
                with self.assertRaises(SystemExit) as e: lean_verify.verify(self.spec, [(obj, symbol)], self.kept(symbol))
                self.assertIn("which is not among the functions to be shown", str(e.exception))

    def test_a_function_changed_in_one_place(self):
        for fn, what, old, new, why in SOURCES:
            with self.subTest(what=what):
                symbol, obj = FUNCTIONS[fn]
                with open(self.path("changed.ode"), "w") as f: f.write(once(self.source, old, new))
                odec.build(self.path("changed.ode"), fn, self.path("changed.o"))
                self.assertFalse(lean_verify.verify(self.spec, [THIRD, (self.path("changed.o"), symbol)], self.kept(symbol))[0], what)
                last = self.found(self.spec, self.path("changed.o"), symbol)
                self.assertIsInstance(last, tuple, what)                # no proof is found
                self.assertIn(why, last[0], what)
                self.assertEqual(last[1], symbol, what)

    def test_a_contract_changed_in_one_place(self):
        for fn, what, old, new, why, where in SPECS:
            with self.subTest(what=what):
                symbol, obj = FUNCTIONS[fn]
                spec = once(self.spec, old, new)
                self.assertFalse(lean_verify.verify(spec, [THIRD, (obj, symbol)], self.kept(symbol))[0], what)
                last = self.found(spec, obj, symbol)
                self.assertIsInstance(last, tuple, what)
                self.assertIn(why, last[0], what)
                self.assertEqual(last[1], where, what)

    def test_changed_and_still_true(self):
        for what, sources, specs in STILL_TRUE:
            with self.subTest(what=what):
                source, spec = self.source, self.spec
                for old, new in sources: source = once(source, old, new)
                for old, new in specs: spec = once(spec, old, new)
                with open(self.path("true.ode"), "w") as f: f.write(source)
                odec.build(self.path("true.ode"), "sum", self.path("true.o"))
                numbers = self.found(spec, self.path("true.o"), "ode_sum", "true")
                self.assertIsInstance(numbers, dict, what)
                self.assertEqual(lean_verify.verify(spec, [THIRD, (self.path("true.o"), "ode_sum")], self.path("true.proof")), (True, "shown"))
        # (the first of them: the statement has the same bytes twice, as two files' data)
        source = once(self.source, *STILL_TRUE[0][1][0])
        with open(self.path("same.ode"), "w") as f: f.write(source)
        odec.build(self.path("same.ode"), "sum", self.path("same.o"))
        lines = statement.statement(once(self.spec, *STILL_TRUE[0][2][0]), [THIRD, (self.path("same.o"), "ode_sum")])
        self.assertEqual(lines[:2], ["piece 64 " + PRIMES, "piece 64 " + PRIMES])

    def test_the_statements_data(self):
        """The verifier in Lean goes by the lines of the statement. The kept proofs show it as statement.py
        writes it. With a byte of either file's data changed, with `ode_sum` said to be of the other file,
        without its `data` line, with a file's data left out or the two exchanged, nothing is shown."""
        symbol, obj = FUNCTIONS["sum"]
        kept = self.kept(symbol)
        lines = statement.statement(self.spec, [THIRD, (obj, symbol)])
        self.assertEqual(self.run_lines(lines, kept), "shown\n")
        self.assertEqual(lines[:2], ["piece 64 " + PRIMES, "piece 64 " + SQUARES])
        mine = lines.index("fn ode_sum") + 1
        self.assertEqual((lines[3], lines[mine]), ("data 0", "data 1"))
        def said(changed): return self.run_lines(changed, kept)
        def put(k, line): return lines[:k] + [line] + lines[k + 1:]
        # the third prime is 6 in the statement: `ode_third` returns another number than its contract says
        other = once(lines[0], "05000000", "06000000")
        self.assertIn(RETURNS, said(put(0, other)))
        self.assertTrue(said(put(0, other)).rstrip().endswith("in ode_third"))
        # the third square is 10: `ode_sum` returns another number
        other = once(lines[1], "09000000", "0A000000")
        self.assertIn(RETURNS, said(put(1, other)))
        self.assertTrue(said(put(1, other)).rstrip().endswith("in ode_sum"))
        # `ode_sum` is said to be of the file of the primes: it reads the third prime, and returns 10
        self.assertIn(RETURNS, said(put(mine, "data 0")))
        self.assertTrue(said(put(mine, "data 0")).rstrip().endswith("in ode_sum"))
        # `ode_sum` is said to be of no file with data; of a file that the statement does not have; after its instructions
        self.assertIn(NOT_IN_DATA, said(lines[:mine] + lines[mine + 1:]))
        self.assertIn(NO_PIECE, said(put(mine, "data 2")))
        end = next(k for k in range(mine, len(lines)) if not lines[k].startswith(("i ", "data ")))
        self.assertIn(DATA_LATE, said(lines[:mine] + lines[mine + 1:end] + ["data 1"] + lines[end:]))
        # the primes' data left out: the squares are then number 0, and no data has the number 1
        self.assertIn(NO_PIECE, said(lines[1:]))
        # the squares' data left out
        self.assertIn(NO_PIECE, said(lines[:1] + lines[2:]))
        # the two files' data exchanged: `ode_third` reads the third square
        self.assertIn(RETURNS, said([lines[1], lines[0]] + lines[2:]))
        self.assertTrue(said([lines[1], lines[0]] + lines[2:]).rstrip().endswith("in ode_third"))
        # bytes that are no bytes, and a boundary that is no number, are not read
        for bad in (lines[1] + "0", lines[1][:-1] + "G", "piece x " + SQUARES):
            self.assertIn("cannot read the bytes of a file's read-only data", said(put(1, bad)))

    def test_a_table_is_not_handed_to_a_called_function_to_write(self):
        """`ode_parent` (examples/parent) hands a half of a block in its stack frame to the one-block kernel,
        which writes a chaining value there. Changed to hand the kernel a table of its file's read-only data
        instead, it is not shown: a called function is given to write only what its caller may write."""
        kernel = "blake3_servil_compress_in_place_sse41"
        with open(os.path.join(KCHECK, "blake3.spec")) as f: spec = f.read()
        for folder, name in (("kernel", "kernel_sse41.contract"), ("parent", "parent.contract")):
            with open(os.path.join(HERE, "examples", folder, name)) as f: spec += "\n" + f.read()
        with open(os.path.join(HERE, "examples", "parent", "parent.ode")) as f: source = f.read()
        for what, new, want in (("as it is", "  lea rdi, [rsp + 0]\n", None), ("a table", "  lea rdi, [rip + #table]\n", NOT_TO_WRITE)):
            with self.subTest(what=what):
                with open(self.path("parent.ode"), "w") as f: f.write("data table = 0, 0, 0, 0, 0, 0, 0, 0\n" + once(source, "  lea rdi, [rsp + 0]\n", new))
                odec.build(self.path("parent.ode"), "parent", self.path("parent.o"))
                functions = [(os.path.join(KCHECK, "b3hashr.o"), kernel, ""), (self.path("parent.o"), "ode_parent", "")]
                try:
                    prove.prove(spec, functions, self.path("parent.statement"), self.path("parent.proof"))
                    said = "shown"
                except SystemExit as e: said = str(e)
                if want is None: self.assertEqual(said, "shown")
                else:
                    self.assertIn(want, said)
                    self.assertIn("\nin ode_parent", said)

    def test_the_verdict_names_what_the_linker_and_the_loader_owe(self):
        symbol, obj = FUNCTIONS["sum"]
        r = subprocess.run([sys.executable, os.path.join(HERE, "lean_verify.py"), os.path.join(SUM, "sum.spec"), self.kept(symbol),
                            THIRD[0] + ":" + THIRD[1], obj + ":" + symbol], capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("shown: ode_third in odethird.o meets its contract", r.stdout)
        self.assertIn("shown: ode_sum in odesum.o meets its contract", r.stdout)
        self.assertIn("Functions here read constants of their files: odethird.o (32 bytes of read-only data), odesum.o (16 bytes of read-only data).", r.stdout)
        self.assertIn("wherever the program is\nloaded", r.stdout)
        self.assertIn("the linker's and the\nloader's part", r.stdout)


if __name__ == "__main__":
    unittest.main()
