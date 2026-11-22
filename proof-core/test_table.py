#!/usr/bin/env python3
"""The file's read-only data, in the verifier in Lean: four functions of examples/table take the address of
a table of numbers in their file's data (`lea reg, [rip + #primes]`, the row `lea_data`) and read numbers
of it, four bytes, eight bytes and one byte, and one decides a jump by what it read.

The account of the machine has, for each object file, the address at which that file's data lies
(`State.data`). The statement gives the file's bytes once (a `piece` line: statement.py writes it from the
object file, for a file in which a function takes the data's address), and the function says which file's
data it takes the address in (a `data` line). What is shown holds wherever the program is loaded: those
bytes in memory at the file's address, apart from the function's frame, from the address to return to and
from every run given to write. The verifier takes an address that is the data's plus a number as a place
in the data, and a read there as the number the file's bytes make. (A call of a function that reads its
file's data: test_sum.py.)

With the function, its table or its contract changed in one place it does not say `shown`, nor does the
prover find a proof; each case names what the verifier then refuses or lacks. A statement without its
`data` line or its `piece` line, or with one byte of the data changed, is not shown either. Beside its
verdict lean_verify.py says that the place of the data in memory is the linker's and the loader's part.

    python3 test_table.py        (skipped where Lean's `lake` is not installed)"""
import os, shutil, subprocess, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "lang"))
import lean_verify, odec, prove
import built
TABLE = os.path.join(HERE, "examples", "table")
LAKE = lean_verify.LAKE

# (the function in the source, its name in the file, its object, its kept proof)
FUNCTIONS = [("third", "ode_third", "odethird.o"), ("pair", "ode_pair", "odepair.o"),
             ("second", "ode_second", "odesecond.o"), ("first", "ode_first_is_two", "odefirst.o")]
RETURNS = "need entail"               # what is returned is to be shown the contract's number, and it is another number
OUTSIDE = "a read of the file's read-only data that is not one, four or eight bytes within it"
WRITTEN = "a write to a run given only to read, or to no run given"
# (the function, what is changed, the source as it is, the source changed, what the verifier then says)
SOURCES = [
    ("third", "another number of the table is read", "  mov eax, DWORD PTR [rax + 8]\n", "  mov eax, DWORD PTR [rax + 12]\n", RETURNS),
    ("third", "the read is past the table's end", "  mov eax, DWORD PTR [rax + 8]\n", "  mov eax, DWORD PTR [rax + 32]\n", OUTSIDE),
    ("third", "the read is half past the table's end", "  mov eax, DWORD PTR [rax + 8]\n", "  mov eax, DWORD PTR [rax + 30]\n", OUTSIDE),
    ("third", "the table has another number there", "data primes = 2, 3, 5, 7,", "data primes = 2, 3, 6, 7,", RETURNS),
    ("third", "the table is written to", "  mov eax, DWORD PTR [rax + 8]\n", "  mov [rax + 8], rcx\n  mov eax, DWORD PTR [rax + 8]\n", WRITTEN),
    ("pair", "eight bytes are read where four are left", "  mov rax, [rcx + 16]\n", "  mov rax, [rcx + 28]\n", OUTSIDE),
    ("pair", "the eight bytes are read four bytes on", "  mov rax, [rcx + 16]\n", "  mov rax, [rcx + 20]\n", RETURNS),
    ("second", "the address is walked on by eight", "  add rcx, 4\n", "  add rcx, 8\n", RETURNS),
    ("second", "the address is walked past the table", "  add rcx, 4\n", "  add rcx, 32\n", OUTSIDE),
    ("first", "the first number is compared with three", "  cmp rax, 2\n", "  cmp rax, 3\n", RETURNS),
]
# (the function, what is changed, the specification as it is, the specification changed)
SPECS = [
    ("third", "the contract says the fourth prime", "    returns 5\n", "    returns 7\n"),
    ("pair", "the contract says one more", "    returns 55834574859\n", "    returns 55834574860\n"),
    ("second", "the contract says the first prime", "    returns 3\n", "    returns 2\n"),
    ("first", "the contract says no", "    returns 1\n", "    returns 0\n"),
]


@unittest.skipUnless(LAKE, "Lean's lake is not installed")
class Table(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.dir = tempfile.mkdtemp(prefix="odetable-")
        with open(os.path.join(TABLE, "table.spec")) as f: cls.spec = f.read()
        with open(os.path.join(TABLE, "table.ode")) as f: cls.source = f.read()
        cls.fns = {fn: (symbol, os.path.join(TABLE, obj), os.path.join(HERE, "proofs", symbol + ".proof")) for fn, symbol, obj in FUNCTIONS}

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.dir)

    def path(self, name): return os.path.join(self.dir, name)

    def found(self, spec, obj, symbol, name="try"):
        """The prover's numbers; or, where it finds no proof, the verifier's last word."""
        try: return prove.prove(spec, [(obj, symbol, "")], self.path(name + ".statement"), self.path(name + ".proof"))
        except SystemExit as e:
            said = str(e)
            self.assertTrue(said.startswith("prove: no proof of " + symbol), said[:200])
            return said.split("\n", 1)[1]

    def run_lines(self, lines, proof_path):
        with open(self.path("lines.statement"), "w") as f: f.write("".join(l + "\n" for l in lines))
        r = subprocess.run([prove.EXE, prove.TABLE, self.path("lines.statement"), proof_path], capture_output=True, text=True)
        self.assertEqual(r.returncode == 0, r.stdout == "shown\n", r.stdout[:200])
        return r.stdout + r.stderr

    def test_the_examples_are_made_from_their_source(self):
        for fn, (symbol, obj, kept) in self.fns.items():
            odec.build(os.path.join(TABLE, "table.ode"), fn, self.path("made.o"))
            with open(self.path("made.o"), "rb") as f, open(obj, "rb") as g: self.assertEqual(f.read(), g.read(), fn)

    def test_shown_and_the_kept_proofs_are_what_the_prover_finds(self):
        for fn, (symbol, obj, kept) in self.fns.items():
            with self.subTest(fn=fn):
                numbers = self.found(self.spec, obj, symbol, fn)
                self.assertEqual(list(numbers), [symbol])
                self.assertEqual(lean_verify.verify(self.spec, [(obj, symbol)], kept), (True, "shown"))
                with open(kept) as f, open(self.path(fn + ".proof")) as g: self.assertEqual(f.read(), g.read())
                with open(self.path(fn + ".statement")) as f: lines = f.read().splitlines()
                self.assertEqual(sum(l.startswith("i ") and ".lea_data " in l for l in lines), 1)      # the row this is about
                data = [l for l in lines if l.startswith(("piece ", "data "))]
                # the table, as the file has it, on the boundary the file gives its data; and the function is of that file
                self.assertEqual(data, ["piece 64 " + "".join(f"{p:02X}000000" for p in (2, 3, 5, 7, 11, 13, 17, 19)), "data 0"])
                self.assertEqual(lines.index("data 0"), lines.index("fn " + symbol) + 1)       # before the function's instructions

    def test_a_function_changed_in_one_place(self):
        for fn, what, old, new, why in SOURCES:
            with self.subTest(what=what):
                symbol, obj, kept = self.fns[fn]
                self.assertEqual(self.source.count(old), 1, old)
                with open(self.path("changed.ode"), "w") as f: f.write(self.source.replace(old, new))
                odec.build(self.path("changed.ode"), fn, self.path("changed.o"))
                self.assertFalse(lean_verify.verify(self.spec, [(self.path("changed.o"), symbol)], kept)[0], what)
                last = self.found(self.spec, self.path("changed.o"), symbol)
                self.assertIsInstance(last, str, what)                  # no proof is found
                self.assertIn(why, last, what)

    def test_a_contract_changed_in_one_place(self):
        for fn, what, old, new in SPECS:
            with self.subTest(what=what):
                symbol, obj, kept = self.fns[fn]
                self.assertEqual(self.spec.count(old), 1, old)
                spec = self.spec.replace(old, new)
                self.assertFalse(lean_verify.verify(spec, [(obj, symbol)], kept)[0], what)
                last = self.found(spec, obj, symbol)
                self.assertIsInstance(last, str, what)
                self.assertIn(RETURNS, last, what)

    def test_the_verdict_names_what_the_linker_and_the_loader_owe(self):
        """`shown` of a function that reads its file's data holds where the data lies in memory as the function
        expects: lean_verify.py says so beside the verdict, and says nothing of it for a function without data."""
        symbol, obj, kept = self.fns["third"]
        r = subprocess.run([sys.executable, os.path.join(HERE, "lean_verify.py"), os.path.join(TABLE, "table.spec"), kept, obj + ":" + symbol], capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("shown: ode_third in odethird.o meets its contract", r.stdout)
        self.assertIn("Functions here read constants of their files: odethird.o (32 bytes of read-only data).", r.stdout)
        self.assertIn("the linker's and the\nloader's part", r.stdout)
        self.assertIn("relies on them for it and does not show it", r.stdout)
        low = os.path.join(HERE, "examples", "low")
        r = subprocess.run([sys.executable, os.path.join(HERE, "lean_verify.py"), os.path.join(low, "low.spec"), os.path.join(HERE, "proofs", "ode_low.proof"),
                            os.path.join(low, "odelow.o") + ":ode_low"], capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertNotIn("linker", r.stdout)

    def test_the_statements_data(self):
        """The verifier in Lean goes by the bytes the statement gives. Without the function's `data` line the
        address of the data is refused, and without the file's bytes that line names nothing; with one byte
        of them changed the function returns another number than its contract says; and bytes that are no
        bytes are not read."""
        symbol, obj, kept = self.fns["third"]
        self.found(self.spec, obj, symbol, "whole")
        with open(self.path("whole.statement")) as f: lines = f.read().splitlines()
        self.assertEqual(self.run_lines(lines, kept), "shown\n")
        k = next(i for i, l in enumerate(lines) if l.startswith("piece "))
        d = lines.index("data 0")
        self.assertIn("the address of a place that is not in the file's read-only data", self.run_lines(lines[:d] + lines[d + 1:], kept))
        self.assertIn("refused: no read-only data of that number stands before", self.run_lines(lines[:k] + lines[k + 1:], kept))
        head = len("piece 64 ")
        other = lines[k][:head + 16] + "06" + lines[k][head + 18:]      # the third number's lowest byte: 5 becomes 6
        self.assertNotEqual(other, lines[k]); self.assertEqual(len(other), len(lines[k]))
        self.assertIn(RETURNS, self.run_lines(lines[:k] + [other] + lines[k + 1:], kept))
        short = lines[k][:head + 16]                                    # the table cut off before the number read
        self.assertIn(OUTSIDE, self.run_lines(lines[:k] + [short] + lines[k + 1:], kept))
        for bad in (lines[k] + "0", lines[k][:-1] + "G"):
            self.assertIn("cannot read the bytes of a file's read-only data", self.run_lines(lines[:k] + [bad] + lines[k + 1:], kept))


if __name__ == "__main__":
    unittest.main()
