#!/usr/bin/env python3
"""A call of the hash's 32-way kernel: `ode_quad32` (examples/quad/quad32.ode) makes the parent of two
parent nodes as `ode_quad` does (test_quad.py), with the 32-way kernel in place of the 16-way one: a table
of thirty-two addresses and two runs of 1024 bytes, all in its stack frame.

    python3 test_quad32.py        (needs Lean's `lake`; the tests are skipped where it is not installed)

The 32-way kernel finds the order of the message words in a table of constants in its object file. Until
the constants of a program were said once for the loaded program (test_sum.py), the verifier in Lean
refused every call of a function that reads constants, so no function that calls this kernel could be
shown. This is the first one. The call goes by the rule for a function that is given a table of addresses
(`symCallL` in Core.lean), as `ode_quad`'s calls do.

The function, its contract and the kept proof are shown; with the contract, the function or the
verifier's input file changed in one place, so that what is stated is false, nothing is shown, and each
case names what the verifier then refuses. Two changed statements that are still true are shown."""
import os, shutil, subprocess, sys, tempfile, time, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
KCHECK = os.path.join(HERE, "..", "kcheck")
sys.path.insert(0, HERE); sys.path.insert(0, KCHECK); sys.path.insert(0, os.path.join(HERE, "..", "lang"))
import built, lean_verify, odec, prove, statement

QUAD = os.path.join(HERE, "examples", "quad")
NAME, P32 = "ode_quad32", "blake3_servil_avx512_p32"
FUNCTIONS = [(os.path.join(KCHECK, "b3hashr.o"), P32), (os.path.join(QUAD, "odequad32.o"), NAME)]
# Why the verifier refuses.
FOLLOW = "refused: the specification's words are not followed on the terms the function made"
WORD = "refused: a word of the run is not known to hold what the specification says"
STACK = "refused: a call needs more stack than this function's contract allows"
LANE = "refused: a lane of a called function's table is not blocks this function may read, every word of them known"
FRAME = "refused: a called function's table of addresses, or the run it writes, is no part of this function's frame, or the two overlap"
NOT_IN_DATA = "refused: the address of a place that is not in the file's read-only data"
NO_PIECE = "refused: no read-only data of that number stands before"
P = "compress(kf.key, {}, counter(0), 64, kf.flags | PARENT)"
ENS = f"parent(kf.key, kf.flags, {P.format('a')}, {P.format('b')})"


def once(old, new, n=1):
    """The text with `old`, which stands in it `n` times, replaced by `new`."""
    def change(text):
        assert text.count(old) == n, (old, text.count(old))
        return text.replace(old, new)
    return change


def last(old, new):
    """The text with the second `old` replaced by `new`; `old` stands in it twice (once a round)."""
    def change(text):
        assert text.count(old) == 2, (old, text.count(old))
        at = text.rindex(old)
        return text[:at] + new + text[at + len(old):]
    return change


def then(*changes):
    def change(text):
        for c in changes: text = c(text)
        return text
    return change


def out_from(base):
    """`out` is read from the frame at `base` in place of 1280: the last change first, so that no place is changed twice."""
    return then(*[once(f"  mov rax, qword ptr [rsp + {1280 + 8 * k}]\n", f"  mov rax, qword ptr [rsp + {base + 8 * k}]\n") for k in (3, 2, 1, 0)])


# (what is changed, the contract changed, what the verifier then says)
CONTRACTS = [
    ("a and b are said exchanged", once(ENS, f"parent(kf.key, kf.flags, {P.format('b')}, {P.format('a')})"), FOLLOW),
    ("the first compression alone is said", once(ENS, P.format("a")), WORD),
    ("6431 bytes of stack are said", once("stack 6432", "stack 6431"), STACK),
]
# (what is changed, the source changed, what the verifier then says)
SOURCES = [
    ("lane 1 reads a", once("  mov rax, rdx\n  mov qword ptr [rsp + 8], rax\n", "  mov rax, rsi\n  mov qword ptr [rsp + 8], rax\n"), FOLLOW),
    ("the second round reads from the second value on", once("  lea rax, [rsp + 256]\n", "  lea rax, [rsp + 288]\n"), FOLLOW),
    ("PARENT is not in the second round's flags", last("  or rax, 1073741828\n", "  or rax, 1073741824\n"), FOLLOW),
    ("the last lane's cell of the table is not written in the first round", once("  mov rax, rsi\n  mov qword ptr [rsp + 248], rax\n", ""), LANE),
    ("the first round writes over the table", once("  lea r9, [rsp + 256]\n", "  lea r9, [rsp + 128]\n"), FRAME),
    ("out is the first value of the first round", out_from(256), WORD),
]
# Changed so that what is stated is still true: (what is changed, the source changed, the contract changed).
STILL_TRUE = [
    ("lane 17 reads b: what it leaves is not used", once("  mov rax, rsi\n  mov qword ptr [rsp + 136], rax\n", "  mov rax, rdx\n  mov qword ptr [rsp + 136], rax\n"), lambda t: t),
    ("6440 bytes of stack are said", lambda t: t, once("stack 6432", "stack 6440")),
]


def spec_text(change=lambda t: t):
    with open(os.path.join(KCHECK, "blake3.spec")) as f: text = f.read()
    for folder, name in (("kernel", "p32.contract"), ("quad", "quad32.contract")):
        with open(os.path.join(HERE, "examples", folder, name)) as f: text += "\n" + f.read()
    return change(text)


def found(functions, change=lambda t: t):
    """What the prover finds for `ode_quad32`, given the kernel's kept proof: the lines after the function's
    name, or the verifier's last word where the prover has nothing more to write."""
    with tempfile.TemporaryDirectory() as d:
        statement_path = os.path.join(d, "statement")
        with open(statement_path, "w") as f: f.write("\n".join(statement.statement(spec_text(change), functions)) + "\n")
        with open(os.path.join(HERE, "proofs", P32 + ".proof")) as f: kept = f.read().rstrip("\n").split("\n")
        p = prove.Prover(statement_path, kept + [f"for {NAME}"], os.path.join(d, "proof"), [], until=time.time() + 120)
        p.last = ""
        try: lines = p.solve([])
        finally: p.close()
        if lines is not None: return lines
        said = [l for l in p.last.split("\n") if l.startswith(("refused:", "need "))]
        return said[0] if said else p.last


class Statement(unittest.TestCase):
    def test_the_statement_gives_the_kernels_files_data_once(self):
        lines = statement.statement(spec_text(), FUNCTIONS)
        at = lines.index(f"fn {NAME}")
        kernel = lines.index(f"fn {P32}")
        self.assertGreater(at, kernel)                                          # after the function it calls
        self.assertEqual(len([l for l in lines[at + 1:] if l.startswith("i ")]), 133)
        # the one file with data is the kernel's: one section of code and constants, on a boundary of 64 bytes
        (piece,) = [l for l in lines if l.startswith("piece ")]
        self.assertEqual((lines.index(piece), piece.split()[1], len(piece.split()[2]) // 2), (0, "64", 17856))
        self.assertEqual([k for k, l in enumerate(lines) if l.startswith("data ")], [kernel + 1])
        self.assertEqual(lines[kernel + 1], "data 0")
        # what is to be shown of the function is, line for line, what `ode_quad` has (test_quad.py tests what its
        # `ensures` line means), but for the stack
        import test_quad
        quad = statement.statement(test_quad.spec_text(), test_quad.FUNCTIONS)
        mine = [l for l in lines[at + 1:] if not l.startswith(("i ", "def "))]
        theirs = [l for l in quad[quad.index("fn ode_quad") + 1:] if not l.startswith(("i ", "def "))]
        self.assertEqual(mine[:-1], theirs[:-1])
        self.assertEqual((mine[-1], theirs[-1]), ("stack 6432", "stack 5280"))
        self.assertTrue(any(l.startswith("ensuresw out ") for l in mine))
        # the kernel: a table of thirty-two addresses, and one line for each lane's part of the run
        self.assertIn("lanes inputs n", lines[kernel + 1:at])
        self.assertEqual(len([l for l in lines[kernel + 1:at] if l.startswith("ensuresw out ")]), 32)


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Verify(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.dir = tempfile.mkdtemp(prefix="odequad32-")
        with open(os.path.join(QUAD, "quad32.ode")) as f: cls.source = f.read()
    @classmethod
    def tearDownClass(cls): shutil.rmtree(cls.dir)

    def kept(self):
        """The kept proofs of the kernel and of the function, in one file."""
        path = os.path.join(self.dir, "kept.proof")
        with open(path, "w") as out:
            for symbol in (P32, NAME):
                with open(os.path.join(HERE, "proofs", symbol + ".proof")) as f: out.write(f.read())
        return path

    def changed(self, change):
        """The function with its source changed, as an object file."""
        src, obj = os.path.join(self.dir, "changed.ode"), os.path.join(self.dir, "changed.o")
        with open(src, "w") as f: f.write(change(self.source))
        odec.build(src, "quad32", obj)
        return [FUNCTIONS[0], (obj, NAME)]

    def test_the_example_is_made_from_its_source(self):
        odec.build(os.path.join(QUAD, "quad32.ode"), "quad32", os.path.join(self.dir, "made.o"))
        with open(os.path.join(self.dir, "made.o"), "rb") as f, open(FUNCTIONS[1][0], "rb") as g: self.assertEqual(f.read(), g.read())

    def test_the_function_is_shown_with_the_kernel_it_calls(self):
        self.assertEqual(lean_verify.verify(spec_text(), FUNCTIONS, self.kept()), (True, "shown"))
        # the prover finds the kept proof again: the function's name alone
        self.assertEqual(found(FUNCTIONS), [])
        with open(os.path.join(HERE, "proofs", NAME + ".proof")) as f: self.assertEqual(f.read(), f"for {NAME}\n")
        # control: the kernel is not left out of what is to be shown
        with self.assertRaises(SystemExit) as e: lean_verify.verify(spec_text(), FUNCTIONS[1:], self.kept())
        self.assertIn("which is not among the functions to be shown", str(e.exception))

    def test_a_contract_changed_in_one_place(self):
        for what, change, why in CONTRACTS:
            with self.subTest(what=what):
                self.assertFalse(lean_verify.verify(spec_text(change), FUNCTIONS, self.kept())[0], what)
                self.assertEqual(found(FUNCTIONS, change), why, what)

    def test_a_function_changed_in_one_place(self):
        for what, change, why in SOURCES:
            with self.subTest(what=what):
                functions = self.changed(change)
                self.assertFalse(lean_verify.verify(spec_text(), functions, self.kept())[0], what)
                self.assertEqual(found(functions), why, what)

    def test_changed_and_still_true(self):
        for what, source, contract in STILL_TRUE:
            with self.subTest(what=what):
                self.assertEqual(found(self.changed(source), contract), [], what)

    def test_the_statements_data(self):
        """The kept proofs show the statement as statement.py writes it. Without the kernel's `data` line the
        address of its table is refused, in the kernel; without the file's data that line names nothing."""
        lines = statement.statement(spec_text(), FUNCTIONS)
        def said(changed):
            path = os.path.join(self.dir, "lines.statement")
            with open(path, "w") as f: f.write("".join(l + "\n" for l in changed))
            r = subprocess.run([prove.EXE, prove.TABLE, path, self.kept()], capture_output=True, text=True)
            self.assertEqual(r.returncode == 0, r.stdout == "shown\n", r.stdout[:200])
            return r.stdout.rstrip()
        self.assertEqual(said(lines), "shown")
        d = lines.index("data 0")
        without = said(lines[:d] + lines[d + 1:])
        self.assertIn(NOT_IN_DATA, without)
        self.assertTrue(without.endswith("in " + P32), without[-80:])
        self.assertIn(NO_PIECE, said(lines[1:]))


if __name__ == "__main__":
    unittest.main()
