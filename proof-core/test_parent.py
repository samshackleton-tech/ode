#!/usr/bin/env python3
"""A part of the stack frame handed to a called function to WRITE: `ode_parent` (examples/parent) makes
a parent node of two blocks. Its block of 64 bytes is in its stack frame. It sets the block to zeros,
has the one-block kernel compress `a` from the first half and `b` from the second (the kernel reads and
writes a half of the frame's block), and then compresses the frame's block into `out`:

    ensures out = compress(out, compress(zero_cv(), a, counter(0), 64, 0) ++ compress(zero_cv(), b, counter(0), 64, 0), counter(0), 64, 0)

    python3 test_parent.py        (needs Lean's `lake`; the tests are skipped where it is not installed)

What the verifier in Lean takes here that it refused before: a called function that reads and writes a
run of words may be given a part of this function's stack frame, in whole 8-byte cells, each of them
known, at or above the stack pointer and below the address to return to (`symCallF'` in Core.lean; Lean
checks `symCallF'_sound`). After the call each word of the part is a new unknown, and two words make a
cell's number. A part of the frame that the called function reads must lie apart from the part it
writes. (A number kept in the frame across such a call, and a jump on it afterwards: test_turns.py.)

The function, its contract and the kept proof are shown; with the contract or the function changed in one
place, so that what is stated is false, nothing is shown, and each case names what the verifier then
refuses. One changed contract that is still true is shown."""
import os, shutil, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
KCHECK = os.path.join(HERE, "..", "kcheck")
sys.path.insert(0, HERE); sys.path.insert(0, KCHECK); sys.path.insert(0, os.path.join(HERE, "..", "lang"))
import built, lean_verify, odec, prove, statement

PARENT = os.path.join(HERE, "examples", "parent")
NAME, SSE41 = "ode_parent", "blake3_servil_compress_in_place_sse41"
FUNCTIONS = [(os.path.join(KCHECK, "b3hashr.o"), SSE41), (os.path.join(PARENT, "odeparent.o"), NAME)]
ENSURES = "compress(zero_cv(), a, counter(0), 64, 0) ++ compress(zero_cv(), b, counter(0), 64, 0)"
# Why the verifier refuses.
FOLLOW = "refused: the specification's words are not followed on the terms the function made"
NO_PART = "refused: a called function is given a run that is no part of a run this function was given to read"
KEEPS = "refused: at the return a register a callee keeps does not hold what it held at entry"
STACK = "refused: a call needs more stack than this function's contract allows"
# (what is changed, the text as it is, the text changed, what the verifier then says)
CONTRACTS = [
    ("a and b are exchanged", ENSURES, "compress(zero_cv(), b, counter(0), 64, 0) ++ compress(zero_cv(), a, counter(0), 64, 0)", FOLLOW),
    ("the second value is said twice", ENSURES, "compress(zero_cv(), b, counter(0), 64, 0) ++ compress(zero_cv(), b, counter(0), 64, 0)", FOLLOW),
    ("the stack is said to be 95 bytes", "stack 96", "stack 95", STACK),
]
# (what is changed, the source as it is, the source changed, what the verifier then says)
SOURCES = [
    ("one cell of the block is not set to zero", "  mov qword ptr [rsp + 24], rax\n", "", FOLLOW),
    ("the second value is written four bytes early: it overlaps the first", "  lea rdi, [rsp + 32]\n", "  lea rdi, [rsp + 28]\n", NO_PART),
    ("the second value is written eight bytes late: over a saved register", "  lea rdi, [rsp + 32]\n", "  lea rdi, [rsp + 40]\n", KEEPS),
    ("the second call is given the first block again", "  mov rsi, r12\n", "  mov rsi, rbp\n", FOLLOW),
    ("the block is read from eight bytes on: a saved register at its end", "  lea rsi, [rsp + 0]\n", "  lea rsi, [rsp + 8]\n", NO_PART),
]
# Changed contracts that are still true: (what is changed, the text as it is, the text changed).
STILL_TRUE = [
    ("the stack is said to be 104 bytes", "stack 96", "stack 104"),
]


def spec_text(change=lambda t: t):
    with open(os.path.join(KCHECK, "blake3.spec")) as f: text = f.read()
    for folder, name in (("kernel", "kernel_sse41.contract"), ("parent", "parent.contract")):
        with open(os.path.join(HERE, "examples", folder, name)) as f: text += "\n" + f.read()
    return change(text)


def once(old, new):
    def change(text):
        assert text.count(old) == 1, (old, text.count(old))
        return text.replace(old, new)
    return change


def last_word(functions, change=lambda t: t):
    """What the verifier says at last of the functions [(object, symbol)] with the proof that the prover
    writes for them: `shown`, or its last word where the prover has nothing more to write."""
    with tempfile.TemporaryDirectory() as d:
        try: prove.prove(spec_text(change), [(obj, symbol, "") for obj, symbol in functions], os.path.join(d, "statement"), os.path.join(d, "proof"))
        except SystemExit as e:
            lines = [l for l in str(e).split("\n") if l.startswith(("refused:", "need "))]
            return lines[0] if lines else str(e)
        return "shown"


class Statement(unittest.TestCase):
    def test_the_contract_in_the_accounts_terms(self):
        lines = statement.statement(spec_text(), FUNCTIONS)
        at = lines.index(f"fn {NAME}")
        self.assertGreater(at, lines.index(f"fn {SSE41}"))                      # after the function it calls
        mine = [l for l in lines[at + 1:] if not l.startswith(("i ", "def "))]
        self.assertEqual(mine[:3], ["arg out inout 32", "arg a fixed 64", "arg b fixed 64"])
        self.assertEqual(mine[-1], "stack 96")
        self.assertEqual(len([l for l in lines[at + 1:] if l.startswith("i ")]), 39)


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Meaning(unittest.TestCase):
    def test_the_ensures_says_the_parent_of_the_two_blocks(self):
        """The statement's `ensures` line, worked out by the account in Lean on bytes drawn at random, is what
        ../kcheck/ode.py works out of the expression written out here. (Control: with the two blocks
        exchanged ode.py gives another value.)"""
        import ensures_meaning as meaning, ode, random
        with open(os.path.join(KCHECK, "blake3.spec")) as f: spec = ode.Spec(f.read())
        line = meaning.ensures(spec_text(), FUNCTIONS, NAME, "out")
        inner = lambda x: ("call", "compress", [("call", "words", [("name", "z")]), ("call", "words", [("name", x)]), ("call", "counter", [("num", 0)]), ("num", 64), ("num", 0)])
        use = ("call", "bytes_of", [("call", "compress", [("call", "words", [("name", "out")]), ("bin", "++", inner("a"), inner("b")), ("call", "counter", [("num", 0)]), ("num", 64), ("num", 0)])])
        value = lambda o, a, b: "bytes " + bytes(spec.eval(ode.Numbers(), use, {"out": list(o), "a": list(a), "b": list(b), "z": [0] * 32})).hex()
        rng = random.Random(66)
        rnd = lambda n: bytes(rng.randrange(256) for _ in range(n))
        cases = [(rnd(32), rnd(64), rnd(64)) for _ in range(4)]
        want = [value(o, a, b) for o, a, b in cases]
        self.assertNotEqual(value(cases[0][0], cases[0][2], cases[0][1]), want[0])
        self.assertEqual(meaning.account(spec_text(), FUNCTIONS, [(line, {"out": o, "a": a, "b": b}) for o, a, b in cases]), want)


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Verify(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.dir = tempfile.mkdtemp(prefix="odeparent-")
        with open(os.path.join(PARENT, "parent.ode")) as f: cls.source = f.read()
    @classmethod
    def tearDownClass(cls): shutil.rmtree(cls.dir)

    def kept(self, symbols=(SSE41, NAME)):
        """The kept proofs of these functions, in one file."""
        path = os.path.join(self.dir, "kept.proof")
        with open(path, "w") as out:
            for symbol in symbols:
                with open(os.path.join(HERE, "proofs", symbol + ".proof")) as f: out.write(f.read())
        return path

    def test_the_example_is_made_from_its_source(self):
        odec.build(os.path.join(PARENT, "parent.ode"), "parent", os.path.join(self.dir, "made.o"))
        with open(os.path.join(self.dir, "made.o"), "rb") as f, open(FUNCTIONS[1][0], "rb") as g: self.assertEqual(f.read(), g.read())

    def test_the_function_is_shown_with_the_kernel_it_calls(self):
        self.assertEqual(lean_verify.verify(spec_text(), FUNCTIONS, self.kept()), (True, "shown"))
        # the prover finds the kept proof again
        statement_path, proof_path = os.path.join(self.dir, "s"), os.path.join(self.dir, "p")
        prove.prove(spec_text(), [(obj, symbol, "") for obj, symbol in FUNCTIONS], statement_path, proof_path)
        with open(proof_path) as f: found = f.read()
        with open(os.path.join(HERE, "proofs", NAME + ".proof")) as f: kept = f.read()
        self.assertEqual(found[found.index("for " + NAME):], kept)
        # controls: the kernel is not taken as shown without its proof, nor left out of what is to be shown
        shown, said = lean_verify.verify(spec_text(), FUNCTIONS, self.kept((NAME,)))
        self.assertFalse(shown)
        self.assertEqual(said.split("\n")[-1], "in " + SSE41)
        with self.assertRaises(SystemExit) as e: lean_verify.verify(spec_text(), FUNCTIONS[1:], self.kept())
        self.assertIn("which is not among the functions to be shown", str(e.exception))

    def test_a_contract_changed_in_one_place(self):
        for what, old, new, why in CONTRACTS:
            with self.subTest(what=what):
                self.assertFalse(lean_verify.verify(spec_text(once(old, new)), FUNCTIONS, self.kept())[0], what)
                self.assertEqual(last_word(FUNCTIONS, once(old, new)), why, what)

    def test_a_function_changed_in_one_place(self):
        for what, old, new, why in SOURCES:
            with self.subTest(what=what):
                self.assertEqual(self.source.count(old), 1, old)
                src, obj = os.path.join(self.dir, "changed.ode"), os.path.join(self.dir, "changed.o")
                with open(src, "w") as f: f.write(self.source.replace(old, new))
                odec.build(src, "parent", obj)
                functions = [FUNCTIONS[0], (obj, NAME)]
                self.assertFalse(lean_verify.verify(spec_text(), functions, self.kept())[0], what)
                self.assertEqual(last_word(functions), why, what)

    def test_a_changed_contract_that_is_still_true_is_shown(self):
        for what, old, new in STILL_TRUE:
            with self.subTest(what=what):
                self.assertEqual(last_word(FUNCTIONS, once(old, new)), "shown", what)


if __name__ == "__main__":
    unittest.main()
