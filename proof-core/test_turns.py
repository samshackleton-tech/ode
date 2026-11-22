#!/usr/bin/env python3
"""A number kept in the stack frame across a call that writes another part of the frame: `ode_turns`
(examples/turns) makes the parent node of examples/parent with a loop. Its block of 64 bytes and the
loop's counter are in its stack frame. On each of two turns the one-block kernel is given a half of the
block to read and write; after that call the counter is read from the frame again, one is added, and
the loop's jump is taken on it:

    ensures out = compress(out, compress(zero_cv(), a, counter(0), 64, 0) ++ compress(zero_cv(), b, counter(0), 64, 0), counter(0), 64, 0)

    python3 test_turns.py        (needs Lean's `lake`; the tests are skipped where it is not installed)

What the verifier in Lean takes here that it refused before. The blocks `a` and `b` are hidden, so
nothing that can be observed of a run may depend on them, and a jump may be taken only on what is known
not to depend on them. A called function that is given a part of the frame to write may leave there
bytes that depend on a secret. The verifier used to forget, at such a call, of every cell of the frame
that it was known not to depend on a secret; so the jump on the counter was refused ("a jump on a flag
that may depend on a secret"), though the called function cannot write the counter's cell. Now only the
cells that do not lie apart from the part given are forgotten (`quietAtCall` and `callQuiet` in
Core.lean; Lean checks `callQuiet_sound`). The hash's upper functions keep counters and flags in the
frame across the wide kernels' calls in this way.

The function, its contract and the kept proof are shown; with the contract or the function changed in one
place, so that what is stated is false, nothing is shown, and each case names what the verifier then
refuses. Among them: a jump on a cell that the kernel wrote is still refused. Changed contracts and
functions that are still true are shown."""
import os, re, shutil, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
KCHECK = os.path.join(HERE, "..", "kcheck")
sys.path.insert(0, HERE); sys.path.insert(0, KCHECK); sys.path.insert(0, os.path.join(HERE, "..", "lang"))
import built, lean_verify, odec, prove, statement

TURNS = os.path.join(HERE, "examples", "turns")
NAME, SSE41 = "ode_turns", "blake3_servil_compress_in_place_sse41"
FUNCTIONS = [(os.path.join(KCHECK, "b3hashr.o"), SSE41), (os.path.join(TURNS, "odeturns.o"), NAME)]
ENSURES = "compress(zero_cv(), a, counter(0), 64, 0) ++ compress(zero_cv(), b, counter(0), 64, 0)"
# Why the verifier refuses, or what the prover cannot show.
FOLLOW = "refused: the specification's words are not followed on the terms the function made"
NO_CELLS = "refused: a called function is given to write what is not whole cells of this function's frame, each of them known"
NOTHING = "refused: a read of the frame where nothing was written"
SECRET = "refused: a jump on a flag that may depend on a secret: which instructions run would depend on it"
STACK = "refused: a call needs more stack than this function's contract allows"
ENTAIL = "need entail"            # a number is to be shown below its bound (here: that adding one to it does not pass 2^64), and it is not so
JUMP = "@done:\n  mov rax, qword ptr [rsp + {}]\n  cmp rax, 1\n  jb @skip\n  mov rax, rax\n@skip:\n"       # a jump on a cell of the frame, after the loop: one instruction more is run where the cell holds 1 or more
# (what is changed, the text as it is, the text changed, what the verifier then says)
CONTRACTS = [
    ("a and b are exchanged", ENSURES, "compress(zero_cv(), b, counter(0), 64, 0) ++ compress(zero_cv(), a, counter(0), 64, 0)", FOLLOW),
    ("the second value is said twice", ENSURES, "compress(zero_cv(), b, counter(0), 64, 0) ++ compress(zero_cv(), b, counter(0), 64, 0)", FOLLOW),
    ("the stack is said to be 111 bytes", "stack 112", "stack 111", STACK),
]
# (what is changed, [(the source as it is, the source changed, how often it stands there)], what the verifier then says)
SOURCES = [
    # the marks: what a called function wrote may depend on the hidden blocks
    ("a jump on the first cell that the kernel wrote", [("@done:\n", JUMP.format(0), 1)], SECRET),
    ("a jump on the fifth cell that the kernel wrote", [("@done:\n", JUMP.format(32), 1)], SECRET),
    # the counter's cell and the parts given to the kernel
    ("the counter is kept in the block's last cell, which the second call reads and writes",
     [("qword ptr [rsp + 64]", "qword ptr [rsp + 56]", 4)], ENTAIL),
    ("the counter overlaps the block's last four bytes", [("qword ptr [rsp + 64]", "qword ptr [rsp + 60]", 4)], NO_CELLS),
    ("the counter is not set to zero", [("  // i = 0\n  mov qword ptr [rsp + 64], rax\n", "", 1)], NOTHING),
    ("the loop goes on while i < 3: a third call is given the counter's cell and what lies above it", [("  cmp rax, 2\n", "  cmp rax, 3\n", 1)], NO_CELLS),
    ("the counter goes up by two: the second value is never made", [("  add rax, 1\n", "  add rax, 2\n", 1)], FOLLOW),
    ("one cell of the block is not set to zero", [("  mov qword ptr [rsp + 8], rax\n", "", 1)], NO_CELLS),
    # the values
    ("b is compressed on the first turn and a on the second", [("  jb @first\n", "  jae @first\n", 1)], FOLLOW),
    ("a is compressed on both turns", [("  mov rsi, r12\n", "  mov rsi, rbp\n", 1)], FOLLOW),
    ("each value is written 16 bytes after the one before: they overlap", [("  shl rax, 5\n", "  shl rax, 4\n", 1)], FOLLOW),
    ("the block is read from eight bytes on: the counter is at its end", [("  lea rsi, [rsp + 0]\n", "  lea rsi, [rsp + 8]\n", 1)], FOLLOW),
]
# Changed contracts that are still true: (what is changed, the text as it is, the text changed).
STILL_TRUE = [
    ("the stack is said to be 120 bytes", "stack 112", "stack 120"),
    ("what can be observed may depend on a", "    requires no_overlap(out, a, b)\n", "    requires no_overlap(out, a, b)\n    trace depends on a\n"),
]
# Changed functions that still meet the contract: (what is changed, [(as it is, changed, how often)]).
SOURCES_STILL_TRUE = [
    ("a jump on the counter after the loop: its cell lies apart from both halves", [("@done:\n", JUMP.format(64), 1)]),
    ("the counter is kept one cell further up", [("qword ptr [rsp + 64]", "qword ptr [rsp + 72]", 4)]),
]


def below(source):
    """The function with its block 16 bytes further up and the counter in the cell right below the block."""
    def move(m):
        n = int(m.group(1))
        return f"[rsp + {8 if n == 64 else n + 16}]"
    return re.sub(r"\[rsp \+ (\d+)\]", move, source)


def spec_text(change=lambda t: t):
    with open(os.path.join(KCHECK, "blake3.spec")) as f: text = f.read()
    for folder, name in (("kernel", "kernel_sse41.contract"), ("turns", "turns.contract")):
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
        self.assertEqual(mine[:6], ["arg out inout 32", "arg a fixed 64", "arg b fixed 64", "needs sse41", "hidden a", "hidden b"])
        self.assertEqual(mine[-1], "stack 112")
        self.assertEqual(len([l for l in lines[at + 1:] if l.startswith("i ")]), 46)


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
        rng = random.Random(67)
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
        cls.dir = tempfile.mkdtemp(prefix="odeturns-")
        with open(os.path.join(TURNS, "turns.ode")) as f: cls.source = f.read()
    @classmethod
    def tearDownClass(cls): shutil.rmtree(cls.dir)

    def kept(self, symbols=(SSE41, NAME)):
        """The kept proofs of these functions, in one file."""
        path = os.path.join(self.dir, "kept.proof")
        with open(path, "w") as out:
            for symbol in symbols:
                with open(os.path.join(HERE, "proofs", symbol + ".proof")) as f: out.write(f.read())
        return path

    def made(self, source):
        """The functions with `ode_turns` made from this source."""
        src, obj = os.path.join(self.dir, "changed.ode"), os.path.join(self.dir, "changed.o")
        with open(src, "w") as f: f.write(source)
        odec.build(src, "turns", obj)
        return [FUNCTIONS[0], (obj, NAME)]

    def changed(self, pairs):
        source = self.source
        for old, new, count in pairs:
            self.assertEqual(source.count(old), count, old)
            source = source.replace(old, new)
        return self.made(source)

    def test_the_example_is_made_from_its_source(self):
        odec.build(os.path.join(TURNS, "turns.ode"), "turns", os.path.join(self.dir, "made.o"))
        with open(os.path.join(self.dir, "made.o"), "rb") as f, open(FUNCTIONS[1][0], "rb") as g: self.assertEqual(f.read(), g.read())

    def test_the_function_is_shown_with_the_kernel_it_calls(self):
        self.assertEqual(lean_verify.verify(spec_text(), FUNCTIONS, self.kept()), (True, "shown"))
        # the prover finds the kept proof again: it is the function's name and nothing more (the two turns of
        # the loop are walked, and each jump is on a number the verifier holds)
        statement_path, proof_path = os.path.join(self.dir, "s"), os.path.join(self.dir, "p")
        prove.prove(spec_text(), [(obj, symbol, "") for obj, symbol in FUNCTIONS], statement_path, proof_path)
        with open(proof_path) as f: found = f.read()
        with open(os.path.join(HERE, "proofs", NAME + ".proof")) as f: kept = f.read()
        self.assertEqual(found[found.index("for " + NAME):], kept)
        self.assertEqual(kept, f"for {NAME}\n")
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
        for what, pairs, why in SOURCES:
            with self.subTest(what=what):
                functions = self.changed(pairs)
                self.assertFalse(lean_verify.verify(spec_text(), functions, self.kept())[0], what)
                self.assertEqual(last_word(functions), why, what)

    def test_a_changed_contract_that_is_still_true_is_shown(self):
        for what, old, new in STILL_TRUE:
            with self.subTest(what=what):
                self.assertEqual(last_word(FUNCTIONS, once(old, new)), "shown", what)

    def test_a_changed_function_that_still_meets_the_contract_is_shown(self):
        for what, pairs in SOURCES_STILL_TRUE:
            with self.subTest(what=what):
                self.assertEqual(last_word(self.changed(pairs)), "shown", what)

    def test_the_counter_in_the_cell_right_below_the_block(self):
        """The same function with the block 16 bytes further up and the counter in the cell right below it
        is shown; a jump there on a cell that the kernel wrote is refused, and one on the counter is not."""
        source = below(self.source)
        self.assertIn("  mov qword ptr [rsp + 8], rax\n  // while i < 2\n", source)       # i = 0, now in the cell at 8
        self.assertIn("  lea rdi, [rsp + 16]\n", source)
        self.assertEqual(last_word(self.made(source)), "shown")
        jump = lambda cell: source.replace("@done:\n", JUMP.format(cell))
        self.assertEqual(last_word(self.made(jump(16))), SECRET)
        self.assertEqual(last_word(self.made(jump(72))), SECRET)
        self.assertEqual(last_word(self.made(jump(8))), "shown")


if __name__ == "__main__":
    unittest.main()
