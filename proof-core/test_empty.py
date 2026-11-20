#!/usr/bin/env python3
"""A part of the stack frame handed to a called function to read: `ode_empty` (examples/empty) works out
the root node of the empty message. BLAKE3 hashes a message of no bytes by one compression of a block of
sixty-four zero bytes. The function makes that block in its own stack frame, by eight stores of the
number 0, and gives the one-block kernel its address:

    def zero_block() { [word(0) for i in 0..16] }
    ensures out = compress(out, zero_block(), counter(0), 0, 11)

    python3 test_empty.py        (needs Lean's `lake`; the tests are skipped where it is not installed)

What the verifier in Lean takes here that it refused before: a called function that reads a run of a
fixed count may be given a part of this function's stack frame. The verifier holds what the frame's
8-byte cells are. A word of the frame is a half of a cell: the cell's number modulo 2^32, or its
quotient by 2^32. The part must lie at or above the stack pointer and below the address to return to, in
whole cells, each of them known. (Lean checks the theorem for it: `frameRun_sound` in SoundFrame.lean, and
the frame's case in `symCallW'_sound`.) A part of the frame given to a called function to WRITE is not
here yet.

The function, its contract and the kept proof are shown; with the contract or the function changed in one
place, so that what is stated is false, nothing is shown, and each case names what the verifier then
refuses. One changed contract that is still true is shown."""
import os, shutil, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
KCHECK = os.path.join(HERE, "..", "kcheck")
sys.path.insert(0, HERE); sys.path.insert(0, KCHECK); sys.path.insert(0, os.path.join(HERE, "..", "lang"))
import built, lean_verify, odec, prove, statement

EMPTY = os.path.join(HERE, "examples", "empty")
NAME, SSE41 = "ode_empty", "blake3_servil_compress_in_place_sse41"
FUNCTIONS = [(os.path.join(KCHECK, "b3hashr.o"), SSE41), (os.path.join(EMPTY, "odeempty.o"), NAME)]
CONTRACT = ["arg out inout 32", "needs sse41",
            "ensuresw out (call bytes_of (call compress (call words (name out)) (call zero_block) (call counter (num 0)) (num 0) (num 11)))",
            "stack 72"]
# Why the verifier refuses.
FOLLOW = "refused: the specification's words are not followed on the terms the function made"
NO_PART = "refused: a called function is given a run that is no part of a run this function was given to read"
STACK = "refused: a call needs more stack than this function's contract allows"
BLOCK = "def zero_block() { [word(0) for i in 0..16] }"
# (what is changed, the text as it is, the text changed, what the verifier then says)
CONTRACTS = [
    ("the flags are said to be 3: the root flag is left out", "counter(0), 0, 11)", "counter(0), 0, 3)", FOLLOW),
    ("the block length is said to be 64", "counter(0), 0, 11)", "counter(0), 64, 11)", FOLLOW),
    ("the counter 1 is said", "counter(0), 0, 11)", "counter(1), 0, 11)", FOLLOW),
    ("the block's last word is said to be 1", BLOCK, "def zero_block() { [word(0) for i in 0..15] ++ [word(1)] }", FOLLOW),
    ("the stack is said to be 71 bytes", "stack 72", "stack 71", STACK),
]
# (what is changed, the source as it is, the source changed, what the verifier then says)
SOURCES = [
    ("one cell of the block is not set to zero: the kernel would read what the frame held", "  mov qword ptr [rsp + 24], rax\n", "", NO_PART),
    ("one cell of the block is set to 1", "  mov qword ptr [rsp + 8], rax\n", "  mov rcx, 1\n  mov qword ptr [rsp + 8], rcx\n", FOLLOW),
    ("the kernel is given the block from eight bytes on: its end is the address to return to", "  lea rsi, [rsp + 0]\n", "  lea rsi, [rsp + 8]\n", NO_PART),
    ("the kernel is given the flags 3", "  mov r8, 11\n", "  mov r8, 3\n", FOLLOW),
    ("the kernel is given the block length 64", "  mov rdx, 0\n", "  mov rdx, 64\n", FOLLOW),
]
# Changed contracts that are still true: (what is changed, the text as it is, the text changed).
STILL_TRUE = [
    ("the stack is said to be 80 bytes", "stack 72", "stack 80"),
]
# BLAKE3's eight constants, as the bytes of a chaining value, and its hash of the empty message.
IV = b"".join(w.to_bytes(4, "little") for w in (0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19))
EMPTY_HASH = "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"


def spec_text(change=lambda t: t):
    with open(os.path.join(KCHECK, "blake3.spec")) as f: text = f.read()
    for folder, name in (("kernel", "kernel_sse41.contract"), ("empty", "empty.contract")):
        with open(os.path.join(HERE, "examples", folder, name)) as f: text += "\n" + f.read()
    return change(text)


def once(old, new):
    def change(text):
        assert text.count(old) == 1, (old, text.count(old))
        return text.replace(old, new)
    return change


def last_word(functions, change=lambda t: t):
    """What the verifier says at last of the functions [(object, symbol)], the prover answering what it asks
    for: `shown`, or the word the prover has no answer to."""
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
        self.assertEqual(mine, CONTRACT)
        self.assertEqual(len([l for l in lines[at + 1:] if l.startswith("i ")]), 17)


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Meaning(unittest.TestCase):
    def test_the_ensures_says_the_root_node_of_the_empty_message(self):
        """The statement's `ensures` line, worked out by the account in Lean on keys drawn at random: the
        compression of sixty-four zero bytes with the block length 0 and the flags 11, as ../kcheck/ode.py
        works out `compress` of a block written out here. From BLAKE3's own constants it is BLAKE3's hash
        of the empty message. (Control: with the flags 3 ode.py gives another value.)"""
        import ensures_meaning as meaning, ode, random
        with open(os.path.join(KCHECK, "blake3.spec")) as f: spec = ode.Spec(f.read())
        line = meaning.ensures(spec_text(), FUNCTIONS, NAME, "out")
        use = lambda flags: ("call", "bytes_of", [("call", "compress", [("call", "words", [("name", "h")]), ("call", "words", [("name", "b")]),
                                                                       ("call", "counter", [("num", 0)]), ("num", 0), ("num", flags)])])
        value = lambda h, flags=11: "bytes " + bytes(spec.eval(ode.Numbers(), use(flags), {"h": list(h), "b": [0] * 64})).hex()
        rng = random.Random(65)
        keys = [IV] + [bytes(rng.randrange(256) for _ in range(32)) for _ in range(4)]
        want = [value(h) for h in keys]
        self.assertEqual(want[0], "bytes " + EMPTY_HASH)
        self.assertNotEqual(value(IV, 3), want[0])
        self.assertEqual(meaning.account(spec_text(), FUNCTIONS, [(line, {"out": h}) for h in keys]), want)


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Verify(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.dir = tempfile.mkdtemp(prefix="odeempty-")
        with open(os.path.join(EMPTY, "empty.ode")) as f: cls.source = f.read()
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
        odec.build(os.path.join(EMPTY, "empty.ode"), "empty", os.path.join(self.dir, "made.o"))
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
                odec.build(src, "empty", obj)
                functions = [FUNCTIONS[0], (obj, NAME)]
                self.assertFalse(lean_verify.verify(spec_text(), functions, self.kept())[0], what)
                self.assertEqual(last_word(functions), why, what)

    def test_a_changed_contract_that_is_still_true_is_shown(self):
        for what, old, new in STILL_TRUE:
            with self.subTest(what=what):
                self.assertEqual(last_word(FUNCTIONS, once(old, new)), "shown", what)


if __name__ == "__main__":
    unittest.main()
