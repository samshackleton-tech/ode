#!/usr/bin/env python3
"""The specification's `the greatest power of two` is followed: `ode_left_block` (examples/left) compresses
the last block of the left part of a message of 2049 to 4096 bytes, and its contract says where that block
lies by ../kcheck/blake3.spec's own `left_chunks`:

    def left_chunks(bytes) { the greatest power of two k with 1024 * k < len(bytes) }
    ensures h = compress(h, words(input[1024 * left_chunks(input) - 64 .. 1024 * left_chunks(input)]), counter(0), 64, 0)

    python3 test_left.py        (needs Lean's `lake`; the tests are skipped where it is not installed)

What the verifier in Lean takes here that it refused before: `the greatest power of two x with cond` (or
the least), on the terms the function made. As the account has it, the sixty-four powers of two are gone
through from the greatest down; the value is the first of which the condition is true, the condition
being false of every one before. Each of those comparisons is seen at once here from one known fact:
`len <= 4096` says it of the powers from 4 up, and `len >= 2049` of the power 2. (Where no one fact says
it, the proof file names the inequality in a row, and the verifier shows it first: test_split.py.)

The function, its contract and the kept proof are shown; with the contract, the definition or the function
changed in one place, so that what is stated is false, nothing is shown, and each case names what the
verifier then refuses or what it lacks. Two changed contracts that are still true are shown."""
import os, shutil, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
KCHECK = os.path.join(HERE, "..", "kcheck")
sys.path.insert(0, HERE); sys.path.insert(0, KCHECK); sys.path.insert(0, os.path.join(HERE, "..", "lang"))
import built, lean_verify, odec, prove, statement

LEFT = os.path.join(HERE, "examples", "left")
NAME, SSE41 = "ode_left_block", "blake3_servil_compress_in_place_sse41"
FUNCTIONS = [(os.path.join(KCHECK, "b3hashr.o"), SSE41), (os.path.join(LEFT, "odeleft.o"), NAME)]
CONTRACT = ["arg h inout 32", "arg input bytes len", "arg len number", "needs sse41", "atleast len 2049", "below len 4097", "hidden input", "hidden len",
            "ensuresw h (call bytes_of (call compress (call words (name h)) (call words (slice (name input) "
            "(bin - (bin * (num 1024) (call left_chunks (name input))) (num 64)) (bin * (num 1024) (call left_chunks (name input))))) "
            "(call counter (num 0)) (num 64) (num 0)))",
            "stack 64"]
# Why the verifier refuses, or what the prover cannot give it.
FOLLOW = "refused: the specification's words are not followed on the terms the function made"
ARGS = "refused: what a called function's contract says of its arguments is not followed"
ENTAIL = "need entail"            # an address is to be shown not to pass 2^64, a number to be below its bound, or a part given to a
                                  # called function to lie within the run it is a part of, and it is not so
KNOW = "need know"                # the proof file has run out before an `ensures` or a call, and of the rows that the prover
                                  # would name there (that a part lies within its run; how two numbers compare) none is shown
DEFINITION = "def left_chunks(bytes) { the greatest power of two k with 1024 * k < len(bytes) }"
# (what is changed, the text as it is, the text changed, what the verifier then says)
CONTRACTS = [
    ("the message may have 2048 bytes: its left part is then one chunk", "len >= 2049", "len >= 2048", KNOW),
    ("the message may have 4097 bytes: its left part is then four chunks", "len <= 4096", "len <= 4097", KNOW),
    ("nothing is asked of the message's length from below", "    requires len >= 2049\n", "", ENTAIL),
    ("nothing is asked of the message's length from above", "    requires len <= 4096\n", "", KNOW),
    ("the block before the last is said", "input[1024 * left_chunks(input) - 64 .. 1024 * left_chunks(input)]",
     "input[1024 * left_chunks(input) - 128 .. 1024 * left_chunks(input) - 64]", FOLLOW),
    ("the right part's first block is said", "input[1024 * left_chunks(input) - 64 .. 1024 * left_chunks(input)]",
     "input[1024 * left_chunks(input) .. 1024 * left_chunks(input) + 64]", KNOW),
    ("the counter 1 is said", "counter(0), 64, 0)\n    stack 64", "counter(1), 64, 0)\n    stack 64", FOLLOW),
    ("the definition: the least power of two", DEFINITION, "def left_chunks(bytes) { the least power of two k with 1024 * k < len(bytes) }", FOLLOW),
    ("the definition: a left part may be the whole message", DEFINITION, "def left_chunks(bytes) { the greatest power of two k with 1024 * k <= len(bytes) }", KNOW),
    ("the definition: chunks of 2048 bytes", DEFINITION, "def left_chunks(bytes) { the greatest power of two k with 2048 * k < len(bytes) }", FOLLOW),
]
# (what is changed, the source as it is, the source changed, what the verifier then says)
SOURCES = [
    ("the kernel is given the block before", "  add rsi, 1984\n", "  add rsi, 1920\n", FOLLOW),
    ("the kernel is given the first chunk's last block", "  add rsi, 1984\n", "  add rsi, 960\n", FOLLOW),
    ("the kernel is given the fourth chunk's last block, which a shorter message does not have", "  add rsi, 1984\n", "  add rsi, 4032\n", ENTAIL),
    ("the kernel is given the bytes from 1985 on", "  add rsi, 1984\n", "  add rsi, 1985\n", ARGS),
    ("the kernel is given the block length 32", "  mov rdx, 64\n", "  mov rdx, 32\n", FOLLOW),
    ("the kernel is given the flag 1", "  mov r8, 0\n", "  mov r8, 1\n", FOLLOW),
]
# Changed contracts that are still true: (what is changed, the text as it is, the text changed).
STILL_TRUE = [
    ("the message has at most 4000 bytes", "len <= 4096", "len <= 4000"),
    ("the message has at least 3000 bytes", "len >= 2049", "len >= 3000"),
]


def spec_text(change=lambda t: t):
    with open(os.path.join(KCHECK, "blake3.spec")) as f: text = f.read()
    for folder, name in (("kernel", "kernel_sse41.contract"), ("left", "left.contract")):
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
        self.assertEqual(mine, CONTRACT)
        self.assertEqual(len([l for l in lines[at + 1:] if l.startswith("i ")]), 8)


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Meaning(unittest.TestCase):
    def test_the_ensures_says_the_compression_of_the_left_parts_last_block(self):
        """The statement's `ensures` line, worked out by the account in Lean on bytes drawn at random: for
        2049 to 4096 bytes, the compression of the message's bytes 1984 to 2048, as ../kcheck/ode.py works
        out `compress`. (Controls: for 2048 bytes, for 4097 and for two more lengths the same line gives
        another block's, the left part then being one chunk, four, one and eight.)"""
        import ensures_meaning as meaning, ode, random
        with open(os.path.join(KCHECK, "blake3.spec")) as f: spec = ode.Spec(f.read())
        line = meaning.ensures(spec_text(), FUNCTIONS, NAME, "h")
        use = ("call", "bytes_of", [("call", "compress", [("call", "words", [("name", "h")]), ("call", "words", [("name", "b")]), ("call", "counter", [("num", 0)]), ("num", 64), ("num", 0)])])
        rng = random.Random(62)
        value = lambda h, block: "bytes " + bytes(spec.eval(ode.Numbers(), use, {"h": list(h), "b": list(block)})).hex()
        cases, want = [], []
        for n, last in ((2049, 2048), (2050, 2048), (3000, 2048), (4095, 2048), (4096, 2048), (2048, 1024), (4097, 4096), (1025, 1024), (9000, 8192)):
            h, message = bytes(rng.randrange(256) for _ in range(32)), bytes(rng.randrange(256) for _ in range(n))
            cases.append((line, {"h": h, "input": message, "len": n}))
            want.append(value(h, message[last - 64:last]))
            if last != 2048 and n >= 2048: self.assertNotEqual(want[-1], value(h, message[1984:2048]))
        self.assertEqual(meaning.account(spec_text(), FUNCTIONS, cases), want)


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Verify(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.dir = tempfile.mkdtemp(prefix="odeleft-")
        with open(os.path.join(LEFT, "left.ode")) as f: cls.source = f.read()
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
        odec.build(os.path.join(LEFT, "left.ode"), "left_block", os.path.join(self.dir, "made.o"))
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

    def test_a_changed_proof_is_refused(self):
        with open(os.path.join(HERE, "proofs", NAME + ".proof")) as f: lines = f.read().split("\n")[:-1]
        self.assertGreater(len(lines), 2)
        for k in range(1, len(lines)):
            with self.subTest(left_out=lines[k]):
                path = os.path.join(self.dir, "changed.proof")
                with open(path, "w") as out:
                    with open(os.path.join(HERE, "proofs", SSE41 + ".proof")) as f: out.write(f.read())
                    out.write("\n".join(lines[:k] + lines[k + 1:]) + "\n")
                self.assertFalse(lean_verify.verify(spec_text(), FUNCTIONS, path)[0])

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
                odec.build(src, "left_block", obj)
                functions = [FUNCTIONS[0], (obj, NAME)]
                self.assertFalse(lean_verify.verify(spec_text(), functions, self.kept())[0], what)
                self.assertEqual(last_word(functions), why, what)

    def test_a_changed_contract_that_is_still_true_is_shown(self):
        for what, old, new in STILL_TRUE:
            with self.subTest(what=what):
                self.assertEqual(last_word(FUNCTIONS, once(old, new)), "shown", what)


if __name__ == "__main__":
    unittest.main()
