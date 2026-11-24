#!/usr/bin/env python3
"""The way the hash's `b3l_take` and `b3l_subtree` find where a message splits, shown for a message of
any length from 1025 bytes on: `ode_left_last` (examples/doubling) works out the count of chunks
c = ((len - 1) >> 10) + 1, lets k take the value of its double while the double is below c, and
compresses the 64 bytes that end the first k chunks. Its contract says where those bytes lie by
../kcheck/blake3.spec's own `left_chunks`:

    def left_chunks(bytes) { the greatest power of two k with 1024 * k < len(bytes) }
    ensures h = compress(h, words(input[1024 * left_chunks(input) - 64 .. 1024 * left_chunks(input)]), counter(0), 64, 0)

    python3 test_doubling.py        (needs Lean's `lake`; the tests are skipped where it is not installed)

The loop has no invariant. The verifier walks it: one path for each of the fifty-four counts the left
part can have (1, 2, 4, ... 2^53 chunks). On each path the specification's definition is to be worked out:
of the sixty-four powers of two, which are too great for the message? No one known fact says it; the
proof file names the inequalities that say it, in rows (see test_split.py). The prover names the middle
one of the powers not yet decided, since a row about one power says it of all the greater ones, or of all
the lesser. The kept proof has two to seven rows a path.

The function, its contract and the kept proof are shown; with the contract, the definition or the function
changed in one place, so that what is stated is false, nothing is shown, and each case names what the
verifier then refuses or what the prover cannot give it. Two changed contracts that are still true are
shown. (On the path of the greatest count the function adds 2^63 to the message's address. The verifier
took a number from 2^63 on as a negative one, and the function was shown only with the length bounded
by 2^63; now it takes 2^63 as it stands: test_far.py.)"""
import os, shutil, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
KCHECK = os.path.join(HERE, "..", "kcheck")
sys.path.insert(0, HERE); sys.path.insert(0, KCHECK); sys.path.insert(0, os.path.join(HERE, "..", "lang"))
import built, lean_verify, odec, prove, statement

DOUBLING = os.path.join(HERE, "examples", "doubling")
NAME, SSE41 = "ode_left_last", "blake3_servil_compress_in_place_sse41"
FUNCTIONS = [(os.path.join(KCHECK, "b3hashr.o"), SSE41), (os.path.join(DOUBLING, "odedoubling.o"), NAME)]
BLOCK = "input[1024 * left_chunks(input) - 64 .. 1024 * left_chunks(input)]"
CONTRACT = ["arg h inout 32", "arg input bytes len", "arg len number", "needs sse41", "atleast len 1025", "hidden input",
            "ensuresw h (call bytes_of (call compress (call words (name h)) (call words (slice (name input) "
            "(bin - (bin * (num 1024) (call left_chunks (name input))) (num 64)) (bin * (num 1024) (call left_chunks (name input))))) "
            "(call counter (num 0)) (num 64) (num 0)))",
            "stack 64"]
# Why the verifier refuses, or what the prover cannot give it.
FOLLOW = "refused: the specification's words are not followed on the terms the function made"
ENTAIL = "need entail"            # an address is to be shown not to pass 2^64, a number to be below its bound, or a part given to a
                                  # called function to lie within the run it is a part of, and it is not so
KNOW = "need know"                # the proof file has run out before an `ensures` or a call, and of the rows that the prover
                                  # would name there (that a part lies within its run; how two numbers compare) none is shown
DEFINITION = "def left_chunks(bytes) { the greatest power of two k with 1024 * k < len(bytes) }"


def turned(row):
    """The row that says the opposite: where `row` says c + a.x >= 0, it says -c - 1 - a.x >= 0."""
    numbers = [int(n) for n in row.split()[1:]]
    return "k " + " ".join(str(n) for n in [-numbers[0] - 1] + [-n for n in numbers[1:]])
JUMP = "refused: a jump on a flag that may depend on values kept out of the trace: which instructions run would depend on them"
# (what is changed, the text as it is, the text changed, what the verifier then says)
CONTRACTS = [
    # (refused before the specification is reached: the address of byte 1024 may then be 2^64)
    ("the message may have 1024 bytes: it is one chunk, and no power of two is its left part", "len >= 1025", "len >= 1024", ENTAIL),
    ("the block before the last is said", BLOCK, "input[1024 * left_chunks(input) - 128 .. 1024 * left_chunks(input) - 64]", FOLLOW),
    ("the right part's first block is said", BLOCK, "input[1024 * left_chunks(input) .. 1024 * left_chunks(input) + 64]", KNOW),
    ("the counter 1 is said", "counter(0), 64, 0)\n    trace depends on len", "counter(1), 64, 0)\n    trace depends on len", FOLLOW),
    ("the definition: the least power of two", DEFINITION, "def left_chunks(bytes) { the least power of two k with 1024 * k < len(bytes) }", FOLLOW),
    ("the definition: a left part may be the whole message", DEFINITION, "def left_chunks(bytes) { the greatest power of two k with 1024 * k <= len(bytes) }", KNOW),
    ("the definition: chunks of 2048 bytes", DEFINITION, "def left_chunks(bytes) { the greatest power of two k with 2048 * k < len(bytes) }", FOLLOW),
    # the trace: where the block is read is the length's to say
    ("the length is hidden", "    trace depends on len\n", "", JUMP),
]
# (what is changed, the source as it is, the source changed, what the verifier then says)
SOURCES = [
    ("the count of chunks is one too few", "  add rcx, 1\n", "", KNOW),
    ("two are taken from the length, not one: 2049 bytes are taken for two chunks", "  sub rcx, 1\n", "  sub rcx, 2\n", KNOW),
    ("the length is divided by 2048", "  shr rcx, 10\n", "  shr rcx, 11\n", FOLLOW),
    ("k starts at 2: the kernel is given bytes a message of two chunks does not have", "  mov r9, 1\n", "  mov r9, 2\n", ENTAIL),
    ("the double is doubled again: counts are passed over", "  shl rax, 1\n", "  shl rax, 2\n", KNOW),
    ("the count is taken for a count of half chunks", "  shl r9, 10\n", "  shl r9, 9\n", FOLLOW),
    ("the kernel is given the block before", "  sub rsi, 64\n", "  sub rsi, 128\n", FOLLOW),
    ("the kernel is given the block length 32", "  mov rdx, 64\n", "  mov rdx, 32\n", FOLLOW),
    ("the kernel is given the flag 1", "  mov r8, 0\n", "  mov r8, 1\n", FOLLOW),
]
# Changed contracts that are still true: (what is changed, the text as it is, the text changed).
STILL_TRUE = [
    ("the message has at most 4096 bytes", "    requires len >= 1025\n", "    requires len >= 1025\n    requires len <= 4096\n"),
    ("the message has at least 5000 bytes", "len >= 1025", "len >= 5000"),
]


def spec_text(change=lambda t: t):
    with open(os.path.join(KCHECK, "blake3.spec")) as f: text = f.read()
    for folder, name in (("kernel", "kernel_sse41.contract"), ("doubling", "doubling.contract")):
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
        self.assertEqual(len([l for l in lines[at + 1:] if l.startswith("i ")]), 21)


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Meaning(unittest.TestCase):
    def test_the_ensures_says_the_compression_of_the_left_parts_last_block(self):
        """The statement's `ensures` line, worked out by the account in Lean on bytes drawn at random: the
        compression of the 64 bytes that end the left part, as ../kcheck/ode.py works out `compress`: the
        left part of 1025 to 2048 bytes is one chunk, of 2049 to 4096 two, of 4097 four, of 9000 eight, of
        70000 sixty-four. (Control: each of them is another block than the one before.)"""
        import ensures_meaning as meaning, ode, random
        with open(os.path.join(KCHECK, "blake3.spec")) as f: spec = ode.Spec(f.read())
        line = meaning.ensures(spec_text(), FUNCTIONS, NAME, "h")
        use = ("call", "bytes_of", [("call", "compress", [("call", "words", [("name", "h")]), ("call", "words", [("name", "b")]), ("call", "counter", [("num", 0)]), ("num", 64), ("num", 0)])])
        rng = random.Random(64)
        value = lambda h, block: "bytes " + bytes(spec.eval(ode.Numbers(), use, {"h": list(h), "b": list(block)})).hex()
        cases, want, before = [], [], None
        for n, last in ((1025, 1024), (2048, 1024), (2049, 2048), (4096, 2048), (4097, 4096), (9000, 8192), (70000, 65536)):
            h, message = bytes(rng.randrange(256) for _ in range(32)), bytes(rng.randrange(256) for _ in range(n))
            cases.append((line, {"h": h, "input": message, "len": n}))
            want.append(value(h, message[last - 64:last]))
            if before is not None and before != last: self.assertNotEqual(want[-1], value(h, message[before - 64:before]))
            before = last
        self.assertEqual(meaning.account(spec_text(), FUNCTIONS, cases), want)


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Verify(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.dir = tempfile.mkdtemp(prefix="odedoubling-")
        with open(os.path.join(DOUBLING, "doubling.ode")) as f: cls.source = f.read()
        with open(os.path.join(HERE, "proofs", NAME + ".proof")) as f: cls.lines = f.read().split("\n")[:-1]
    @classmethod
    def tearDownClass(cls): shutil.rmtree(cls.dir)

    def kept(self, symbols=(SSE41, NAME)):
        """The kept proofs of these functions, in one file."""
        path = os.path.join(self.dir, "kept.proof")
        with open(path, "w") as out:
            for symbol in symbols:
                with open(os.path.join(HERE, "proofs", symbol + ".proof")) as f: out.write(f.read())
        return path

    def changed(self, lines):
        """The kernel's kept proof and these lines for the function, in one file."""
        path = os.path.join(self.dir, "changed.proof")
        with open(path, "w") as out:
            with open(os.path.join(HERE, "proofs", SSE41 + ".proof")) as f: out.write(f.read())
            out.write("\n".join(lines) + "\n")
        return path

    def test_the_example_is_made_from_its_source(self):
        odec.build(os.path.join(DOUBLING, "doubling.ode"), "left_last", os.path.join(self.dir, "made.o"))
        with open(os.path.join(self.dir, "made.o"), "rb") as f, open(FUNCTIONS[1][0], "rb") as g: self.assertEqual(f.read(), g.read())

    def test_the_function_is_shown_with_the_kernel_it_calls(self):
        self.assertEqual(lean_verify.verify(spec_text(), FUNCTIONS, self.kept()), (True, "shown"))
        # the prover finds the kept proof again
        statement_path, proof_path = os.path.join(self.dir, "s"), os.path.join(self.dir, "p")
        prove.prove(spec_text(), [(obj, symbol, "") for obj, symbol in FUNCTIONS], statement_path, proof_path)
        with open(proof_path) as f: found = f.read()
        self.assertEqual(found[found.index("for " + NAME):], "\n".join(self.lines) + "\n")
        # fifty-four ways out of the loop, and 293 rows, each about the length alone (the unknown 2: rdx at
        # entry). On each of the 53 ways with two chunks or more: one row before the call (the length is at
        # least 1024 * k: the block lies within the message) and one before the `ensures` (1024 * k is below
        # the length). The powers too great are said in 187 rows (`len <= 2^n`), up to five a way out,
        # where going from the greatest power down took about twenty-six. No row says anything else.
        rows = [[int(n) for n in l.split()[1:]] for l in self.lines if l.startswith("k ")]
        self.assertEqual({tuple(r[1:3]) for r in rows}, {(0, 0)})
        power = lambda n: n > 0 and n & (n - 1) == 0
        at_least = sorted(-r[0] for r in rows if r[3] == 1)                    # `len >= N`
        at_most = [r[0] for r in rows if r[3] == -1]                           # `len <= N`
        self.assertEqual(len(rows), len(at_least) + len(at_most))
        self.assertEqual([n for n in at_least if power(n)], [1024 << k for k in range(1, 54)])
        self.assertEqual([n for n in at_least if not power(n)], [(1024 << k) + 1 for k in range(1, 54)])
        self.assertEqual((len(at_most), all(power(n) for n in at_most)), (187, True))
        self.assertEqual((len(rows), self.lines.count("t next")), (293, 54))
        self.assertEqual([l for l in self.lines if l in ("t ge", "t lt")], [])
        # controls: the kernel is not taken as shown without its proof, nor left out of what is to be shown
        shown, said = lean_verify.verify(spec_text(), FUNCTIONS, self.kept((NAME,)))
        self.assertFalse(shown)
        self.assertEqual(said.split("\n")[-1], "in " + SSE41)
        with self.assertRaises(SystemExit) as e: lean_verify.verify(spec_text(), FUNCTIONS[1:], self.kept())
        self.assertIn("which is not among the functions to be shown", str(e.exception))

    def test_a_changed_proof_is_refused(self):
        """The kept proof with one line left out: every fiftieth line, and the last."""
        self.assertGreater(len(self.lines), 2000)
        for k in list(range(1, len(self.lines), 50)) + [len(self.lines) - 1]:
            with self.subTest(left_out=k):
                self.assertFalse(lean_verify.verify(spec_text(), FUNCTIONS, self.changed(self.lines[:k] + self.lines[k + 1:]))[0])

    def test_a_row_turned_round_is_refused(self):
        """The proof file names an inequality, and the verifier must show it from the known facts: the kept
        proof with one row turned round (a row that says the opposite, which is false on that way through
        the function) is refused. Every tenth row is tried."""
        places = [k for k, l in enumerate(self.lines) if l.startswith("k ")]
        self.assertEqual(len(places), 293)
        self.assertEqual(turned("k -2049 0 0 1"), "k 2048 0 0 -1")
        for k in places[::10]:
            with self.subTest(turned=self.lines[k]):
                shown, said = lean_verify.verify(spec_text(), FUNCTIONS, self.changed(self.lines[:k] + [turned(self.lines[k])] + self.lines[k + 1:]))
                self.assertFalse(shown)
                self.assertEqual(said.split("\n")[0], "refused: a proof of arithmetic does not show what is to be shown")

    def test_a_row_of_an_unknown_that_is_not_in_use_is_refused(self):
        """A row may speak only of unknowns in use where it is read: the first row, the hundredth and the last,
        each with one more number, for an unknown far beyond those in use."""
        places = [k for k, l in enumerate(self.lines) if l.startswith("k ")]
        for k in (places[0], places[99], places[-1]):
            with self.subTest(row=self.lines[k]):
                shown, said = lean_verify.verify(spec_text(), FUNCTIONS, self.changed(self.lines[:k] + [self.lines[k] + " 0" * 300 + " 1"] + self.lines[k + 1:]))
                self.assertFalse(shown)
                self.assertEqual(said.split("\n")[0], "refused: a row the proof gives speaks of an unknown that is not in use")

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
                odec.build(src, "left_last", obj)
                functions = [FUNCTIONS[0], (obj, NAME)]
                self.assertFalse(lean_verify.verify(spec_text(), functions, self.kept())[0], what)
                self.assertEqual(last_word(functions), why, what)

    def test_a_changed_contract_that_is_still_true_is_shown(self):
        for what, old, new in STILL_TRUE:
            with self.subTest(what=what):
                self.assertEqual(last_word(FUNCTIONS, once(old, new)), "shown", what)


if __name__ == "__main__":
    unittest.main()
