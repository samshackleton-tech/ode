#!/usr/bin/env python3
"""A called function is given a part of a run of bytes: `ode_second_block` (examples/part) hands the one-block
kernel the second 64 bytes of a message as its block, and its own chaining value, which nothing has been
written to yet, as the chaining value the kernel reads and writes.

    python3 test_part.py        (needs Lean's `lake`; the tests are skipped where it is not installed)

Two things the verifier in Lean takes here that it refused before:
- a run of a fixed count that a called function reads may be a part of a run of bytes with a length that
  this function was given: at a place that is a number, and seen at once to end within the run (here by
  `requires len >= 128`);
- a run that a called function reads and writes may be one of this function's that nothing has been written
  to yet: its words are then the words it held at entry.
And the specification's `words(input[64 .. 128])`, of a run of bytes with a length, is followed on terms.

The function, its contract and the kept proof are shown; with the contract or the function changed in one
place, so that what is stated is false, nothing is shown, and each case names what the verifier then
refuses or what it lacks."""
import os, shutil, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
KCHECK = os.path.join(HERE, "..", "kcheck")
sys.path.insert(0, HERE); sys.path.insert(0, KCHECK); sys.path.insert(0, os.path.join(HERE, "..", "lang"))
import built, lean_verify, odec, prove, statement

PART = os.path.join(HERE, "examples", "part")
NAME, SSE41 = "ode_second_block", "blake3_servil_compress_in_place_sse41"
FUNCTIONS = [(os.path.join(KCHECK, "b3hashr.o"), SSE41), (os.path.join(PART, "odepart.o"), NAME)]
CONTRACT = ["arg h inout 32", "arg input bytes len", "arg len number", "needs sse41", "atleast len 128", "hidden input",
            "ensuresw h (call bytes_of (call compress (call words (name h)) (call words (slice (name input) (num 64) (num 128))) "
            "(call counter (num 0)) (num 64) (num 0)))",
            "stack 64"]
# Why the verifier refuses, or what the prover cannot give it.
FOLLOW = "refused: the specification's words are not followed on the terms the function made"
NO_PART = "refused: a called function is given a run that is no part of a run this function was given to read"
ENTAIL = "need entail"            # an address is to be shown not to pass 2^64, a number to be below its bound, or a part given to a
                                  # called function to lie within the run it is a part of, and it is not so
BELOW = "need below"              # the specification turns on how two numbers compare, the proof is asked which way, and neither follows
NOT_KNOWN = "refused: a called function is given to write what is not whole words of a run this function may read and write, each of them known"
# (what is changed, the contract as it is, the contract changed, what the verifier then says)
CONTRACTS = [
    ("the first block is said", "input[64 .. 128]", "input[0 .. 64]", FOLLOW),
    ("bytes 60 to 124 are said", "input[64 .. 128]", "input[60 .. 124]", FOLLOW),
    ("the third block is said", "input[64 .. 128]", "input[128 .. 192]", BELOW),
    ("the message may be one byte too short", "len >= 128", "len >= 127", ENTAIL),
    ("nothing is asked of the message's length", "    requires len >= 128\n", "", ENTAIL),
    ("the counter 1 is said", "input[64 .. 128]), counter(0)", "input[64 .. 128]), counter(1)", FOLLOW),
    ("the block length 63 is said", ", 64, 0)", ", 63, 0)", FOLLOW),
    ("the flag 1 is said", ", 64, 0)", ", 64, 1)", FOLLOW),
]
# (what is changed, the source as it is, the source changed, what the verifier then says)
SOURCES = [
    ("the kernel is given the bytes from 32 on", "  add rsi, 64\n", "  add rsi, 32\n", FOLLOW),
    ("the kernel is given the bytes from 65 on: the last is past the 128 asked for", "  add rsi, 64\n", "  add rsi, 65\n", ENTAIL),
    ("the kernel is given the bytes from 128 on", "  add rsi, 64\n", "  add rsi, 128\n", ENTAIL),
    ("the kernel is given the bytes 64 before the message", "  add rsi, 64\n", "  sub rsi, 64\n", ENTAIL),
    ("the kernel is given the length as the block's address", "  add rsi, 64\n", "  mov rsi, rdx\n", NO_PART),
    ("the kernel is given the block length 32", "  mov rdx, 64\n", "  mov rdx, 32\n", FOLLOW),
    ("the kernel is given the counter 1", "  mov rcx, 0\n", "  mov rcx, 1\n", FOLLOW),
    ("the kernel is given the flag 2", "  mov r8, 0\n", "  mov r8, 2\n", FOLLOW),
    ("eight bytes of h are written before the call", "  sub rsp, 8\n", "  sub rsp, 8\n  mov qword ptr [rdi + 0], rdx\n", FOLLOW),
    ("one byte of h is written before the call", "  sub rsp, 8\n", "  sub rsp, 8\n  mov byte ptr [rdi + 0], 1\n", NOT_KNOWN),
]


def spec_text(change=lambda t: t):
    with open(os.path.join(KCHECK, "blake3.spec")) as f: text = f.read()
    for folder, name in (("kernel", "kernel_sse41.contract"), ("part", "part.contract")):
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
        self.assertEqual(len([l for l in lines[at + 1:] if l.startswith("i ")]), 8)


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Meaning(unittest.TestCase):
    def test_the_ensures_says_the_second_blocks_compression(self):
        """The statement's `ensures` line, worked out by the account in Lean on bytes drawn at random: the
        compression of the message's bytes 64 to 128, as ../kcheck/ode.py works out `compress`."""
        import ensures_meaning as meaning, ode, random
        with open(os.path.join(KCHECK, "blake3.spec")) as f: spec = ode.Spec(f.read())
        line = meaning.ensures(spec_text(), FUNCTIONS, NAME, "h")
        use = ("call", "bytes_of", [("call", "compress", [("call", "words", [("name", "h")]), ("call", "words", [("name", "b")]), ("call", "counter", [("num", 0)]), ("num", 64), ("num", 0)])])
        rng = random.Random(61)
        cases, want, first = [], [], []
        for n in (128, 129, 200, 1000):
            h, message = bytes(rng.randrange(256) for _ in range(32)), bytes(rng.randrange(256) for _ in range(n))
            cases.append((line, {"h": h, "input": message, "len": n}))
            want.append("bytes " + bytes(spec.eval(ode.Numbers(), use, {"h": list(h), "b": list(message[64:128])})).hex())
            first.append("bytes " + bytes(spec.eval(ode.Numbers(), use, {"h": list(h), "b": list(message[:64])})).hex())
        got = meaning.account(spec_text(), FUNCTIONS, cases)
        self.assertEqual(got, want)
        self.assertTrue(all(g != f for g, f in zip(got, first)))          # (a control: the first block's is another)


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Verify(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.dir = tempfile.mkdtemp(prefix="odepart-")
        with open(os.path.join(PART, "part.ode")) as f: cls.source = f.read()
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
        odec.build(os.path.join(PART, "part.ode"), "second_block", os.path.join(self.dir, "made.o"))
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
                odec.build(src, "second_block", obj)
                functions = [FUNCTIONS[0], (obj, NAME)]
                self.assertFalse(lean_verify.verify(spec_text(), functions, self.kept())[0], what)
                self.assertEqual(last_word(functions), why, what)


if __name__ == "__main__":
    unittest.main()
