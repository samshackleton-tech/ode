#!/usr/bin/env python3
"""A called function writes a run of bytes for its caller: `ode_tail` (examples/tail) calls `b3l_pad`, the
hash's own function that pads the last block of a chunk, as it lies in ../kcheck/b3hashr.o.

    python3 test_tail.py        (needs Lean's `lake`; the tests are skipped where it is not installed)

`ode_tail` keeps a 96-byte record: a chaining value, then a block of 64 bytes. It gives `b3l_pad` the
address of the record's block to write, and the message from its byte 16 on to read. What the verifier in
Lean takes here that it refused before:
- a call of a function that writes a run it does not read, whose contract says the run then holds the
  list a definition gives (`ensures block = padded(src)`). The run must be whole words of a run this
  function may read and write, each of them known. After the call those words are new unknowns, and the
  definition, used with what the function was given, is known to be their bytes;
- a run of bytes with a length that the called function reads may be a part of such a run of this
  function's: the place and the length are numbers the verifier holds, seen at once to lie within the run;
- the specification's `src[16 .. len]` and `len(...)` of a run of bytes with a length are followed.
The theorem behind the first needs one fact about the machine: a contract says what a run holds as a
list of numbers, and each must be a byte. In the account a cell of memory is a byte by its type. (When
this was built it was a theorem about the machine's runs, `runs_bytes`.)

The function, its contract and the kept proof are shown; with the contract or the function changed in one
place, so that what is stated is false, nothing is shown, and each case names what the verifier then
refuses or what it lacks. Two true statements are refused, and are kept here as limits."""
import os, re, shutil, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
KCHECK = os.path.join(HERE, "..", "kcheck")
sys.path.insert(0, HERE); sys.path.insert(0, KCHECK); sys.path.insert(0, os.path.join(HERE, "..", "lang"))
import built, lean_verify, odec, prove, statement

TAIL = os.path.join(HERE, "examples", "tail")
NAME, PAD = "ode_tail", "b3l_pad"
FUNCTIONS = [(os.path.join(KCHECK, "b3hashr.o"), PAD), (os.path.join(TAIL, "odetail.o"), NAME)]
# the record the contract says the run becomes, as statement.py writes it (`r.h`: the field of the record at entry);
# the record is had once, by a `let`, and its bytes are those of its fields' words
NEW = "(record (h (call words (slice (name r) (num 0) (num 32)))) (block (call padded (slice (name src) (num 16) (name len)))))"
CONTRACT = ["arg r inout 96", "arg src bytes len", "arg len number", "atleast len 17", "below len 81", "hidden src",
            f"ensuresw r (call bytes_of (let record {NEW} (bin ++ (field (name record) h) (call words (field (name record) block)))))",
            "stack 64"]
# Why the verifier refuses, or what the prover cannot give it.
FOLLOW = "refused: the specification's words are not followed on the terms the function made"
WORD = "refused: a word of the run is not known to hold what the specification says"
NOT_WORDS = "refused: a called function is given to write what is not whole words of a run this function may read and write, each of them known"
NO_PART = "refused: a called function is given a run of bytes that is no part of a run of bytes this function was given"
NO_RUN = "refused: a write to a run given only to read, or to no run given"
ENTAIL = "need entail"            # an address is to be shown not to pass 2^64, a number to be below its bound, or a part given to a
                                  # called function to lie within the run it is a part of, and it is not so
KNOW = "need know"                # the proof file has run out before an `ensures` or a call, and of the rows that the prover
                                  # would name there (that a part lies within its run; how two numbers compare) none is shown
STACK = "refused: a call needs more stack than this function's contract allows"
# (what is changed, the contract as it is, the contract changed, what the verifier then says)
CONTRACTS = [
    ("the block is said to hold the message from byte 15 on", "src[16 .. len]", "src[15 .. len]", FOLLOW),
    ("the block is said to hold the whole message", "padded(src[16 .. len])", "padded(src)", FOLLOW),
    ("the block is said to hold bytes 16 to 80, which a shorter message does not have", "src[16 .. len]", "src[16 .. 80]", KNOW),
    ("the block is said to hold all but the last byte", "src[16 .. len]", "src[16 .. len - 1]", KNOW),
    ("the block is said to be as it was", "block: padded(src[16 .. len])", "block: r.block", WORD),
    ("one byte less of stack is said", "stack 64", "stack 63", STACK),
    ("the fields are said to lie in the other order", "h: cv at 0, block: 64 bytes at 32", "block: 64 bytes at 0, h: cv at 64", WORD),
]
# (what is changed, the source as it is, the source changed, what the verifier then says)
SOURCES = [
    ("b3l_pad is given r + 28 to write: it writes the chaining value's last word", "  add rdi, 32\n", "  add rdi, 28\n", WORD),
    ("b3l_pad is given r + 36 to write: its last word is past the record", "  add rdi, 32\n", "  add rdi, 36\n", NOT_WORDS),
    ("b3l_pad is given r to write", "  add rdi, 32\n", "  add rdi, 0\n", WORD),
    ("b3l_pad is given r + 34 to write: no whole words", "  add rdi, 32\n", "  add rdi, 34\n", NOT_WORDS),
    ("b3l_pad is given the message from byte 15 on, as long as before", "  add rsi, 16\n", "  add rsi, 15\n", FOLLOW),
    ("b3l_pad is given one byte more to read: a byte past the message", "  sub rdx, 16\n", "  sub rdx, 15\n", KNOW),
    ("b3l_pad is given one byte less to read", "  sub rdx, 16\n", "  sub rdx, 17\n", FOLLOW),
    ("b3l_pad is given the whole length to read: 16 bytes past the message", "  sub rdx, 16\n", "", KNOW),
    ("b3l_pad is given the message itself to write", "  add rdi, 32\n", "  mov rdi, rsi\n", NOT_WORDS),
    ("b3l_pad is given the record's own bytes to read", "  add rsi, 16\n", "  mov rsi, rdi\n", NO_PART),
    ("a byte is written where rdi points after the call", "  add rsp, 8\n", "  mov byte ptr [rdi + 0], 1\n  add rsp, 8\n", NO_RUN),
    ("there is no call", "  call b3l_pad\n", "", FOLLOW),
]


def pad_contract():
    """The contract of b3l_pad as ../kcheck/proofs/inner.spec has it."""
    with open(os.path.join(KCHECK, "proofs", "inner.spec")) as f: text = f.read()
    (found,) = re.findall(r"^contract b3l_pad\(.*?^\}\n", text, re.S | re.M)
    return found


def spec_text(change=lambda t: t):
    with open(os.path.join(KCHECK, "blake3.spec")) as f: text = f.read()
    with open(os.path.join(TAIL, "tail.contract")) as f: mine = f.read()
    return change(text + "\n" + pad_contract() + "\n" + mine)


def pad_places():
    with open(os.path.join(HERE, "examples", "hash", "pad.places")) as f: return f.read()


def once(old, new):
    def change(text):
        assert text.count(old) == 1, (old, text.count(old))
        return text.replace(old, new)
    return change


def last_word(functions, change=lambda t: t):
    """What the verifier says at last of the functions [(object, symbol)] with the proof that the prover
    writes for them: `shown`, or its last word where the prover has nothing more to write."""
    with tempfile.TemporaryDirectory() as d:
        try:
            prove.prove(spec_text(change), [(obj, symbol, pad_places() if symbol == PAD else "") for obj, symbol in functions],
                        os.path.join(d, "statement"), os.path.join(d, "proof"))
        except SystemExit as e:
            lines = [l for l in str(e).split("\n") if l.startswith(("refused:", "need "))]
            return lines[0] if lines else str(e)
        return "shown"


class Statement(unittest.TestCase):
    def test_the_contract_in_the_accounts_terms(self):
        lines = statement.statement(spec_text(), FUNCTIONS)
        at = lines.index(f"fn {NAME}")
        self.assertGreater(at, lines.index(f"fn {PAD}"))                      # after the function it calls
        mine = [l for l in lines[at + 1:] if not l.startswith(("i ", "def "))]
        self.assertEqual(mine, CONTRACT)
        self.assertEqual(len([l for l in lines[at + 1:] if l.startswith("i ")]), 7)


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Meaning(unittest.TestCase):
    def test_the_ensures_says_the_record_of_the_contract(self):
        """The statement's `ensures` line, worked out by the account in Lean on bytes drawn at random: the
        chaining value as it was, then the message from byte 16 on with zeros after it to 64 bytes."""
        import ensures_meaning as meaning, random
        line = meaning.ensures(spec_text(), FUNCTIONS, NAME, "r")
        rng = random.Random(63)
        cases, want = [], []
        for n in (17, 18, 40, 79, 80):
            r, src = bytes(rng.randrange(256) for _ in range(96)), bytes(rng.randrange(1, 256) for _ in range(n))
            cases.append((line, {"r": r, "src": src, "len": n}))
            want.append("bytes " + (r[:32] + src[16:].ljust(64, b"\0")).hex())
        self.assertEqual(meaning.account(spec_text(), FUNCTIONS, cases), want)
        # (of 81 bytes there are 65 from byte 16 on, and `padded` is the first 64 of them: the `ensures` has a
        # value there too. What a contract that allowed 81 would ask of b3l_pad is another matter: see the limits.)
        r, src = bytes(96), bytes(range(1, 82))
        self.assertEqual(meaning.account(spec_text(), FUNCTIONS, [(line, {"r": r, "src": src, "len": 81})]), ["bytes " + (r[:32] + src[16:80]).hex()])


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Verify(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.dir = tempfile.mkdtemp(prefix="odetail-")
        with open(os.path.join(TAIL, "tail.ode")) as f: cls.source = f.read()
    @classmethod
    def tearDownClass(cls): shutil.rmtree(cls.dir)

    def kept(self, symbols=(PAD, NAME)):
        """The kept proofs of these functions, in one file."""
        path = os.path.join(self.dir, "kept.proof")
        with open(path, "w") as out:
            for symbol in symbols:
                with open(os.path.join(HERE, "proofs", symbol + ".proof")) as f: out.write(f.read())
        return path

    def test_the_example_is_made_from_its_source(self):
        odec.build(os.path.join(TAIL, "tail.ode"), "tail", os.path.join(self.dir, "made.o"))
        with open(os.path.join(self.dir, "made.o"), "rb") as f, open(FUNCTIONS[1][0], "rb") as g: self.assertEqual(f.read(), g.read())

    def test_the_function_is_shown_with_the_function_it_calls(self):
        self.assertEqual(lean_verify.verify(spec_text(), FUNCTIONS, self.kept()), (True, "shown"))
        # the prover finds the kept proofs again
        statement_path, proof_path = os.path.join(self.dir, "s"), os.path.join(self.dir, "p")
        prove.prove(spec_text(), [(obj, symbol, pad_places() if symbol == PAD else "") for obj, symbol in FUNCTIONS], statement_path, proof_path)
        with open(proof_path) as f: found = f.read()
        with open(os.path.join(HERE, "proofs", NAME + ".proof")) as f: kept = f.read()
        self.assertEqual(found[found.index("for " + NAME):], kept)
        with open(os.path.join(HERE, "proofs", PAD + ".proof")) as f: self.assertEqual(found[:found.index("for " + NAME)], f.read())
        # controls: b3l_pad is not taken as shown without its proof, nor left out of what is to be shown
        shown, said = lean_verify.verify(spec_text(), FUNCTIONS, self.kept((NAME,)))
        self.assertFalse(shown)
        self.assertEqual(said.split("\n")[-1], "in " + PAD)
        with self.assertRaises(SystemExit) as e: lean_verify.verify(spec_text(), FUNCTIONS[1:], self.kept())
        self.assertIn("which is not among the functions to be shown", str(e.exception))

    def test_a_changed_proof_is_refused(self):
        with open(os.path.join(HERE, "proofs", NAME + ".proof")) as f: lines = f.read().split("\n")[:-1]
        self.assertGreater(len(lines), 2)
        for k in range(1, len(lines)):
            with self.subTest(left_out=lines[k]):
                path = os.path.join(self.dir, "changed.proof")
                with open(path, "w") as out:
                    with open(os.path.join(HERE, "proofs", PAD + ".proof")) as f: out.write(f.read())
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
                odec.build(src, "tail", obj)
                functions = [FUNCTIONS[0], (obj, NAME)]
                self.assertFalse(lean_verify.verify(spec_text(), functions, self.kept())[0], what)
                self.assertEqual(last_word(functions), why, what)

    def test_limits_two_true_statements_refused(self):
        # With 16 bytes the statement is still true: b3l_pad is then given no byte to read. The verifier
        # refuses it: `src + 16` could be 2^64, one past the last address, and its rule for an addition asks
        # that the sum stay below 2^64. (Kept as a test: when the rule takes it, this test says so.)
        self.assertFalse(lean_verify.verify(spec_text(once("len >= 17", "len >= 16")), FUNCTIONS, self.kept())[0])
        self.assertEqual(last_word(FUNCTIONS, once("len >= 17", "len >= 16")), ENTAIL)
        # With 81 bytes the statement is still true: b3l_pad is then given 65 bytes, and as it is written it
        # copies the first 64 of them, which is what `padded` of 65 bytes is. The verifier refuses it:
        # b3l_pad's contract asks for at most 64, and a call is taken by the called function's contract alone,
        # whatever its instructions would do. (A limit that stays: it is what verifying by contracts means.)
        self.assertFalse(lean_verify.verify(spec_text(once("len <= 80", "len <= 81")), FUNCTIONS, self.kept())[0])
        self.assertEqual(last_word(FUNCTIONS, once("len <= 80", "len <= 81")), ENTAIL)


if __name__ == "__main__":
    unittest.main()
