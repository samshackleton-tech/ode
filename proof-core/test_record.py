#!/usr/bin/env python3
"""A called function is given, to read and write, a part of a run that its caller may read and write:
`ode_absorb` (examples/record) keeps a chaining value in the second half of a 64-byte record and hands the
one-block kernel the address of that half, twice.

    python3 test_record.py        (needs Lean's `lake`; the tests are skipped where it is not installed)

What the verifier in Lean takes here that it refused before:
- the run a called function reads and writes may be whole words of a run this function may read and write,
  at a place that is a number: after the call those words are the new ones, and what was known of the
  run's other words stays;
- a run nothing was written to yet is first taken as written with the words it held at entry, so that the
  words the call leaves alone (here the record's tag) are still known after it;
- a contract may say what a record laid out by a `layout` holds after the call: `ensures r = {tag: …, h: …}`
  (statement.py writes it as the record's words, one field after another).

The function, its contract and the kept proof are shown; with the contract or the function changed in one
place, so that what is stated is false, nothing is shown, and each case names what the verifier then
refuses or what it lacks."""
import os, shutil, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
KCHECK = os.path.join(HERE, "..", "kcheck")
sys.path.insert(0, HERE); sys.path.insert(0, KCHECK); sys.path.insert(0, os.path.join(HERE, "..", "lang"))
import built, lean_verify, odec, prove, statement

RECORD = os.path.join(HERE, "examples", "record")
NAME, SSE41 = "ode_absorb", "blake3_servil_compress_in_place_sse41"
FUNCTIONS = [(os.path.join(KCHECK, "b3hashr.o"), SSE41), (os.path.join(RECORD, "oderecord.o"), NAME)]
# the record at entry, and the record the contract says it becomes, as statement.py writes them
OLD = "(record (tag (call words (slice (name r) (num 0) (num 32)))) (h (call words (slice (name r) (num 32) (num 64)))))"
NEW = (f"(record (tag (field {OLD} tag)) (h (call compress (call compress (field {OLD} h) (call words (name m)) "
       "(call counter (num 0)) (num 64) (num 0)) (call words (name m2)) (call counter (num 0)) (num 64) (num 0))))")
CONTRACT = ["arg r inout 64", "arg m fixed 64", "arg m2 fixed 64", "needs sse41", "hidden m", "hidden m2",
            f"ensuresw r (call bytes_of (bin ++ (field {NEW} tag) (field {NEW} h)))",
            "stack 32"]
# Why the verifier refuses, or what the prover cannot give it.
FOLLOW = "refused: the specification's words are not followed on the terms the function made"
WORD = "refused: a word of the run is not known to hold what the specification says"
NOT_WORDS = "refused: a called function is given to write what is not whole words of a run this function may read and write, each of them known"
NO_PART = "refused: a called function is given a run that is no part of a run this function was given to read"
ENTAIL = "need entail"            # an address is to be shown not to pass 2^64, and it is not so
BYTE = "refused: a byte written to a run that words were written to: not here yet"
STACK = "refused: a call needs more stack than this function's contract allows"
BOTH = "compress(compress(r.h, m, counter(0), 64, 0), m2, counter(0), 64, 0)"
# (what is changed, the contract as it is, the contract changed, what the verifier then says)
CONTRACTS = [
    ("the tag is said to become the old chaining value", "tag: r.tag", "tag: r.h", WORD),
    ("the first block is said to be compressed into the tag", "compress(r.h, m,", "compress(r.tag, m,", FOLLOW),
    ("the blocks are said in the other order", BOTH, "compress(compress(r.h, m2, counter(0), 64, 0), m, counter(0), 64, 0)", FOLLOW),
    ("one block only is said", BOTH, "compress(r.h, m, counter(0), 64, 0)", WORD),
    ("the second counter is said to be 1", "m2, counter(0)", "m2, counter(1)", FOLLOW),
    ("the fields are said to lie in the other order", "tag: cv at 0, h: cv at 32", "h: cv at 0, tag: cv at 32", FOLLOW),
    ("one byte less of stack is said", "stack 32", "stack 31", STACK),
]
CALL = "  mov rsi, r12\n  mov rdx, 64\n  mov rcx, 0\n  mov r8, 0\n  call blake3_servil_compress_in_place_sse41\n"
# (what is changed, the source as it is, which of its places (0: the only one), the source changed, what the verifier then says)
SOURCES = [
    ("the first call is given r + 28: seven words on", "  add rdi, 32\n", 1, "  add rdi, 28\n", FOLLOW),
    ("the first call is given r + 36: its last word is past the record", "  add rdi, 32\n", 1, "  add rdi, 36\n", NOT_WORDS),
    ("the first call is given r: it writes the tag", "  add rdi, 32\n", 1, "  add rdi, 0\n", FOLLOW),
    ("the second call is given r", "  add rdi, 32\n", 2, "  add rdi, 0\n", FOLLOW),
    ("the second call is given r + 30: no whole words", "  add rdi, 32\n", 2, "  add rdi, 30\n", NOT_WORDS),
    ("the second call is given r + 64: past the record", "  add rdi, 32\n", 2, "  add rdi, 64\n", ENTAIL),
    ("the second call is given r - 32: before the record", "  add rdi, 32\n", 2, "  sub rdi, 32\n", ENTAIL),
    ("the second call is given what the first left in rsi", "  mov rsi, r12\n", 0, "", NO_PART),
    ("there is no second call", CALL, 0, "", FOLLOW),
    ("a byte of the tag is written before the calls", "  mov rbx, rdi\n", 0, "  mov rbx, rdi\n  mov byte ptr [rdi + 3], 1\n", NOT_WORDS),
    ("a byte of the chaining value is written between the calls", "  mov rdi, rbx\n", 0, "  mov byte ptr [rbx + 40], 1\n  mov rdi, rbx\n", BYTE),
    ("the first call's block is the record itself", "  add rdi, 32\n", 1, "  mov rsi, rdi\n  add rdi, 32\n", NO_PART),
    ("the second call is given the flag 1", "  mov r8, 0\n", 2, "  mov r8, 1\n", FOLLOW),
]


def spec_text(change=lambda t: t):
    with open(os.path.join(KCHECK, "blake3.spec")) as f: text = f.read()
    for folder, name in (("kernel", "kernel_sse41.contract"), ("record", "record.contract")):
        with open(os.path.join(HERE, "examples", folder, name)) as f: text += "\n" + f.read()
    return change(text)


def once(old, new):
    def change(text):
        assert text.count(old) == 1, (old, text.count(old))
        return text.replace(old, new)
    return change


def at_place(text, old, which, new):
    """The text with `new` for `old` at its place `which` (1: the first, 2: the second; 0: its only place)."""
    assert text.count(old) == (1 if which == 0 else 2), (old, text.count(old))
    i = text.index(old)
    if which == 2: i = text.index(old, i + 1)
    return text[:i] + new + text[i + len(old):]


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
        self.assertEqual(len([l for l in lines[at + 1:] if l.startswith("i ")]), 21)

    def test_a_record_that_is_written_overlaps_nothing_else(self):
        # what is written is taken to overlap nothing else given: the contract must ask it of the caller
        with self.assertRaises(SystemExit) as e: statement.statement(spec_text(once("no_overlap(r, m, m2)", "no_overlap(r, m)")), FUNCTIONS)
        self.assertIn("does not say `requires no_overlap(r, m, m2)`", str(e.exception))

    def test_a_layout_this_reader_does_not_take_for_a_written_record(self):
        # a field that is a number, and fields that leave a gap: said, not guessed at
        cases = (("a number", "tag: number at 0, more: 24 bytes at 8, h: cv at 32", "tag: 0, more: r.more", "does not read there yet: tag: number"),
                 ("a gap", "tag: 28 bytes at 0, h: cv at 32", "tag: r.tag", "do not lie one after another"))
        for what, layout, field, why in cases:
            with self.subTest(what=what):
                change = lambda t: once("tag: r.tag", field)(once("tag: cv at 0, h: cv at 32", layout)(t))
                with self.assertRaises(SystemExit) as e: statement.statement(spec_text(change), FUNCTIONS)
                self.assertIn(why, str(e.exception))


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Verify(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.dir = tempfile.mkdtemp(prefix="oderecord-")
        with open(os.path.join(RECORD, "record.ode")) as f: cls.source = f.read()
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
        odec.build(os.path.join(RECORD, "record.ode"), "absorb", os.path.join(self.dir, "made.o"))
        with open(os.path.join(self.dir, "made.o"), "rb") as f, open(FUNCTIONS[1][0], "rb") as g: self.assertEqual(f.read(), g.read())

    def test_the_function_is_shown_with_the_kernel_it_calls(self):
        self.assertEqual(lean_verify.verify(spec_text(), FUNCTIONS, self.kept()), (True, "shown"))
        # the prover finds the kept proof again: the function's name and no line more (no arithmetic is asked for)
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
        for what, old, which, new, why in SOURCES:
            with self.subTest(what=what):
                src, obj = os.path.join(self.dir, "changed.ode"), os.path.join(self.dir, "changed.o")
                with open(src, "w") as f: f.write(at_place(self.source, old, which, new))
                odec.build(src, "absorb", obj)
                functions = [FUNCTIONS[0], (obj, NAME)]
                self.assertFalse(lean_verify.verify(spec_text(), functions, self.kept())[0], what)
                self.assertEqual(last_word(functions), why, what)


if __name__ == "__main__":
    unittest.main()
