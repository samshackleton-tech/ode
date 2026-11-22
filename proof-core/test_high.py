#!/usr/bin/env python3
"""Flags packed into a larger number: `ode_high` (examples/high) compresses one block from a key, as
`ode_keyed` does, and hands the kernel its flags packed with more: the record's flags, PARENT (4), and the
bit 2^34, put together by `or`. The kernel's contract reads the low 32 bits of that register.

    python3 test_high.py        (needs Lean's `lake`; the tests are skipped where it is not installed)

What the verifier in Lean takes here that it refused before. Two numbers' bits put together are no row of
numbers in general: the verifier keeps one unknown for the pair. But the flags are a number below 256
(the layout says so), and a number of the table that is 256 or more has bits the flags cannot reach:
- the bits of the table's number from bit 8 on are ADDED (`symOrSmall` in Core.lean), and only its low
  byte is put together with the flags. So `flags | (2^34 | 4)` is 2^34 and `flags | 4`;
- the remainder and the quotient by a number m of a row that is a multiple of m and a number seen at once
  to lie from 0 to below m are that number and the multiple's quotient (`lowOf`, `quotOf`): the low 32
  bits of 2^34 and `flags | 4` are `flags | 4`;
- where the specification puts a number below 256 together with a number of the table that is 256 or
  more, the same parts are found (`orSmall`).
The hash's upper functions pack the flags of their wide kernels so (`flags | 0x40020100`), and the wide
kernels' contracts take the four bytes apart by `%` and `/`.

The function, its contract and the kept proof are shown; with the contract or the function changed in one
place, so that what is stated is false, nothing is shown, and each case names what the verifier then
refuses. Changed contracts and functions that are still true are shown. One true statement is refused,
and is kept here as a limit: the contract may say the flags with the bit 2^34 that the function sets
(`compress` takes the low word of its flags, so the value is the same); the verifier compares the flags
as numbers and does not open `compress`."""
import os, shutil, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
KCHECK = os.path.join(HERE, "..", "kcheck")
sys.path.insert(0, HERE); sys.path.insert(0, KCHECK); sys.path.insert(0, os.path.join(HERE, "..", "lang"))
import built, lean_verify, odec, prove, statement

HIGH = os.path.join(HERE, "examples", "high")
NAME, SSE41 = "ode_high", "blake3_servil_compress_in_place_sse41"
FUNCTIONS = [(os.path.join(KCHECK, "b3hashr.o"), SSE41), (os.path.join(HIGH, "odehigh.o"), NAME)]
CONTRACT = ["arg out inout 32", "arg m fixed 64", "arg kf fixed 40", "mbelow kf 32 256", "needs sse41", "hidden m", "hidden kf",
            "ensuresw out (call bytes_of (call compress (call words (slice (name kf) (num 0) (num 32))) (call words (name m)) "
            "(call counter (num 0)) (num 64) (bin | (call number.le (slice (name kf) (num 32) (num 40))) (call PARENT))))",
            "stack 64"]
# Why the verifier refuses.
FOLLOW = "refused: the specification's words are not followed on the terms the function made"
STACK = "refused: a call needs more stack than this function's contract allows"
ARGS = "refused: what a called function's contract says of its arguments is not followed"
ENS = "64, kf.flags | PARENT)"
PACK = "  mov rax, 1\n  shl rax, 34\n  or rax, 4\n  or r8, rax\n"
# (what is changed, the contract as it is, the contract changed, what the verifier then says)
CONTRACTS = [
    ("PARENT is not said", ENS, "64, kf.flags)", FOLLOW),
    ("CHUNK_END is said in PARENT's place", ENS, "64, kf.flags | CHUNK_END)", FOLLOW),
    ("the record's flags are not said", ENS, "64, PARENT)", FOLLOW),
    ("the flags are said with the bit 2^31, which the kernel would read", ENS, "64, kf.flags | 2147483652)", FOLLOW),
    ("the flags and 4 are said added, not put together", ENS, "64, kf.flags + 4)", FOLLOW),
    ("the low 32 bits of the flags and 2^34 are said, without PARENT", ENS, "64, (kf.flags + 17179869184) % 4294967296)", FOLLOW),
    ("the block length is said as a quotient that is 65", ENS, "(kf.flags + 279172874240) / 4294967296, kf.flags | PARENT)", FOLLOW),
    ("the block length is said as a quotient that is 65 where the flags are 255", ENS, "(kf.flags + 279172873985) / 4294967296, kf.flags | PARENT)", FOLLOW),
    ("fifteen bytes of stack are said", "stack 64", "stack 15", STACK),
]
# Changed contracts that are still true: (what is changed, the contract as it is, the contract changed).
CONTRACTS_STILL_TRUE = [
    ("PARENT is said as the number 4", ENS, "64, kf.flags | 4)"),
    ("the low 32 bits of what is said are said", ENS, "64, (kf.flags | PARENT) % 4294967296)"),
    ("the low 32 bits of the flags and 2^34, put together with PARENT", ENS, "64, (kf.flags + 17179869184) % 4294967296 | PARENT)"),
    ("the block length is said as a quotient that is 64", ENS, "(kf.flags + 274877906944) / 4294967296, kf.flags | PARENT)"),
    ("the block length is said as a quotient that is 64 whatever the flags", ENS, "(kf.flags + 279172873984) / 4294967296, kf.flags | PARENT)"),
]
# (what is changed, the source as it is, the source changed, what the verifier then says)
SOURCES = [
    ("the bit put in is 2^31: the kernel reads it", "  shl rax, 34\n", "  shl rax, 31\n", FOLLOW),
    ("the bit put in is 2^8: the kernel reads it", "  shl rax, 34\n", "  shl rax, 8\n", FOLLOW),
    ("PARENT is not put in", "  or rax, 4\n", "", FOLLOW),
    ("CHUNK_END is put in, not PARENT", "  or rax, 4\n", "  or rax, 2\n", FOLLOW),
    ("nothing is put in", PACK, "", FOLLOW),
    ("the number is added to the flags, not put together with them", "  or r8, rax\n", "  add r8, rax\n", FOLLOW),
    ("the kernel is given the number alone, without the record's flags", "  or r8, rax\n", "  mov r8, rax\n", FOLLOW),
    ("the flags are read from byte 24 on: the key's last eight bytes", "  mov r8, qword ptr [rdx + 32]\n", "  mov r8, qword ptr [rdx + 24]\n", ARGS),
]
# Changed functions that still meet the contract: (what is changed, the source as it is, the source changed).
STILL_TRUE = [
    ("the bit put in is 2^32, the first the kernel does not read", "  shl rax, 34\n", "  shl rax, 32\n"),
    ("the bit put in is 2^63", "  shl rax, 34\n", "  shl rax, 63\n"),
    ("no bit above the low word is put in", "  mov rax, 1\n  shl rax, 34\n  or rax, 4\n", "  mov rax, 4\n"),
    ("the flags are put into the number, and the kernel is given that", "  or r8, rax\n", "  or rax, r8\n  mov r8, rax\n"),
    ("PARENT is put into the flags first, the bit 2^34 after it", PACK, "  or r8, 4\n  mov rax, 1\n  shl rax, 34\n  or r8, rax\n"),
]


def spec_text(change=lambda t: t):
    with open(os.path.join(KCHECK, "blake3.spec")) as f: text = f.read()
    for folder, name in (("kernel", "kernel_sse41.contract"), ("high", "high.contract")):
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
        self.assertEqual(len([l for l in lines[at + 1:] if l.startswith("i ")]), 15)

    def test_a_constant_of_the_specification_named_in_a_contract(self):
        """`PARENT` in the contract is the specification's constant: the statement has the use of the
        definition it is. An argument of that name would be the argument."""
        lines = statement.statement(spec_text(), FUNCTIONS)
        self.assertIn("def PARENT = (num 4)", lines)
        self.assertIn("(call PARENT)", CONTRACT[7])
        renamed = lambda t: once("contract ode_high(out: cv, m: block, kf: keyed)", "contract ode_high(out: cv, PARENT: block, kf: keyed)")(
            once("requires no_overlap(out, m, kf)", "requires no_overlap(out, PARENT, kf)")(once("compress(kf.key, m, ", "compress(kf.key, PARENT, ")(t)))
        lines = statement.statement(spec_text(renamed), FUNCTIONS)
        ensures = [l for l in lines[lines.index(f"fn {NAME}"):] if l.startswith("ensuresw out ")][0]
        self.assertIn("(call words (name PARENT))", ensures)
        self.assertNotIn("(call PARENT)", ensures)


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Meaning(unittest.TestCase):
    def test_the_ensures_says_the_compression_with_the_flags_and_parent(self):
        """The statement's `ensures` line, worked out by the account in Lean on bytes drawn at random: the
        compression of the block from the record's key with the record's flags and PARENT put together,
        as ../kcheck/ode.py works out `compress`. (Controls: the flags without PARENT, and the flags and 4
        added, give other bytes where the flags have no bit 4, or have it.)"""
        import ensures_meaning as meaning, ode, random
        with open(os.path.join(KCHECK, "blake3.spec")) as f: spec = ode.Spec(f.read())
        line = meaning.ensures(spec_text(), FUNCTIONS, NAME, "out")
        use = ("call", "bytes_of", [("call", "compress", [("call", "words", [("name", "k")]), ("call", "words", [("name", "b")]), ("call", "counter", [("num", 0)]), ("num", 64), ("name", "f")])])
        rng = random.Random(78)
        cases, want, plain, added = [], [], [], []
        for flags in (0, 1, 16, 255, 4, 12, 251):
            out, m, key = (bytes(rng.randrange(256) for _ in range(n)) for n in (32, 64, 32))
            cases.append((line, {"out": out, "m": m, "kf": key + flags.to_bytes(8, "little")}))
            value = lambda f: "bytes " + bytes(spec.eval(ode.Numbers(), use, {"k": list(key), "b": list(m), "f": f})).hex()
            want.append(value(flags | 4))
            plain.append((flags, value(flags)))
            added.append((flags, value(flags + 4)))
        got = meaning.account(spec_text(), FUNCTIONS, cases)
        self.assertEqual(got, want)
        self.assertTrue(all((g != o) == (flags & 4 == 0) for g, (flags, o) in zip(got, plain)))
        self.assertTrue(all((g != o) == (flags & 4 != 0) for g, (flags, o) in zip(got, added)))


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Verify(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.dir = tempfile.mkdtemp(prefix="odehigh-")
        with open(os.path.join(HIGH, "high.ode")) as f: cls.source = f.read()
    @classmethod
    def tearDownClass(cls): shutil.rmtree(cls.dir)

    def kept(self, symbols=(SSE41, NAME)):
        """The kept proofs of these functions, in one file."""
        path = os.path.join(self.dir, "kept.proof")
        with open(path, "w") as out:
            for symbol in symbols:
                with open(os.path.join(HERE, "proofs", symbol + ".proof")) as f: out.write(f.read())
        return path

    def changed(self, old, new):
        """The function with its source changed in one place, as an object file."""
        self.assertEqual(self.source.count(old), 1, old)
        src, obj = os.path.join(self.dir, "changed.ode"), os.path.join(self.dir, "changed.o")
        with open(src, "w") as f: f.write(self.source.replace(old, new))
        odec.build(src, "high", obj)
        return [FUNCTIONS[0], (obj, NAME)]

    def test_the_example_is_made_from_its_source(self):
        odec.build(os.path.join(HIGH, "high.ode"), "high", os.path.join(self.dir, "made.o"))
        with open(os.path.join(self.dir, "made.o"), "rb") as f, open(FUNCTIONS[1][0], "rb") as g: self.assertEqual(f.read(), g.read())

    def test_the_function_is_shown_with_the_kernel_it_calls(self):
        self.assertEqual(lean_verify.verify(spec_text(), FUNCTIONS, self.kept()), (True, "shown"))
        # the prover finds the kept proof again: the function's name alone
        statement_path, proof_path = os.path.join(self.dir, "s"), os.path.join(self.dir, "p")
        prove.prove(spec_text(), [(obj, symbol, "") for obj, symbol in FUNCTIONS], statement_path, proof_path)
        with open(proof_path) as f: found = f.read()
        with open(os.path.join(HERE, "proofs", NAME + ".proof")) as f: kept = f.read()
        self.assertEqual(found[found.index("for " + NAME):], kept)
        self.assertEqual(kept, f"for {NAME}\n")
        # control: the kernel is not taken as shown without its proof
        shown, said = lean_verify.verify(spec_text(), FUNCTIONS, self.kept((NAME,)))
        self.assertFalse(shown)
        self.assertEqual(said.split("\n")[-1], "in " + SSE41)

    def test_a_contract_changed_in_one_place(self):
        for what, old, new, why in CONTRACTS:
            with self.subTest(what=what):
                self.assertFalse(lean_verify.verify(spec_text(once(old, new)), FUNCTIONS, self.kept())[0], what)
                self.assertEqual(last_word(FUNCTIONS, once(old, new)), why, what)

    def test_a_changed_contract_that_is_still_true_is_shown(self):
        for what, old, new in CONTRACTS_STILL_TRUE:
            with self.subTest(what=what):
                self.assertEqual(lean_verify.verify(spec_text(once(old, new)), FUNCTIONS, self.kept()), (True, "shown"), what)

    def test_a_function_changed_in_one_place(self):
        for what, old, new, why in SOURCES:
            with self.subTest(what=what):
                functions = self.changed(old, new)
                self.assertFalse(lean_verify.verify(spec_text(), functions, self.kept())[0], what)
                self.assertEqual(last_word(functions), why, what)

    def test_a_changed_function_that_still_meets_the_contract_is_shown(self):
        for what, old, new in STILL_TRUE:
            with self.subTest(what=what):
                self.assertEqual(last_word(self.changed(old, new)), "shown", what)

    def test_limits_a_true_statement_is_refused(self):
        """The contract may say the flags with the bit 2^34, which the function sets: `compress` makes a
        word of its flags (their low 32 bits), so the value is the same and the statement is true. The
        verifier compares the two numbers, 2^34 apart, and does not open `compress`: refused."""
        change = once(ENS, "64, kf.flags | 17179869188)")
        self.assertFalse(lean_verify.verify(spec_text(change), FUNCTIONS, self.kept())[0])
        self.assertEqual(last_word(FUNCTIONS, change), FOLLOW)


if __name__ == "__main__":
    unittest.main()
