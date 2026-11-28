#!/usr/bin/env python3
"""A key and its flags, read from a record, start a compression: `ode_keyed` (examples/keyed) copies the 32
bytes of a key into `out`, sixteen bytes at a time through a vector register, reads the flags that lie
beside the key, and calls the one-block kernel, which reads and writes `out`.

    python3 test_keyed.py        (needs Lean's `lake`; the tests are skipped where it is not installed)

The record is the hash's own `keyed` (`layout keyed 40 { key: cv at 0, flags: byte at 32 }`), and the steps
are those by which the hash's `b3l_take` and `b3l_subtree` begin a parent node. No rule of the verifier in
Lean is new here. The test keeps what those functions will rely on:
- sixteen bytes read from a record given to read are four of its words, and sixteen bytes stored to a run
  given to read and write are four words of it: after two such copies the run holds the key's eight words;
- the flags are a number read from the record, which the layout says is below 256; the called function is
  given it in a register;
- the specification's `kf.key` and `kf.flags` are followed on those words and that number.

The function, its contract and the kept proof are shown; with the contract or the function changed in one
place, so that what is stated is false, nothing is shown, and each case names what the verifier then
refuses or what it lacks. Three changed functions that still meet the contract are shown.

The contract has no `trace` line: the record is hidden, the key and the flags. The flags are read from it
into a register and given to the kernel, whose contract hides its flags. (Until a number given in a
register could be hidden, this contract had to say `trace depends on kf`, and the statement without that
line, true as it was, was refused: it was kept here as a limit.)"""
import os, shutil, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
KCHECK = os.path.join(HERE, "..", "kcheck")
sys.path.insert(0, HERE); sys.path.insert(0, KCHECK); sys.path.insert(0, os.path.join(HERE, "..", "lang"))
import built, lean_verify, odec, prove, statement

KEYED = os.path.join(HERE, "examples", "keyed")
NAME, SSE41 = "ode_keyed", "blake3_servil_compress_in_place_sse41"
FUNCTIONS = [(os.path.join(KCHECK, "b3hashr.o"), SSE41), (os.path.join(KEYED, "odekeyed.o"), NAME)]
CONTRACT = ["arg out inout 32", "arg m fixed 64", "arg kf fixed 40", "mbelow kf 32 256", "needs sse41", "disjoint out m 1", "disjoint out kf 1", "disjoint m kf 1", "hidden m", "hidden kf",
            "ensuresw out (call bytes_of (call compress (call words (slice (name kf) (num 0) (num 32))) (call words (name m)) "
            "(call counter (num 0)) (num 64) (call number.le (slice (name kf) (num 32) (num 40)))))",
            "stack 64"]
# Why the verifier refuses, or what the prover cannot give it.
FOLLOW = "refused: the specification's words are not followed on the terms the function made"
NO_PART = "refused: a called function is given a run that is no part of a run this function was given to read"
NOT_KNOWN = "refused: a called function is given to write what is not whole words of a run this function may read and write, each of them known"
STACK = "refused: a call needs more stack than this function's contract allows"
JUMP = "refused: a jump on a flag that may depend on values kept out of the trace: which instructions run would depend on them"
ARGS = "refused: what a called function's contract says of its arguments is not followed"
NOT_WORDS = "refused: sixteen bytes that are not four words of the run"
READ8 = "refused: a read of a run of a fixed count that is not eight bytes within it: not here yet"
# (what is changed, the contract as it is, the contract changed, what the verifier then says)
CONTRACTS = [
    ("the flags are said to be none", "64, kf.flags)", "64, 0)", FOLLOW),
    ("the counter 1 is said", "counter(0), 64, kf.flags)", "counter(1), 64, kf.flags)", FOLLOW),
    ("the block length 63 is said", "64, kf.flags)", "63, kf.flags)", FOLLOW),
    ("what `out` held is said to be the start", "compress(kf.key, m,", "compress(out, m,", FOLLOW),
    ("the layout has the flags first and the key after them", "key: cv at 0, flags: byte at 32", "flags: byte at 0, key: cv at 8", ARGS),
    ("the layout has a record of 48 bytes, the flags at its end", "layout keyed 40 { key: cv at 0, flags: byte at 32 }", "layout keyed 48 { key: cv at 0, flags: byte at 40 }", ARGS),
    ("fifteen bytes of stack are said", "stack 64", "stack 15", STACK),
]
# (what is changed, the source as it is, the source changed, what the verifier then says)
SOURCES = [
    ("the key's first half is read from byte 8 on", "  movups xmm0, xmmword ptr [rdx + 0]\n", "  movups xmm0, xmmword ptr [rdx + 8]\n", FOLLOW),
    ("the key's second half is not copied", "  movups xmm0, xmmword ptr [rdx + 16]\n  movups xmmword ptr [rdi + 16], xmm0\n", "", NOT_KNOWN),
    ("the key's second half is stored four bytes early", "  movups xmmword ptr [rdi + 16], xmm0\n", "  movups xmmword ptr [rdi + 12], xmm0\n", NOT_KNOWN),
    ("the key's second half is stored four bytes late: its last word is past `out`", "  movups xmmword ptr [rdi + 16], xmm0\n", "  movups xmmword ptr [rdi + 20], xmm0\n", NOT_WORDS),
    ("the key's second half is read from byte 28 on: four bytes past the record", "  movups xmm0, xmmword ptr [rdx + 16]\n", "  movups xmm0, xmmword ptr [rdx + 28]\n", NOT_WORDS),
    ("the key's two halves are exchanged", "  movups xmmword ptr [rdi + 0], xmm0\n  movups xmm0, xmmword ptr [rdx + 16]\n  movups xmmword ptr [rdi + 16], xmm0\n",
     "  movups xmmword ptr [rdi + 16], xmm0\n  movups xmm0, xmmword ptr [rdx + 16]\n  movups xmmword ptr [rdi + 0], xmm0\n", FOLLOW),
    ("the flags are read from byte 24 on: the key's last eight bytes", "  mov r8, qword ptr [rdx + 32]\n", "  mov r8, qword ptr [rdx + 24]\n", ARGS),
    ("the flags are read from byte 33 on: one byte past the record", "  mov r8, qword ptr [rdx + 32]\n", "  mov r8, qword ptr [rdx + 33]\n", READ8),
    ("the flags are not read: the kernel is given what r8 held", "  mov r8, qword ptr [rdx + 32]\n", "", ARGS),
    ("the kernel is given the flags and one more", "  mov rdx, 64\n", "  add r8, 1\n  mov rdx, 64\n", FOLLOW),
    ("the kernel is given the block length 32", "  mov rdx, 64\n", "  mov rdx, 32\n", FOLLOW),
    ("the kernel is given the counter 1", "  mov rcx, 0\n", "  mov rcx, 1\n", FOLLOW),
    ("the kernel is given the block from its byte 4 on: four bytes past it", "  mov rdx, 64\n", "  add rsi, 4\n  mov rdx, 64\n", NO_PART),
    ("the kernel is given the record as its block", "  mov rdx, 64\n", "  mov rsi, rdx\n  mov rdx, 64\n", NO_PART),
]
# Changed functions that still meet the contract: (what is changed, the source as it is, the source changed).
STILL_TRUE = [
    ("the flags are read first", "  movups xmm0, xmmword ptr [rdx + 0]\n", "  mov r8, qword ptr [rdx + 32]\n  movups xmm0, xmmword ptr [rdx + 0]\n"),
    ("the key's second half is copied first",
     "  movups xmm0, xmmword ptr [rdx + 0]\n  movups xmmword ptr [rdi + 0], xmm0\n  movups xmm0, xmmword ptr [rdx + 16]\n  movups xmmword ptr [rdi + 16], xmm0\n",
     "  movups xmm0, xmmword ptr [rdx + 16]\n  movups xmmword ptr [rdi + 16], xmm0\n  movups xmm0, xmmword ptr [rdx + 0]\n  movups xmmword ptr [rdi + 0], xmm0\n"),
    ("both halves are read before either is stored",
     "  movups xmmword ptr [rdi + 0], xmm0\n  movups xmm0, xmmword ptr [rdx + 16]\n  movups xmmword ptr [rdi + 16], xmm0\n",
     "  movups xmm1, xmmword ptr [rdx + 16]\n  movups xmmword ptr [rdi + 0], xmm0\n  movups xmmword ptr [rdi + 16], xmm1\n"),
]


def spec_text(change=lambda t: t):
    with open(os.path.join(KCHECK, "blake3.spec")) as f: text = f.read()
    for folder, name in (("kernel", "kernel_sse41.contract"), ("keyed", "keyed.contract")):
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
        self.assertEqual(len([l for l in lines[at + 1:] if l.startswith("i ")]), 11)


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Meaning(unittest.TestCase):
    def test_the_ensures_says_the_compression_from_the_key_with_the_flags(self):
        """The statement's `ensures` line, worked out by the account in Lean on bytes drawn at random: the
        compression of the block from the record's key with the record's flags, as ../kcheck/ode.py works
        out `compress`. (`out` as it was has no part in it.)"""
        import ensures_meaning as meaning, ode, random
        with open(os.path.join(KCHECK, "blake3.spec")) as f: spec = ode.Spec(f.read())
        line = meaning.ensures(spec_text(), FUNCTIONS, NAME, "out")
        use = ("call", "bytes_of", [("call", "compress", [("call", "words", [("name", "k")]), ("call", "words", [("name", "b")]), ("call", "counter", [("num", 0)]), ("num", 64), ("name", "f")])])
        rng = random.Random(77)
        cases, want, other_flags, other_key = [], [], [], []
        for flags in (0, 1, 16, 255, 2, 11):
            out, m, key = (bytes(rng.randrange(256) for _ in range(n)) for n in (32, 64, 32))
            cases.append((line, {"out": out, "m": m, "kf": key + flags.to_bytes(8, "little")}))
            value = lambda k, f: "bytes " + bytes(spec.eval(ode.Numbers(), use, {"k": list(k), "b": list(m), "f": f})).hex()
            want.append(value(key, flags))
            other_flags.append(value(key, flags ^ 1))
            other_key.append(value(out, flags))
        got = meaning.account(spec_text(), FUNCTIONS, cases)
        self.assertEqual(got, want)
        self.assertTrue(all(g != o for g, o in zip(got, other_flags)))       # (controls: other flags, and `out` as the key,
        self.assertTrue(all(g != o for g, o in zip(got, other_key)))         #  give other bytes)


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Verify(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.dir = tempfile.mkdtemp(prefix="odekeyed-")
        with open(os.path.join(KEYED, "keyed.ode")) as f: cls.source = f.read()
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
        odec.build(src, "keyed", obj)
        return [FUNCTIONS[0], (obj, NAME)]

    def test_the_example_is_made_from_its_source(self):
        odec.build(os.path.join(KEYED, "keyed.ode"), "keyed", os.path.join(self.dir, "made.o"))
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
                functions = self.changed(old, new)
                self.assertFalse(lean_verify.verify(spec_text(), functions, self.kept())[0], what)
                self.assertEqual(last_word(functions), why, what)

    def test_a_changed_function_that_still_meets_the_contract_is_shown(self):
        for what, old, new in STILL_TRUE:
            with self.subTest(what=what):
                self.assertEqual(last_word(self.changed(old, new)), "shown", what)

    def test_the_trace(self):
        """The record is hidden (`hidden kf`), and so are the flags read from it: the function is shown, since
        it only hands the flags to the kernel, whose contract hides them. Changed so that one instruction more
        is run where the flags are 0, it is refused; the same changed function is shown against a contract
        that says the trace may depend on the record. And the function as it is meets that weaker contract."""
        self.assertIn("hidden kf", statement.statement(spec_text(), FUNCTIONS))
        named = once("    stack 64\n    needs sse41\n}\n", "    trace depends on kf\n    stack 64\n    needs sse41\n}\n")
        self.assertNotIn("hidden kf", statement.statement(spec_text(named), FUNCTIONS))
        jump = self.changed("  mov r8, qword ptr [rdx + 32]\n", "  mov r8, qword ptr [rdx + 32]\n  cmp r8, 0\n  je @none\n  mov rax, rax\n@none:\n")
        self.assertFalse(lean_verify.verify(spec_text(), jump, self.kept())[0])
        self.assertEqual(last_word(jump), JUMP)
        self.assertEqual(last_word(jump, named), "shown")
        self.assertEqual(last_word(FUNCTIONS, named), "shown")


if __name__ == "__main__":
    unittest.main()
