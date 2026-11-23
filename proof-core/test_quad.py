#!/usr/bin/env python3
"""A call of a function that is given a table of addresses: `ode_quad` (examples/quad) makes the parent of
two parent nodes with the hash's 16-way kernel, called twice. The kernel's contract gives it a table of
sixteen addresses, each the address of a lane's blocks, and a run of 512 bytes to write; it has one
`ensures` for each lane. In `ode_quad` the table and both runs written are parts of its own stack frame,
and the second round's lanes read what the first round wrote.

    python3 test_quad.py        (needs Lean's `lake`; the tests are skipped where it is not installed)

What the verifier in Lean takes here that it refused before (`symCallL` in Core.lean; its proof is
SoundCallL.lean):
- the table and the run the called function writes are parts of this function's frame, at or above the
  stack pointer, apart from each other, and every cell of the table is known;
- each lane's blocks are a part of a run this function was given to read, or a part of the frame, apart
  from the run written, every word of them known (so the first round's values are, in the second round);
- the count of blocks is a number of the table;
- after the call the words written are new unknowns. Where a lane's `ensures` is the bytes of the words of
  a use of a definition that the verifier does not work out, the use is given a number of its own, and the
  verifier holds that the use gives the lane's words. `out` is then compared with what the contract says
  through those uses: `parent` of two uses of `compress`.

The function, its contract and the kept proof are shown; with the contract or the function changed in one
place, so that what is stated is false, nothing is shown, and each case names what the verifier then
refuses. Changed functions that still meet the contract are shown. One true statement is refused, and is
kept here as a limit: every lane of the second round reads the same block, so its second value is the same
bytes as its first, and a function that takes `out` from the second value still meets the contract. The
verifier holds what a use gives for the first lane that has it; of a later lane with the same use it holds
nothing about the words written."""
import os, shutil, sys, tempfile, time, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
KCHECK = os.path.join(HERE, "..", "kcheck")
sys.path.insert(0, HERE); sys.path.insert(0, KCHECK); sys.path.insert(0, os.path.join(HERE, "..", "lang"))
import built, lean_verify, odec, prove, statement

QUAD = os.path.join(HERE, "examples", "quad")
NAME, P16 = "ode_quad", "blake3_servil_avx512_p16"
FUNCTIONS = [(os.path.join(KCHECK, "b3hashr.o"), P16), (os.path.join(QUAD, "odequad.o"), NAME)]
COMPRESS = ("(call compress (call words (slice (name kf) (num 0) (num 32))) (call words (name {})) (call counter (num 0)) (num 64) "
            "(bin | (call number.le (slice (name kf) (num 32) (num 40))) (call PARENT)))")
CONTRACT = ["arg out inout 32", "arg a fixed 64", "arg b fixed 64", "arg kf fixed 40", "mbelow kf 32 256", "needs avx512", "hidden a", "hidden b", "hidden kf",
            "ensuresw out (call bytes_of (call parent (call words (slice (name kf) (num 0) (num 32))) (call number.le (slice (name kf) (num 32) (num 40))) "
            + COMPRESS.format("a") + " " + COMPRESS.format("b") + "))",
            "stack 5280"]
# Why the verifier refuses.
FOLLOW = "refused: the specification's words are not followed on the terms the function made"
WORD = "refused: a word of the run is not known to hold what the specification says"
STACK = "refused: a call needs more stack than this function's contract allows"
LANE = "refused: a lane of a called function's table is not blocks this function may read, every word of them known"
FRAME = "refused: a called function's table of addresses, or the run it writes, is no part of this function's frame, or the two overlap"
JUMP = "refused: a jump on a flag that may depend on values kept out of the trace: which instructions run would depend on them"
P = "compress(kf.key, {}, counter(0), 64, kf.flags | PARENT)"
ENS = f"parent(kf.key, kf.flags, {P.format('a')}, {P.format('b')})"


def once(old, new, n=1):
    """The text with `old`, which stands in it `n` times, replaced by `new`."""
    def change(text):
        assert text.count(old) == n, (old, text.count(old))
        return text.replace(old, new)
    return change


def first(old, new):
    """The text with the first `old` replaced by `new`; `old` stands in it twice (once a round)."""
    def change(text):
        assert text.count(old) == 2, (old, text.count(old))
        return text.replace(old, new, 1)
    return change


def last(old, new):
    """The text with the second `old` replaced by `new`; `old` stands in it twice (once a round)."""
    def change(text):
        assert text.count(old) == 2, (old, text.count(old))
        at = text.rindex(old)
        return text[:at] + new + text[at + len(old):]
    return change


def then(*changes):
    def change(text):
        for c in changes: text = c(text)
        return text
    return change


def out_from(base):
    """`out` is read from the frame at `base` in place of 640: the last change first, so that no place is changed twice."""
    return then(*[once(f"qword ptr [rsp + {640 + 8 * k}]", f"qword ptr [rsp + {base + 8 * k}]") for k in (3, 2, 1, 0)])


# (what is changed, the contract changed, what the verifier then says)
CONTRACTS = [
    ("a and b are said exchanged", once(ENS, f"parent(kf.key, kf.flags, {P.format('b')}, {P.format('a')})"), FOLLOW),
    ("a is said twice", once(ENS, f"parent(kf.key, kf.flags, {P.format('a')}, {P.format('a')})"), FOLLOW),
    ("PARENT is not said in the first compression", once(ENS, ENS.replace("kf.flags | PARENT)", "kf.flags)", 1)), FOLLOW),
    ("the counter 1 is said in the first compression", once(ENS, ENS.replace("counter(0)", "counter(1)", 1)), FOLLOW),
    ("the first compression alone is said", once(ENS, P.format("a")), WORD),
    ("5279 bytes of stack are said", once("stack 5280", "stack 5279"), STACK),
]
# (what is changed, the source changed, what the verifier then says)
SOURCES = [
    ("lane 1 reads a", once("  mov rax, rdx\n  mov qword ptr [rsp + 8], rax\n", "  mov rax, rsi\n  mov qword ptr [rsp + 8], rax\n"), FOLLOW),
    ("lanes 0 and 1 are exchanged", once("  mov rax, rsi\n  mov qword ptr [rsp + 0], rax\n  mov rax, rdx\n  mov qword ptr [rsp + 8], rax\n",
                                         "  mov rax, rdx\n  mov qword ptr [rsp + 0], rax\n  mov rax, rsi\n  mov qword ptr [rsp + 8], rax\n"), FOLLOW),
    ("the second round reads from the second value on", once("  lea rax, [rsp + 128]\n", "  lea rax, [rsp + 160]\n"), FOLLOW),
    ("PARENT is not in the first round's flags", first("  or rax, 1073741828\n", "  or rax, 1073741824\n"), FOLLOW),
    ("PARENT is not in the second round's flags", last("  or rax, 1073741828\n", "  or rax, 1073741824\n"), FOLLOW),
    ("the counter is 1 in the second round", last("  mov rcx, 0\n", "  mov rcx, 1\n"), FOLLOW),
    ("two blocks a lane in the first round", first("  mov rsi, 1\n", "  mov rsi, 2\n"), LANE),
    ("lane 5's cell of the table is not written in the first round", once("  mov rax, rsi\n  mov qword ptr [rsp + 40], rax\n", ""), LANE),
    ("the first round writes over the table", once("  lea r9, [rsp + 128]\n", "  lea r9, [rsp + 64]\n"), FRAME),
    ("the second round writes over what its lanes read", once("  lea r9, [rsp + 640]\n", "  lea r9, [rsp + 128]\n"), LANE),
    ("out is the first value of the first round", out_from(128), WORD),
    # (one instruction more is run where the cell holds 1 or more)
    ("a jump on a cell the kernel wrote", once("  mov rax, 0\n  add rsp, 1160\n",
                                                "  mov rax, qword ptr [rsp + 640]\n  cmp rax, 1\n  jb @skip\n  mov rax, 0\n@skip:\n  mov rax, 0\n  add rsp, 1160\n"), JUMP),
]
# Changed functions that still meet the contract: (what is changed, the source changed).
STILL_TRUE = [
    ("lane 2 reads b: what it leaves is not used", once("  mov rax, rsi\n  mov qword ptr [rsp + 16], rax\n", "  mov rax, rdx\n  mov qword ptr [rsp + 16], rax\n")),
    ("the count of blocks comes by way of another register", first("  mov rsi, 1\n", "  mov rax, 1\n  mov rsi, rax\n")),
    ("the second round's values lie eight bytes further up", then(once("  lea r9, [rsp + 640]\n", "  lea r9, [rsp + 648]\n"), out_from(648))),
    # (a caller may rely on nothing that a called function leaves in a register: until that was the rule, this was refused)
    ("rax is not set to zero at the end: it holds bytes of the value", once("  mov rax, 0\n  add rsp, 1160\n", "  add rsp, 1160\n")),
]
# A changed function that still meets the contract and is refused: a limit.
SECOND_VALUE = out_from(672)


def spec_text(change=lambda t: t):
    with open(os.path.join(KCHECK, "blake3.spec")) as f: text = f.read()
    for folder, name in (("kernel", "p16.contract"), ("quad", "quad.contract")):
        with open(os.path.join(HERE, "examples", folder, name)) as f: text += "\n" + f.read()
    return change(text)


def found(functions, change=lambda t: t):
    """What the prover finds for `ode_quad`, given the kernel's kept proof: the lines after the function's
    name, or the verifier's last word where the prover has nothing more to write."""
    with tempfile.TemporaryDirectory() as d:
        statement_path = os.path.join(d, "statement")
        with open(statement_path, "w") as f: f.write("\n".join(statement.statement(spec_text(change), functions)) + "\n")
        with open(os.path.join(HERE, "proofs", P16 + ".proof")) as f: kept = f.read().rstrip("\n").split("\n")
        p = prove.Prover(statement_path, kept + [f"for {NAME}"], os.path.join(d, "proof"), [], until=time.time() + 120)
        p.last = ""
        try: lines = p.solve([])
        finally: p.close()
        if lines is not None: return lines
        said = [l for l in p.last.split("\n") if l.startswith(("refused:", "need "))]
        return said[0] if said else p.last


def last_word(functions, change=lambda t: t):
    got = found(functions, change)
    return "shown" if isinstance(got, list) else got


class Statement(unittest.TestCase):
    def test_the_contract_in_the_accounts_terms(self):
        lines = statement.statement(spec_text(), FUNCTIONS)
        at = lines.index(f"fn {NAME}")
        self.assertGreater(at, lines.index(f"fn {P16}"))                        # after the function it calls
        mine = [l for l in lines[at + 1:] if not l.startswith(("i ", "def "))]
        self.assertEqual(mine, CONTRACT)
        self.assertEqual(len([l for l in lines[at + 1:] if l.startswith("i ")]), 85)
        # the kernel it calls: a table of sixteen addresses, and one line for each lane's part of the run
        kernel = lines[lines.index(f"fn {P16}") + 1:at]
        self.assertIn("lanes inputs n", kernel)
        self.assertEqual(len([l for l in kernel if l.startswith("ensuresw out ")]), 16)


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Meaning(unittest.TestCase):
    def test_the_ensures_says_the_parent_of_two_parents(self):
        """The statement's `ensures` line, worked out by the account in Lean on bytes drawn at random: the
        parent of the compressions of `a` and of `b`, as ../kcheck/ode.py works out `parent` and `compress`.
        (Controls: with a and b exchanged the bytes are others; so are they without PARENT in the
        compressions, where the flags do not have it.)"""
        import ensures_meaning as meaning, ode, random
        with open(os.path.join(KCHECK, "blake3.spec")) as f: spec = ode.Spec(f.read())
        line = meaning.ensures(spec_text(), FUNCTIONS, NAME, "out")
        comp = lambda block, flags: ("call", "compress", [("call", "words", [("name", "k")]), ("call", "words", [("name", block)]),
                                                         ("call", "counter", [("num", 0)]), ("num", 64), ("name", flags)])
        use = lambda x, y, flags: ("call", "bytes_of", [("call", "parent", [("call", "words", [("name", "k")]), ("name", "f"), comp(x, flags), comp(y, flags)])])
        rng = random.Random(81)
        cases, want, exchanged, plain = [], [], [], []
        for flags in (0, 1, 16, 251, 4, 255):
            out, a, b, key = (bytes(rng.randrange(256) for _ in range(n)) for n in (32, 64, 64, 32))
            cases.append((line, {"out": out, "a": a, "b": b, "kf": key + flags.to_bytes(8, "little")}))
            env = {"k": list(key), "a": list(a), "b": list(b), "f": flags, "fp": flags | 4}
            value = lambda e: "bytes " + bytes(spec.eval(ode.Numbers(), e, env)).hex()
            want.append(value(use("a", "b", "fp")))
            exchanged.append(value(use("b", "a", "fp")))
            plain.append((flags, value(use("a", "b", "f"))))
        got = meaning.account(spec_text(), FUNCTIONS, cases)
        self.assertEqual(got, want)
        self.assertTrue(all(g != o for g, o in zip(got, exchanged)))
        self.assertTrue(all((g != o) == (flags & 4 == 0) for g, (flags, o) in zip(got, plain)))


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Verify(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.dir = tempfile.mkdtemp(prefix="odequad-")
        with open(os.path.join(QUAD, "quad.ode")) as f: cls.source = f.read()
    @classmethod
    def tearDownClass(cls): shutil.rmtree(cls.dir)

    def kept(self, symbols=(P16, NAME)):
        """The kept proofs of these functions, in one file."""
        path = os.path.join(self.dir, "kept.proof")
        with open(path, "w") as out:
            for symbol in symbols:
                with open(os.path.join(HERE, "proofs", symbol + ".proof")) as f: out.write(f.read())
        return path

    def changed(self, change):
        """The function with its source changed, as an object file."""
        src, obj = os.path.join(self.dir, "changed.ode"), os.path.join(self.dir, "changed.o")
        with open(src, "w") as f: f.write(change(self.source))
        odec.build(src, "quad", obj)
        return [FUNCTIONS[0], (obj, NAME)]

    def test_the_example_is_made_from_its_source(self):
        odec.build(os.path.join(QUAD, "quad.ode"), "quad", os.path.join(self.dir, "made.o"))
        with open(os.path.join(self.dir, "made.o"), "rb") as f, open(FUNCTIONS[1][0], "rb") as g: self.assertEqual(f.read(), g.read())

    def test_the_function_is_shown_with_the_kernel_it_calls(self):
        self.assertEqual(lean_verify.verify(spec_text(), FUNCTIONS, self.kept()), (True, "shown"))
        # the prover finds the kept proof again: the function's name alone
        self.assertEqual(found(FUNCTIONS), [])
        with open(os.path.join(HERE, "proofs", NAME + ".proof")) as f: self.assertEqual(f.read(), f"for {NAME}\n")
        # control: the kernel is not taken as shown without its proof
        shown, said = lean_verify.verify(spec_text(), FUNCTIONS, self.kept((NAME,)))
        self.assertFalse(shown)
        self.assertEqual(said.split("\n")[-1], "in " + P16)

    def test_a_contract_changed_in_one_place(self):
        for what, change, why in CONTRACTS:
            with self.subTest(what=what):
                self.assertFalse(lean_verify.verify(spec_text(change), FUNCTIONS, self.kept())[0], what)
                self.assertEqual(last_word(FUNCTIONS, change), why, what)

    def test_a_function_changed_in_one_place(self):
        for what, change, why in SOURCES:
            with self.subTest(what=what):
                functions = self.changed(change)
                self.assertFalse(lean_verify.verify(spec_text(), functions, self.kept())[0], what)
                self.assertEqual(last_word(functions), why, what)

    def test_a_changed_function_that_still_meets_the_contract_is_shown(self):
        for what, change in STILL_TRUE:
            with self.subTest(what=what):
                functions = self.changed(change)
                self.assertEqual(lean_verify.verify(spec_text(), functions, self.kept()), (True, "shown"), what)
                self.assertEqual(found(functions), [], what)

    def test_limits_a_true_statement_is_refused(self):
        """Every lane of the second round reads the same block (the first round's first two values), so
        the second value the second round leaves is the same bytes as the first, and a function that
        takes `out` from the second value still meets the contract. The verifier holds what the use gives
        for the first lane; for the second lane it works the same use out from that, and holds nothing
        about the words the second lane wrote: refused."""
        functions = self.changed(SECOND_VALUE)
        self.assertFalse(lean_verify.verify(spec_text(), functions, self.kept())[0])
        self.assertEqual(last_word(functions), WORD)


if __name__ == "__main__":
    unittest.main()
