#!/usr/bin/env pypy3
"""Verify `b3l_pad`, the hash's function that pads the last block of a chunk, from the shipped bytes.

    pypy3 test_pad.py        (skipped where Lean's `lake` is not installed)

The function is `b3l_pad` as it lies in ../kcheck/b3hashr.o: 39 instructions. Its contract is the one in
../kcheck/proofs/inner.spec, as it is written there:

    contract b3l_pad(block: 64 bytes, src: n bytes, n: number) {
        requires no_overlap(block, src)
        requires n <= 64
        ensures block = padded(src)
        stack 48
    }

It has no `trace depends on` line: which instructions run and which addresses are touched depend on `n` and
on no byte of `src`. So the statement says `hidden src`, and the verifier shows that too.

What it exercises that no function before it did:

  - a loop that writes a run, one byte each time round. The loop's place (examples/hash/pad.places) says
    what is written so far: `wrote block[i ..] = padded(src)`, the places of the block from `i` on, each
    with the specification's thing there. The verifier shows that of the first coming to the place (nothing
    is written yet: `i` is 64), and of each later coming from the one before (one byte more, at `i - 1`).
    At the return `i` is 0 and the whole block is what `ensures` says;
  - a specification that is a list made thing by thing (`[if k < len(bytes) then bytes[k] else 0 for k in 0..64]`);
  - a run of bytes whose length is an argument, hidden.

Each control is a statement that is false, or a place that says too little or something false. Each is
refused."""
import os, re, shutil, sys, tempfile, time, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
KCHECK = os.path.join(HERE, "..", "kcheck")
sys.path.insert(0, HERE); sys.path.insert(0, KCHECK); sys.path.insert(0, os.path.join(HERE, "..", "lang"))
import built, lean_verify, odec, prove, statement

OBJ = os.path.join(KCHECK, "b3hashr.o")
PAD = "b3l_pad"
LINES = ["fn b3l_pad", "arg block out 64", "arg src bytes n", "arg n number", "below n 65", "hidden src",
         "ensures block (num 0) (num 64) (call padded (name src))", "stack 48"]
SECRET = "may depend on a secret"


def contract():
    """The contract as ../kcheck/proofs/inner.spec has it."""
    with open(os.path.join(KCHECK, "proofs", "inner.spec")) as f: text = f.read()
    (found,) = re.findall(r"^contract b3l_pad\(.*?^\}\n", text, re.S | re.M)
    return found


def spec_text(change=lambda t: t):
    with open(os.path.join(KCHECK, "blake3.spec")) as f: text = f.read()
    return change(text + "\n" + contract())


def places(change=lambda t: t):
    with open(os.path.join(HERE, "examples", "hash", "pad.places")) as f: return change(f.read())


def once(old, new):
    def change(text):
        assert text.count(old) == 1, (old, text.count(old))
        return text.replace(old, new)
    return change


def last_word(obj=OBJ, spec=lambda t: t, place=lambda t: t):
    """What the verifier says at last with the proof that the prover writes: `shown`, or its last word."""
    with tempfile.TemporaryDirectory() as d:
        try: prove.prove(spec_text(spec), [(obj, PAD, places(place))], os.path.join(d, "statement"), os.path.join(d, "proof"))
        except SystemExit as e:
            lines = [l for l in str(e).split("\n") if l.startswith(("refused:", "need "))]
            return lines[0] if lines else str(e)
        return "shown"


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Pad(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.dir = tempfile.mkdtemp(prefix="odepad-")
        with open(os.path.join(KCHECK, "hash.ode")) as f: cls.source = f.read()
        cls.kept = os.path.join(HERE, "proofs", PAD + ".proof")
    @classmethod
    def tearDownClass(cls): shutil.rmtree(cls.dir)

    def pad_from(self, old, new):
        """The function built again from its source, with one line of it changed."""
        text = self.source
        start = text.index('fn pad as "b3l_pad" {'); end = text.index("\n}\n", start)
        body = text[start:end]
        self.assertEqual(body.count(old), 1, old)
        text = text[:start] + body.replace(old, new) + text[end:]
        src, obj = os.path.join(self.dir, "changed.ode"), os.path.join(self.dir, "changed.o")
        with open(src, "w") as f: f.write(text)
        odec.build(src, "pad", obj)
        return obj

    def test_the_contract_in_the_accounts_terms(self):
        lines = statement.statement(spec_text(), [(OBJ, PAD)])
        self.assertEqual([l for l in lines if l.split()[0] not in ("i", "def")], LINES)
        self.assertEqual(sum(l.startswith("i ") for l in lines), 39)

    def test_the_function_is_shown_from_the_shipped_bytes(self):
        t = time.time()
        self.assertEqual(lean_verify.verify(spec_text(), [(OBJ, PAD)], self.kept), (True, "shown"))
        took = time.time() - t
        # the prover finds the kept proof again
        statement_path, proof_path = os.path.join(self.dir, "s"), os.path.join(self.dir, "p")
        numbers = prove.prove(spec_text(), [(OBJ, PAD, places())], statement_path, proof_path)
        with open(proof_path) as f: found = f.read()
        with open(self.kept) as f: kept = f.read()
        self.assertEqual(found, kept)
        print(f"\nb3l_pad: shown; the proof: {len(kept.splitlines())} lines, {len(kept)} bytes, found in {numbers[PAD][0]} runs of the verifier; "
              f"one run from the files (with building the statement) {took * 1000:.0f} ms", file=sys.stderr)

    def test_a_changed_proof_is_refused(self):
        with open(self.kept) as f: lines = f.read().split("\n")[:-1]
        at = [k for k, l in enumerate(lines) if l.startswith(("t ", "p ", "s ", "q", "wrote ", "fact ", "decreases ", "keep "))]
        self.assertGreater(len(at), 20)
        for k in at:
            with self.subTest(left_out=lines[k]):
                path = os.path.join(self.dir, "changed.proof")
                with open(path, "w") as out: out.write("\n".join(lines[:k] + lines[k + 1:]) + "\n")
                try: shown = lean_verify.verify(spec_text(), [(OBJ, PAD)], path)[0]
                except SystemExit: shown = False
                # a `keep` line left out leaves a place that keeps nothing: refused; any other line left out: refused
                self.assertFalse(shown)

    def test_a_wrong_specification_is_refused(self):
        padded = "def padded(bytes) { [if k < len(bytes) then bytes[k] else 0 for k in 0..64] }"
        for what, change in (
                ("the padding is ones", once(padded, padded.replace("else 0", "else 1"))),
                ("one byte more of the run than it has", once(padded, padded.replace("k < len(bytes)", "k <= len(bytes)"))),
                ("one byte less of the run", once(padded, padded.replace("k < len(bytes)", "k + 1 < len(bytes)"))),
                ("the bytes one place on", once(padded, padded.replace("then bytes[k]", "then bytes[k + 1]"))),
                ("a list of 63", once(padded, padded.replace("0..64", "0..63"))),
                ("the other run's bytes", once("ensures block = padded(src)", "ensures block = padded(block)"))):
            with self.subTest(what=what):
                self.assertNotEqual(last_word(spec=change), "shown")
                try: shown = lean_verify.verify(spec_text(change), [(OBJ, PAD)], self.kept)[0]
                except SystemExit: shown = False
                self.assertFalse(shown)

    def test_a_wrong_contract_is_refused(self):
        for what, change, word in (
                ("less stack than the function uses", once("    stack 48\n", "    stack 39\n"), "need entail"),
                ("the run may be longer than a block and the list is of its bytes", once("requires n <= 64", "requires n <= 4096"), None)):
            with self.subTest(what=what):
                said = last_word(spec=change)
                if word is None: self.assertEqual(said, "shown")       # (true: the first 64 bytes are copied, and `padded` has no more)
                else: self.assertIn(word, said)

    def test_a_place_that_says_too_little_or_something_false_is_refused(self):
        line = "    wrote block[i ..] = padded(src)\n"
        for what, change in (
                ("nothing of what is written", once(line, "")),
                ("one place less", once(line, "    wrote block[i + 1 ..] = padded(src)\n")),
                ("one place more", once(line, "    wrote block[i - 1 ..] = padded(src)\n")),
                ("every place, from the start", once(line, "    wrote block[0 ..] = padded(src)\n")),
                ("no bound of the count", once("    fact i <= 64\n", "")),
                ("a count that does not go down", once("    decreases i\n", "    decreases 64 - i\n"))):
            with self.subTest(what=what):
                self.assertNotEqual(last_word(place=change), "shown")

    def test_a_wrong_function_is_refused(self):
        for what, old, new, word in (
                ("the padding is ones", "  // u8[block + i] = 0\n  mov rax, 0\n", "  // u8[block + i] = 0\n  mov rax, 1\n", None),
                ("a byte of the run past its end", "  mov rcx, r12\n  cmp rax, rcx\n  jae @l2\n", "  mov rcx, r12\n  add rcx, 1\n  cmp rax, rcx\n  jae @l2\n", None),
                ("the bytes one place on", "  mov rax, rbp\n  add rax, r13\n", "  mov rax, rbp\n  add rax, r13\n  add rax, 1\n", None),
                ("the block's own bytes", "  mov rax, rbp\n  add rax, r13\n", "  mov rax, rbx\n  add rax, r13\n", None),
                ("one place of the block left out", "  mov rax, 64\n  mov r13, rax\n", "  mov rax, 63\n  mov r13, rax\n", None),
                ("a jump on a byte of the run", "  movzx eax, byte ptr [rax]\n", "  movzx eax, byte ptr [rax]\n  cmp rax, 0\n  je @l3\n", SECRET)):
            with self.subTest(what=what):
                said = last_word(obj=self.pad_from(old, new))
                self.assertNotEqual(said, "shown")
                if word: self.assertIn(word, said)

    def test_the_function_built_again_from_its_source_is_the_same(self):
        instructions = lambda obj: [l for l in statement.statement(spec_text(), [(obj, PAD)]) if l.startswith("i ")]
        again = self.pad_from("  // i = 64\n", "  // i = 64 \n")
        self.assertEqual(instructions(again), instructions(OBJ))
        self.assertEqual(lean_verify.verify(spec_text(), [(again, PAD)], self.kept), (True, "shown"))

    def test_the_trace(self):
        # the contract may say the trace depends on the run: it promises less, and is shown too
        self.assertEqual(last_word(spec=once("    stack 48\n", "    stack 48\n    trace depends on src\n")), "shown")


if __name__ == "__main__":
    unittest.main()
