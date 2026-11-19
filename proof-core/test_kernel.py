#!/usr/bin/env python3
"""The hash's one-block kernel, `blake3_servil_compress_in_place_avx512`, in the verifier in Lean.

    python3 test_kernel.py        (the tests of the verifier are skipped where Lean's `lake` is not installed)

The kernel is 76 instructions of ../kcheck/b3hashr.o (its source: ../wide/one.ode). Its contract gives it
eight words to read and write (`h: cv`), sixteen to read (`m: block`), a counter and two low bytes of
registers, and promises `h = compress(h, m, t, length, flags)`: BLAKE3's compression function as
../kcheck/blake3.spec defines it. statement.py writes that in the account's terms: 32 bytes read and
written, 64 bytes read, three numbers, and the run `h` at the return being the bytes of the words `compress`
gives of the words of the bytes at entry.

The verifier shows it. It follows each of the four low words of a vector register as a term over the words
read at entry (a sum, an exclusive or, a turn to the right), goes seven times round the loop by the count
the function keeps in a byte, and at the return works the specification's `compress` out on the same terms:
each word it gives must be the term stored at its place of `h`. The proof it needs is 189 bytes: four
proofs of arithmetic, that the flags' byte shifted left by 32 bits, and the length's byte added to that,
stay below 2^64.

With the specification, the contract or the function changed in one place it does not say `shown`, and the
prover finds no proof; each case names what the verifier then says. With a line of the proof left out or
changed it does not say `shown`.

Not shown here, though the kernel's real contract (../kcheck/proofs/inner.spec) promises it: that which
instructions run and which addresses are touched depend on no byte of `h` or `m`. The account in Lean says
nothing of that yet (examples/kernel/kernel.contract says so with `trace depends on h, m`)."""
import os, shutil, subprocess, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "lang"))
import built, lean_verify, odec, prove, statement
KCHECK = os.path.join(HERE, "..", "kcheck")
LAKE = lean_verify.LAKE
SYMBOL = "blake3_servil_compress_in_place_avx512"
CONTRACT = ["arg h inout 32", "arg m fixed 64", "arg length number", "arg t number", "arg flags number", "needs avx512",
            "ensuresw h (call bytes_of (call compress (call words (name h)) (call words (name m)) (call counter (name t)) "
            "(bin % (name length) (num 256)) (bin % (name flags) (num 256))))", "stack 0"]
# what the verifier says where it does not say `shown`
FOLLOW = "the specification's words are not followed on the terms the function made"    # a word the specification gives is no term the function made
HOLD = "a word of the run is not known to hold what the specification says"            # every word is a term the function made, but not the one stored there
WORDS = "sixteen bytes that are not four words of the run"                             # a load or a store that is not of whole words inside a run
NO_RUN = "sixteen bytes written to what is no run given to write"
AGAIN = "a read of a run given to read and write after it was written to"
ENTAIL = "need entail"                                                                 # something is to be shown of numbers, and the prover has no proof of it
RESULT = "[s[7][i] ^ s[7][i + 8] for i in 0..8]"
# (what is changed, the text as it is, the text changed, what the verifier then says): the specification, then the contract
SPECS = [
    ("a turn by 15 for 16", ">>> 16", ">>> 15", FOLLOW),
    ("a turn by 13 for 12", ">>> 12", ">>> 13", FOLLOW),
    ("a turn by 9 for 8", ">>> 8", ">>> 9", FOLLOW),
    ("a turn by 9 for 7", ">>> 7", ">>> 9", FOLLOW),
    ("a word of the constants", "0x6A09E667", "0x6A09E668", FOLLOW),
    ("two places of the permutation exchanged", "2, 6, 3, 10", "6, 2, 3, 10", FOLLOW),
    ("the counter's halves exchanged", "lo(t), hi(t)", "hi(t), lo(t)", FOLLOW),
    ("the length and the flags exchanged", "word(length), word(flags)", "word(flags), word(length)", FOLLOW),
    ("two words of the block exchanged in a column", "g(c1, 1, 5, 9, 13, m[2], m[3])", "g(c1, 1, 5, 9, 13, m[3], m[2])", FOLLOW),
    ("a diagonal mixes another word", "g(d1, 1, 6, 11, 12,", "g(d1, 1, 6, 11, 13,", FOLLOW),
    ("six rounds", RESULT, RESULT.replace("s[7]", "s[6]"), FOLLOW),
    ("eight rounds", RESULT, RESULT.replace("s[7]", "s[8]"), FOLLOW),
    ("the block is not permuted between rounds", "let w[r + 1] = [w[r][PERMUTATION[i]] for i in 0..16]", "let w[r + 1] = w[r]", FOLLOW),
    ("the two halves of the state are not joined", RESULT, "[s[7][i] for i in 0..8]", HOLD),
    ("seven words are promised", RESULT, RESULT.replace("0..8", "0..7"), HOLD),
    ("the contract: the length and the flags exchanged", "ensures h = compress(h, m, t, length, flags)", "ensures h = compress(h, m, t, flags, length)", FOLLOW),
    ("the contract: the whole of the length's register", "length: low byte", "length: number", FOLLOW),
    ("the contract: the whole of the flags' register", "flags: low byte", "flags: number", FOLLOW),
    ("the contract: the counter is a plain number", "t: counter", "t: number", FOLLOW),
    ("the contract: the block and the value exchanged", "ensures h = compress(h, m, t, length, flags)", "ensures h = compress(m, h, t, length, flags)", FOLLOW),
]
END = "  ret\n}\n\n// The same for processors with SSE4.1"            # (the end of this kernel in ../wide/one.ode: the other kernel there ends alike)
STORES = "  vmovdqu xmmword ptr [rdi], xmm0\n  vmovdqu xmmword ptr [rdi+0x10], xmm1\n" + END
# (what is changed, the source as it is, the source changed, what the verifier then says)
SOURCES = [
    ("a turn by 15 for 16", "    vprord xmm3, xmm3, 16\n", "    vprord xmm3, xmm3, 15\n", FOLLOW),
    ("a turn by 6 for 7", "    vprord xmm1, xmm1, 7\n", "    vprord xmm1, xmm1, 6\n", FOLLOW),
    ("the block's words taken the other way", "  vshufps xmm4, xmm8, xmm9, 136\n  vshufps xmm5, xmm8, xmm9, 221\n  vmovups xmm8, xmmword ptr [rsi+0x20]",
     "  vshufps xmm4, xmm8, xmm9, 221\n  vshufps xmm5, xmm8, xmm9, 136\n  vmovups xmm8, xmmword ptr [rsi+0x20]", FOLLOW),
    ("six rounds", "  vpshufd xmm7, xmm7, 0x93\n  mov al, 7\n", "  vpshufd xmm7, xmm7, 0x93\n  mov al, 6\n", FOLLOW),
    ("a row of the state turned the other way", "  g(xmm4, xmm5)\n  vpshufd xmm0, xmm0, 0x93\n", "  g(xmm4, xmm5)\n  vpshufd xmm0, xmm0, 0x39\n", FOLLOW),
    ("the block's permutation changed in one word", "  vpblendd xmm9, xmm9, xmm8, 0xAA\n", "  vpblendd xmm9, xmm9, xmm8, 0xA8\n", FOLLOW),
    ("the halves of the state joined crosswise", "  vpxor xmm0, xmm0, xmm2\n  vpxor xmm1, xmm1, xmm3\n", "  vpxor xmm0, xmm0, xmm3\n  vpxor xmm1, xmm1, xmm2\n", FOLLOW),
    ("the counter and the length exchanged", "  vmovq xmm3, rcx\n  vmovq xmm4, rdx\n", "  vmovq xmm3, rdx\n  vmovq xmm4, rcx\n", FOLLOW),
    ("a word of the constants", "data one_iv = 0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A", "data one_iv = 0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53B", FOLLOW),
    ("the flags put one bit lower", "  shl rax, 32\n  add rdx, rax\n  vmovq xmm3, rcx", "  shl rax, 31\n  add rdx, rax\n  vmovq xmm3, rcx", FOLLOW),
    ("the whole of the length's register is taken", "  movzx eax, r8b\n  movzx edx, dl\n", "  movzx eax, r8b\n", ENTAIL),
    ("the last four words are not stored", STORES, "  vmovdqu xmmword ptr [rdi], xmm0\n" + END, HOLD),
    ("the two stores exchanged", STORES, "  vmovdqu xmmword ptr [rdi], xmm1\n  vmovdqu xmmword ptr [rdi+0x10], xmm0\n" + END, HOLD),
    ("a store four bytes on, past the run's end", STORES, STORES.replace("[rdi+0x10]", "[rdi+0x14]"), WORDS),
    ("a store into the block, which is only to be read", STORES, STORES.replace(END, "  vmovdqu xmmword ptr [rsi], xmm1\n" + END), NO_RUN),
    ("what was stored is read again", STORES, STORES.replace("  vmovdqu xmmword ptr [rdi+0x10], xmm1\n", "  vmovdqu xmm0, xmmword ptr [rdi]\n  vmovdqu xmmword ptr [rdi+0x10], xmm1\n"), AGAIN),
    ("the block read sixteen bytes on, past its end", "  vmovups xmm9, xmmword ptr [rsi+0x30]\n  vshufps xmm6, xmm8, xmm9, 136", "  vmovups xmm9, xmmword ptr [rsi+0x40]\n  vshufps xmm6, xmm8, xmm9, 136", WORDS),
    ("the block read two bytes on", "  vmovups xmm8, xmmword ptr [rsi]\n  vmovups xmm9, xmmword ptr [rsi+0x10]\n", "  vmovups xmm8, xmmword ptr [rsi+2]\n  vmovups xmm9, xmmword ptr [rsi+0x10]\n", WORDS),
]


def spec_text(change=lambda t: t):
    with open(os.path.join(KCHECK, "blake3.spec")) as f: spec = f.read()
    with open(os.path.join(HERE, "examples", "kernel", "kernel.contract")) as f: contract = f.read()
    return change(spec + "\n" + contract)


class Statement(unittest.TestCase):
    def lines(self, change=lambda t: t):
        return statement.statement(spec_text(change), [(os.path.join(KCHECK, "b3hashr.o"), SYMBOL)])

    def test_the_contract_in_the_accounts_terms(self):
        lines = self.lines()
        self.assertEqual([l for l in lines if l.split()[0] not in ("fn", "i", "def")], CONTRACT)
        self.assertEqual(sum(l.startswith("i ") for l in lines), 76)

    def test_a_contract_that_promises_more_or_other_than_is_read_is_refused(self):
        for what, old, new, why in (
                ("the trace depends on no byte of m", "trace depends on h, m", "trace depends on h", "the trace does not depend on the bytes of m"),
                ("the trace depends on no byte of h", "trace depends on h, m", "trace depends on m", "the trace does not depend on the bytes of h"),
                ("no line of what overlaps", "    requires no_overlap(h, m)\n", "", "does not say `requires no_overlap(h, m)`"),
                ("a part of the words", "ensures h = compress", "ensures h[0 .. 16] = compress", "of a part of a run of words"),
                ("a number returned too", "    stack 0\n", "    returns length\n    stack 0\n", "returns a number beside arguments of the kinds"),
                ("a kind not read", "m: block", "m: 16 words", "an argument of a kind the verifier in Lean does not read yet: m: 16 words"),
                # the machine of the account has every instruction; a processor has those of the kinds it has
                ("no line of what the processor must have", "    needs avx512\n", "", "holds instructions of a kind its contract does not say it needs: avx, avx512"),
                ("the processor is asked for too little", "    needs avx512\n", "    needs sse41\n", "holds instructions of a kind its contract does not say it needs: avx, avx512")):
            with self.subTest(what=what):
                with self.assertRaises(SystemExit) as e: self.lines(lambda t: (self.assertEqual(t.count(old), 1), t.replace(old, new))[1])
                self.assertIn(why, str(e.exception))


@unittest.skipUnless(LAKE, "Lean's lake is not installed")
class Kernel(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.dir = tempfile.mkdtemp(prefix="odekernel-")
        cls.obj = os.path.join(KCHECK, "b3hashr.o")
        cls.spec = spec_text()
        with open(os.path.join(HERE, "..", "wide", "one.ode")) as f: cls.source = f.read()
        cls.kept = os.path.join(HERE, "proofs", SYMBOL + ".proof")

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.dir)

    def path(self, name): return os.path.join(self.dir, name)

    def found(self, spec, obj, name="try"):
        """The prover's numbers; or, where it finds no proof, the verifier's last word."""
        try: return prove.prove(spec, [(obj, SYMBOL, "")], self.path(name + ".statement"), self.path(name + ".proof"))
        except SystemExit as e:
            said = str(e)
            self.assertTrue(said.startswith("prove: no proof of " + SYMBOL), said[:200])
            return said.split("\n", 1)[1]

    def test_shown_and_the_kept_proof_is_what_the_prover_finds(self):
        numbers = self.found(self.spec, self.obj, "shown")
        self.assertEqual(list(numbers), [SYMBOL])
        self.assertEqual(lean_verify.verify(self.spec, [(self.obj, SYMBOL)], self.kept), (True, "shown"))
        if os.environ.get("PYTHONHASHSEED") == "0":
            with open(self.kept) as f, open(self.path("shown.proof")) as g: self.assertEqual(f.read(), g.read())
        self.assertLess(os.path.getsize(self.kept), 1000)
        with open(self.path("shown.statement")) as f: lines = f.read().splitlines()
        self.assertIn("i 98 100 .mov 8 (.reg .rax) (.imm 0x7)", lines)              # the count of rounds, kept in a byte
        self.assertIn("i 282 284 .decb .rax", lines)
        # the kernel made again from its source is the same instructions, and is shown by the same proof
        odec.build(os.path.join(HERE, "..", "wide", "one.ode"), "compress1", self.path("one.o"))
        again = statement.statement(self.spec, [(self.path("one.o"), SYMBOL)])
        self.assertEqual([l for l in again if l.startswith("i ")], [l for l in lines if l.startswith("i ")])
        self.assertEqual(lean_verify.verify(self.spec, [(self.path("one.o"), SYMBOL)], self.kept), (True, "shown"))

    def test_a_contract_that_promises_less_is_shown_too(self):
        # (so the cases below are not refused for being changed: `stack 8` is true of a function that uses none)
        spec = self.spec.replace("    stack 0\n", "    stack 8\n"); self.assertNotEqual(spec, self.spec)
        self.assertEqual(lean_verify.verify(spec, [(self.obj, SYMBOL)], self.kept), (True, "shown"))

    def test_the_specification_or_the_contract_changed_in_one_place(self):
        for what, old, new, why in SPECS:
            with self.subTest(what=what):
                self.assertEqual(self.spec.count(old), 1)
                spec = self.spec.replace(old, new)
                self.assertFalse(lean_verify.verify(spec, [(self.obj, SYMBOL)], self.kept)[0], what)
                last = self.found(spec, self.obj)
                self.assertIsInstance(last, str, what)                      # no proof is found
                self.assertIn(why, last.split("\n")[0], what)

    def test_the_function_changed_in_one_place(self):
        for what, old, new, why in SOURCES:
            with self.subTest(what=what):
                self.assertEqual(self.source.count(old), 1)
                with open(self.path("changed.ode"), "w") as f: f.write(self.source.replace(old, new))
                odec.build(self.path("changed.ode"), "compress1", self.path("changed.o"))
                self.assertFalse(lean_verify.verify(self.spec, [(self.path("changed.o"), SYMBOL)], self.kept)[0], what)
                last = self.found(self.spec, self.path("changed.o"))
                self.assertIsInstance(last, str, what)
                self.assertIn(why, last.split("\n")[0], what)

    def test_the_proof_changed(self):
        with open(self.kept) as f: proof = f.read().splitlines()
        with open(self.path("s.statement"), "w") as f: f.write("\n".join(statement.statement(self.spec, [(self.obj, SYMBOL)])) + "\n")
        def said(lines):
            with open(self.path("c.proof"), "w") as f: f.write("".join(x + "\n" for x in lines))
            r = subprocess.run([lean_verify.EXE, lean_verify.TABLE, self.path("s.statement"), self.path("c.proof")], capture_output=True, text=True)
            self.assertEqual(r.returncode == 0, r.stdout == "shown\n", r.stdout[:200])
            return r.stdout
        self.assertEqual(said(proof), "shown\n")
        self.assertTrue(said(proof[:1]).startswith("need entail"), "with no line of proof the verifier asks for the first")
        kinds = {}
        for k in range(1, len(proof)):                                     # (the first line names the function)
            l = proof[k]
            w = l.split()
            trials = [("left out", None)]
            if w[0] == "s": trials.append(("a step's multiplier", " ".join(w[:2] + [str(int(w[2]) + 1)] + w[3:])))
            if w[0] == "p": trials.append(("a row it starts from", " ".join(w[:1] + [str(int(w[1]) + 1)] + w[2:])))
            for kind, new in trials:
                lines = list(proof)
                if new is None: del lines[k]
                else: lines[k] = new
                self.assertNotEqual(said(lines), "shown\n", (k, l, kind))
                kinds[kind] = kinds.get(kind, 0) + 1
        self.assertEqual(kinds, {"left out": len(proof) - 1, "a step's multiplier": 6, "a row it starts from": 4})


if __name__ == "__main__":
    unittest.main()
