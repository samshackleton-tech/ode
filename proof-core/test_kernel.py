#!/usr/bin/env python3
"""The hash's one-block kernel, `blake3_servil_compress_in_place_avx512`, as far as the verifier in Lean goes.

    python3 test_kernel.py        (skipped where Lean's `lake` is not installed)

So far: what is to be shown of it can be said. Its contract gives it eight words to read and write (`h: cv`),
sixteen to read (`m: block`), a counter and two low bytes of registers, and promises `h = compress(h, m, t,
length, flags)`. statement.py writes that in the account's terms: 32 bytes read and written, 64 bytes read,
three numbers, and the run `h` at the return being the bytes of the words `compress` gives of the words of
the bytes at entry. The verifier refuses the function: it has no rule yet for a row over a vector register.
Nothing is shown here yet."""
import os, subprocess, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import built, lean_verify, prove, statement
KCHECK = os.path.join(HERE, "..", "kcheck")
LAKE = lean_verify.LAKE
SYMBOL = "blake3_servil_compress_in_place_avx512"
CONTRACT = ["arg h inout 32", "arg m fixed 64", "arg length number", "arg t number", "arg flags number", "needs avx512",
            "ensuresw h (call bytes_of (call compress (call words (name h)) (call words (name m)) (call counter (name t)) "
            "(bin % (name length) (num 256)) (bin % (name flags) (num 256))))", "stack 0"]


def spec_text(change=lambda t: t):
    with open(os.path.join(KCHECK, "blake3.spec")) as f: spec = f.read()
    with open(os.path.join(HERE, "examples", "kernel", "kernel.contract")) as f: contract = f.read()
    return spec + "\n" + change(contract)


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
                ("a kind not read", "m: block", "m: 16 words", "an argument of a kind the verifier in Lean does not read yet: m: 16 words")):
            with self.subTest(what=what):
                with self.assertRaises(SystemExit) as e: self.lines(lambda t: (self.assertIn(old, t), t.replace(old, new))[1])
                self.assertIn(why, str(e.exception))


@unittest.skipUnless(LAKE, "Lean's lake is not installed")
class Verifier(unittest.TestCase):
    def test_the_verifier_refuses_the_kernel_so_far(self):
        built.built("odeverify")
        d = tempfile.mkdtemp()
        st, proof = os.path.join(d, "k.statement"), os.path.join(d, "k.proof")
        with open(st, "w") as f: f.write("\n".join(Statement().lines()) + "\n")
        with open(proof, "w") as f: f.write(f"for {SYMBOL}\n")
        r = subprocess.run([prove.EXE, prove.TABLE, st, proof], capture_output=True, text=True)
        self.assertEqual((r.returncode, r.stdout), (1, f"refused: a row over a vector register: not here yet\nin {SYMBOL}\n"))


if __name__ == "__main__":
    unittest.main()
