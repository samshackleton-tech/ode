#!/usr/bin/env python3
"""The table's checks, each with a control that it can fail.

    python3 core/test_core.py

1. The symbolic rules against the primitives' meaning on numbers (sym.py for the vector lanes, sym64.py for
   today's rules of 64-bit registers), and a rule made wrong is caught.
2. Every row against this machine's processor (cross.py; x86-64 Linux with AVX-512 and clang, else
   skipped), and a table with rows made wrong has each of them reported.
3. The table beside today's verifier on the whole of ../kcheck/b3hashr.o (shadow.py): no difference."""
import contextlib, io, os, platform, shutil, subprocess, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import sym, sym64, table

NATIVE = platform.system() == "Linux" and platform.machine() == "x86_64" and shutil.which("clang") and "avx512vl" in open("/proc/cpuinfo").read()
WRONG = [("X = lanes(Y.2, Z.2, Y.3, Z.3)", "X = lanes(Y.2, Z.2, Z.3, Y.3)", "unpckhdq"), ("D = shr64(D, I); zf", "D = shl64(D, I); zf", "shr64_ri"),
         ("zf = equal(D, S); cf = below(D, S)", "zf = equal(D, S); cf = below(S, D)", "cmp64_rr"), ("X = blend4(Y, Z, I)", "X = blend4(Z, Y, I)", "pblendd128"),
         ("D = low8(S)", "D = S", "movzx8_rr")]


class Core(unittest.TestCase):
    def test_the_symbolic_rules_are_the_meaning_on_numbers(self):
        with contextlib.redirect_stdout(io.StringIO()): bad = sym.test(800)
        self.assertEqual(bad, 0)

    def test_a_rule_made_wrong_is_caught(self):
        real = sym.rules
        def wrong(T):
            r = real(T); r["ror32"] = sym.whole(lambda x, n: T.ror(x, (n + 1) % 32) if (n + 1) % 32 else x); return r
        sym.rules = wrong
        try:
            with contextlib.redirect_stdout(io.StringIO()): bad = sym.test(100)
            self.assertGreater(bad, 0)
        finally: sym.rules = real

    def test_the_rules_for_64_bit_registers_are_the_meaning_on_numbers(self):
        with contextlib.redirect_stdout(io.StringIO()) as out: bad = sym64.test(6000)
        self.assertEqual(bad, 0, out.getvalue()[-1500:])
        self.assertIn(f"each of the {len(sym64.CASES)} cases of the rules was compared", out.getvalue())

    def test_a_rule_for_64_bit_registers_made_wrong_is_caught(self):
        real = sym64.Stub.RULE
        def wrong(m, op, x, y):                 # a counter moved down 32 bits: its low word, where the high one is meant
            return ("t", x[1]) if op == "shr" and x[0] == "pair" and y[1] == 32 else real(m, op, x, y)
        sym64.Stub.RULE = staticmethod(wrong)
        try:
            with contextlib.redirect_stdout(io.StringIO()): bad = sym64.test(3000)
            self.assertGreater(bad, 0)
        finally: sym64.Stub.RULE = staticmethod(real)

    @unittest.skipUnless(NATIVE, "no x86-64 Linux with AVX-512 and clang: the rows are not run on a processor")
    def test_every_row_is_what_this_processor_does(self):
        with tempfile.TemporaryDirectory() as d:
            r = subprocess.run([sys.executable, os.path.join(HERE, "cross.py"), "--cases", "100", "--work", d], capture_output=True, text=True)
            self.assertEqual(r.returncode, 0, r.stdout[-2000:] + r.stderr[-500:])
            self.assertIn("every row is what the processor does", r.stdout)

    @unittest.skipUnless(NATIVE, "no x86-64 Linux with AVX-512 and clang: the rows are not run on a processor")
    def test_rows_made_wrong_are_each_reported(self):
        with open(os.path.join(HERE, "x86.tab")) as f: text = f.read()
        for old, new, _ in WRONG:
            self.assertEqual(text.count(old), 1, old); text = text.replace(old, new)
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "wrong.tab")
            with open(path, "w") as f: f.write(text)
            r = subprocess.run([sys.executable, os.path.join(HERE, "cross.py"), "--cases", "60", "--work", d, "--table", path], capture_output=True, text=True)
            self.assertEqual(r.returncode, 1, r.stdout[-1500:])
            for _, _, name in WRONG: self.assertIn(f"DIFFERS {name}:", r.stdout)

    def test_the_table_and_todays_verifier_agree_on_the_hash_file(self):
        r = subprocess.run([sys.executable, os.path.join(HERE, "shadow.py")], capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stdout[-1500:] + r.stderr[-500:])
        self.assertRegex(r.stdout, r"shadow: \d+ instructions run by kfn.py, [1-9]\d* of them also by the table, 0 differ")


if __name__ == "__main__":
    unittest.main()
