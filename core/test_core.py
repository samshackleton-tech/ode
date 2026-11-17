#!/usr/bin/env python3
"""The table's checks, each with a control that it can fail.

    python3 core/test_core.py

1. The symbolic rules against the primitives' meaning on numbers (sym.py for the vector lanes, sym64.py for
   today's rules of 64-bit registers), and a rule made wrong is caught.
2. Every row against this machine's processor (cross.py; x86-64 Linux with AVX-512 and clang, else
   skipped), and a table with rows made wrong has each of them reported.
3. The table beside today's verifier (shadow.py) on the whole of ../kcheck/b3hashr.o and of the eight program
   files: every instruction step leaves the same machine; and a row made wrong shows."""
import contextlib, io, os, platform, shutil, subprocess, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import sym, sym64, table

NATIVE = platform.system() == "Linux" and platform.machine() == "x86_64" and shutil.which("clang") and "avx512vl" in open("/proc/cpuinfo").read()
WRONG = [("X = lanes(Y.2, Z.2, Y.3, Z.3)", "X = lanes(Y.2, Z.2, Z.3, Y.3)", "unpckhdq"), ("D = shr64(D, I); zf", "D = shl64(D, I); zf", "shr64_ri"),
         ("zf = equal(D, S); cf = below(D, S)", "zf = equal(D, S); cf = below(S, D)", "cmp64_rr"), ("X = blend4(Y, Z, I)", "X = blend4(Z, Y, I)", "pblendd128"),
         ("D = low8(S)", "D = S", "movzx8_rr"), ("| jump I if not cf", "| jump I if cf", "jae"), ("mem64(rsp, 0) = P", "mem64(rsp, 8) = P", "push"),
         ("in_quarters(Y512, Z512, 2, 3, 6, 7)", "in_quarters(Y512, Z512, 2, 3, 7, 6)", "unpckhqdq512"), ("| D = at(B, N)", "| D = at(B, N); zf = equal(D, 0)", "lea"),
         ("choose16(M, each32(add32, Y512, Z512), X512)", "choose16(M, X512, each32(add32, Y512, Z512))", "paddd512k")]
PROGRAMS = ["common", "adler32", "varint", "inet", "utf8", "base64", "frame", "lz4"]
SAME = r"shadow: \d+ instruction steps by the verifier and by the table: [1-9]\d* the same, 0 differ, 0 the table refuses, 0 the table answers where the verifier refuses"


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
            self.assertIn("every row run is what the processor does", r.stdout)

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

    def test_the_table_does_every_instruction_of_the_hash_file_as_todays_verifier_does(self):
        r = subprocess.run([sys.executable, os.path.join(HERE, "shadow.py")], capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stdout[-1500:] + r.stderr[-500:])
        self.assertIn("the verification's exit: 0", r.stdout)
        self.assertRegex(r.stdout, SAME)

    def test_and_of_the_program_files(self):
        for name in PROGRAMS:
            r = subprocess.run([sys.executable, os.path.join(HERE, "shadow.py"), "--file", f"programs/{name}/ode{name}.o"], capture_output=True, text=True)
            self.assertEqual(r.returncode, 0, name + r.stdout[-1500:] + r.stderr[-500:])
            self.assertIn("the verification's exit: 0", r.stdout, name)
            self.assertRegex(r.stdout, SAME, name)

    def test_a_row_made_wrong_shows_beside_todays_verifier(self):
        with open(os.path.join(HERE, "x86.tab")) as f: text = f.read()
        old = "| jump I if not cf"
        self.assertEqual(text.count(old), 1)
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "wrong.tab")
            with open(path, "w") as f: f.write(text.replace(old, "| jump I if cf"))
            r = subprocess.run([sys.executable, os.path.join(HERE, "shadow.py"), "--file", "programs/common/odecommon.o", "--list"], capture_output=True, text=True, env=dict(os.environ, ODE_TABLE=path))
        self.assertEqual(r.returncode, 1, r.stdout[-1500:])
        self.assertIn("DIFFERS", r.stdout)


if __name__ == "__main__":
    unittest.main()
