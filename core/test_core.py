#!/usr/bin/env python3
"""The checks of the table of instructions and of the rules that read it, each with a control that it can fail.

    python3 core/test_core.py

1. Every rule on symbols (step.py) against its primitive's meaning on numbers (meaning.py), on kfn.py's
   machine and on kbyte.py's; rules made wrong are caught.
2. Every row against this machine's processor (cross.py; x86-64 Linux with AVX-512 and clang, else
   skipped): as an assembler writes its ASM, and in each way the table itself writes it in bytes; a table
   with rows and ways made wrong has each of them reported.
3. Every row's ASM against its bytes: what an assembler writes for an instance is read as that row, with the
   same registers and numbers (decoder.py).
4. The verifier goes by the table: with a row or a way made wrong, or a way taken out, a shipped file is no
   longer shown.
(Before the verifier's own code for each instruction was taken out, the table was run beside it on every
instruction step of every shipped file and of their single-bit changes, the two machines compared whole
after each: shadow.py, in this repository's history at commit 015750a. Before the reader of code written by
hand was taken out, the reader by the table read beside it every instruction of every shipped file and of
their single-bit changes: decode_diff.py, at commit 1eac41c.)"""
import contextlib, io, os, platform, shutil, subprocess, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import meaning, step, table        # (these put ../kcheck on the path)
import kbyte, kfn

NATIVE = platform.system() == "Linux" and platform.machine() == "x86_64" and shutil.which("clang") and "avx512vl" in open("/proc/cpuinfo").read()
WRONG = [("X = lanes(Y.2, Z.2, Y.3, Z.3)", "X = lanes(Y.2, Z.2, Z.3, Y.3)", "unpckhdq"), ("D = shr64(D, I); zf", "D = shl64(D, I); zf", "shr64_ri"),
         ("zf = equal(D, S); cf = below(D, S)", "zf = equal(D, S); cf = below(S, D)", "cmp64_rr"), ("X = blend4(Y, Z, I)", "X = blend4(Z, Y, I)", "pblendd128"),
         ("D = low8(S)", "D = S", "movzx8_rr"), ("| jump I if not cf", "| jump I if cf", "jae"), ("mem64(rsp, 0) = P", "mem64(rsp, 8) = P", "push"),
         ("in_quarters(Y512, Z512, 2, 3, 6, 7)", "in_quarters(Y512, Z512, 2, 3, 7, 6)", "unpckhqdq512"), ("| D = at(B, N)", "| D = at(B, N); zf = equal(D, 0)", "lea"),
         ("choose16(M, each32(add32, Y512, Z512), X512)", "choose16(M, X512, each32(add32, Y512, Z512))", "paddd512k")]
# ways made wrong: another instruction's bytes, operands exchanged
WAYS = [("= REX.W 29 /r ; rm=D reg=S", "= REX.W 2B /r ; rm=D reg=S", "sub64_rr"), ("= REX.W 81 /4 sd ; rm=D imm=I", "= REX.W 81 /1 sd ; rm=D imm=I", "and64_ri"),
        ("= EVEX.512.66.0F.W0 62 /r ; reg=X vvvv=Y rm=Z", "= EVEX.512.66.0F.W0 6A /r ; reg=X vvvv=Y rm=Z", "unpckldq512"), ("= 50+r ; r=P", "= 58+r ; r=P", "push"),
        ("= 74 rel8 ; rel=I", "= 75 rel8 ; rel=I", "je"), ("= VEX.128.0F.W0 C6 /r cb ; reg=X vvvv=Y rm=Z imm=I", "= VEX.128.0F.W0 C6 /r cb ; reg=X vvvv=Z rm=Y imm=I", "shufps128")]
KCHECK = os.path.join(HERE, "..", "kcheck")


class Core(unittest.TestCase):
    def test_every_rule_on_symbols_is_its_primitives_meaning_on_numbers(self):
        for of in (kfn.Machine, kbyte.Machine):
            with contextlib.redirect_stdout(io.StringIO()) as out: bad = meaning.test(6000, of=of)
            self.assertEqual(bad, 0, out.getvalue()[-1500:])
            self.assertIn("every rule answered", out.getvalue())

    def test_rules_made_wrong_are_caught(self):
        def wrong(name, rule):
            def rules(m):
                R = step.rules(m); right = R[name]
                R[name] = lambda *a: rule(right, m, *a)
                return R
            return rules
        q = step.q
        for name, rule in (
                ("shr64", lambda right, m, x, n: q(x) if q(x)[0] == "p" else right(x, n)),                                   # packed bytes not moved down
                ("shr64", lambda right, m, x, n: ("t", q(x)[1]) if q(x)[0] == "pair" and n == 32 else right(x, n)),            # a counter's low word for its high one
                ("and64", lambda right, m, x, y: q(x) if q(x)[0] == "p" else right(x, y)),                                    # the low byte not taken
                ("equal", lambda right, m, x, y: ("zero", step.lin(q(x)) + step.lin(q(y))) if step.lin(q(x)) is not None and step.lin(q(y)) is not None else right(x, y)),
                ("lanes_of64", lambda right, m, v: (lambda r: (r[1], r[0], r[2], r[3]))(right(v))),                            # the two words exchanged
                ("choose16", lambda right, m, k, a, b: right(k, b, a)),
                ("ror32", lambda right, m, x, n: right(x, n % 31 + 1)),
                ("in_quarters", lambda right, m, a, b, *pick: right(b, a, *pick))):
            with contextlib.redirect_stdout(io.StringIO()): bad = meaning.test(1500, rules=wrong(name, rule), say=False)
            self.assertGreater(bad, 0, name)

    @unittest.skipUnless(NATIVE, "no x86-64 Linux with AVX-512 and clang: the rows are not run on a processor")
    def test_every_row_is_what_this_processor_does(self):
        with tempfile.TemporaryDirectory() as d:
            r = subprocess.run([sys.executable, os.path.join(HERE, "cross.py"), "--cases", "100", "--work", d], capture_output=True, text=True)
            self.assertEqual(r.returncode, 0, r.stdout[-2000:] + r.stderr[-500:])
            self.assertIn("every row and way run is what the processor does", r.stdout)
            self.assertNotIn("ways not run: " + "nop", r.stdout)

    @unittest.skipUnless(NATIVE, "no x86-64 Linux with AVX-512 and clang: the rows are not run on a processor")
    def test_rows_made_wrong_are_each_reported(self):
        with open(os.path.join(HERE, "x86.tab")) as f: text = f.read()
        for old, new, _ in WRONG + WAYS:
            self.assertEqual(text.count(old), 1, old); text = text.replace(old, new)
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "wrong.tab")
            with open(path, "w") as f: f.write(text)
            r = subprocess.run([sys.executable, os.path.join(HERE, "cross.py"), "--cases", "60", "--work", d, "--table", path], capture_output=True, text=True)
            self.assertEqual(r.returncode, 1, r.stdout[-1500:])
            for _, _, name in WRONG: self.assertIn(f"DIFFERS {name}:", r.stdout)
            for _, new, name in WAYS: self.assertIn(f"DIFFERS {name} {new}:", r.stdout)

    @unittest.skipUnless(shutil.which("clang"), "no clang: the rows' instances are not assembled")
    def test_the_decoder_reads_each_rows_instances_as_that_row(self):
        r = subprocess.run([sys.executable, os.path.join(HERE, "decoder.py"), "--cases", "30"], capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stdout[-2000:] + r.stderr[-500:])
        self.assertIn(", 0 otherwise than as their row; it stops at 0 ", r.stdout)

    def test_the_verifier_goes_by_the_table(self):
        """A row made wrong, or a way of writing one, and a shipped file is no longer shown; bytes the table does not write are not verified."""
        check = [sys.executable, os.path.join("programs", "check_file.py"), os.path.join("programs", "common", "odecommon.o")]
        r = subprocess.run(check, capture_output=True, text=True, cwd=KCHECK)
        self.assertEqual(r.returncode, 0, r.stdout[-800:] + r.stderr[-500:])
        with open(os.path.join(HERE, "x86.tab")) as f: text = f.read()
        for old, new in (("| jump I if not cf", "| jump I if cf"), ("| D = mem8(B, N)", "| D = mem64(B, N)"), ("             = 0F B6 /r ; reg=D mem=B+N\n", ""),
                         ("= REX.W 89 /r ; rm=D reg=S", "= REX.W 89 /r ; rm=S reg=D"), ("= 73 rel8 ; rel=I", "= 72 rel8 ; rel=I")):
            self.assertEqual(text.count(old), 1, old)
            with tempfile.TemporaryDirectory() as d:
                path = os.path.join(d, "wrong.tab")
                with open(path, "w") as f: f.write(text.replace(old, new))
                r = subprocess.run(check, capture_output=True, text=True, cwd=KCHECK, env=dict(os.environ, ODE_TABLE=path))
            self.assertEqual(r.returncode, 1, old + r.stdout[-800:])
            self.assertIn("NOT shown", r.stdout, old)


if __name__ == "__main__":
    unittest.main()
