#!/usr/bin/env python3
"""The two limits set for the verifier in Lean, as a test (Sam, November 18, 2026): stop and report if a
proof passes hundreds of kilobytes, or if verifying is more than five times slower than today.

"Today" is the verifier in Python that a reader uses (../kcheck), which goes by the proofs a shipped file
carries. For each shipped function the Lean verifier shows, this measures, on this machine and one after
the other:

    the kept proof's size                              (the limit here: 100 kB, well under the line)
    a whole run of the Lean verifier on it             (the program started, three files read; the best of 7)
    kcheck's verifier on the same function             (its own time for that function; the best of 5)

and fails where the Lean verifier takes more than five times kcheck's time. (Under 15 ms the two are not
compared: a program's start is most of it.) The numbers are printed, so every run of the tests has them.

On November 18 the Lean verifier was five and six times slower on the two larger functions, and it was
seen only when the times were measured for a report. This test is so that it is seen at once.

    python3 test_limits.py        (skipped where Lean's `lake` is not installed)"""
import os, re, subprocess, sys, tempfile, time, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import built, lean_verify, statement
PROGRAMS = os.path.join(HERE, "..", "kcheck", "programs")
# (the folder of ../kcheck/programs, the object, the specification, the function)
SHOWN = [("common", "odecommon.o", "common.spec", "ode_common"), ("adler32", "odeadler32.o", "adler32.spec", "ode_adler32"),
         ("adler32", "odeadler32.o", "adler32.spec", "ode_adler32_blocks"), ("adler32", "odeadler32.o", "adler32.spec", "ode_adler32_blocks4"),
         ("varint", "odevarint.o", "varint.spec", "ode_varint")]
SIZE = 100_000          # bytes of a proof
TIMES = float(os.environ.get("ODE_LIMIT_TIMES", "5"))          # the Lean verifier's time over kcheck's (to see the test fail: ODE_LIMIT_TIMES=1)
SMALL = 0.015           # seconds: under this a program's start is most of the time


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Limits(unittest.TestCase):
    def test_no_proof_is_large_and_no_verification_five_times_slower_than_kchecks(self):
        built.built("odeverify")
        lines = []
        for folder, obj, spec, symbol in SHOWN:
            obj, spec, proof = os.path.join(PROGRAMS, folder, obj), os.path.join(PROGRAMS, folder, spec), os.path.join(HERE, "proofs", symbol + ".proof")
            size = os.path.getsize(proof)
            with open(spec) as f: spec_text = f.read()
            with tempfile.TemporaryDirectory() as d:
                path = os.path.join(d, "statement")
                with open(path, "w") as f: f.write("\n".join(statement.statement(spec_text, [(obj, symbol)])) + "\n")
                lean = None
                for _ in range(7):
                    t = time.time()
                    r = subprocess.run([lean_verify.EXE, lean_verify.TABLE, path, proof], capture_output=True, text=True)
                    took = time.time() - t
                    self.assertEqual(r.stdout, "shown\n", symbol)
                    lean = took if lean is None else min(lean, took)
            python = None
            for _ in range(5):
                r = subprocess.run([sys.executable, os.path.join(PROGRAMS, "check_file.py"), obj, "--maintain"], capture_output=True, text=True)
                m = re.search(r"^\s+" + re.escape(symbol) + r"\s+at\s.*?([0-9.]+) ms\s+meets its public contract", r.stdout, re.M)
                self.assertTrue(m, (symbol, r.stdout[-300:]))
                took = float(m.group(1)) / 1000
                python = took if python is None else min(python, took)
            lines.append(f"  {symbol:<20} the proof {size:>6} bytes; the Lean verifier {1000 * lean:6.1f} ms; kcheck's {1000 * python:5.1f} ms; {lean / python:4.1f} times")
            with self.subTest(symbol=symbol):
                self.assertLessEqual(size, SIZE, f"{symbol}: the proof is {size} bytes")
                self.assertTrue(lean <= SMALL or lean <= TIMES * python, f"{symbol}: the Lean verifier takes {1000 * lean:.1f} ms, kcheck's {1000 * python:.1f} ms")
        print("\nthe limits (a proof under 100 kB; verifying no more than five times kcheck's time):\n" + "\n".join(lines), file=sys.stderr)


if __name__ == "__main__":
    unittest.main()
