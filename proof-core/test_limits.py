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

The hash's two one-block kernels are two of the fourteen functions of ../kcheck/b3hashr.o, which kcheck
takes 16 seconds to verify whole. Its own time for a kernel is measured with the kernel as the only function
verified in a process (as check_binary.py does it for each): 7 and 8 ms on the machine this was written on,
where the AVX-512 kernel takes 20 ms as the thirteenth of a whole run. The smaller number is the one used.

`b3l_node_out` calls the two kernels and is shown with them (a call is taken by the contract of a function
shown in the same run). Its kept proof is its own three lines; the run measured is of the three functions,
against kcheck's times for the three, one after the other.

The 16-way kernel (`blake3_servil_avx512_p16`, for every count of blocks, by its loop's place) is measured
the same way as the one-block kernels: kcheck's verifier with it as the only function verified in a process.
So are the 32-way kernel by each of its two entries (`blake3_servil_avx512_p32` and
`blake3_servil_avx512_k32`, for every count of blocks) and `b3l_pad`.

On November 18 the Lean verifier was five and six times slower on the two larger functions, and it was
seen only when the times were measured for a report. This test is so that it is seen at once.

    python3 test_limits.py        (skipped where Lean's `lake` is not installed)"""
import os, re, subprocess, sys, tempfile, time, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import built, lean_verify, statement, test_k32, test_kernel, test_node, test_p16, test_p32, test_pad
KCHECK = os.path.join(HERE, "..", "kcheck")
PROGRAMS = os.path.join(KCHECK, "programs")
# (the folder of ../kcheck/programs, the object, the specification, the function)
SHOWN = [("common", "odecommon.o", "common.spec", "ode_common"), ("adler32", "odeadler32.o", "adler32.spec", "ode_adler32"),
         ("adler32", "odeadler32.o", "adler32.spec", "ode_adler32_blocks"), ("adler32", "odeadler32.o", "adler32.spec", "ode_adler32_blocks4"),
         ("varint", "odevarint.o", "varint.spec", "ode_varint")]
KERNELS = [(test_kernel.AVX512, "the AVX-512 kernel"), (test_kernel.SSE, "the SSE4.1 kernel")]
# kcheck's verifier on one function of the hash's file, as check_binary.py's `main` does it for each: the
# arithmetic by the proofs the file carries, nothing searched for. Prints its time in milliseconds.
ONE = '''import sys, time
sys.path.insert(0, sys.argv[1])
import check_binary, kdecode, klin, varith
path, symbol = sys.argv[2], sys.argv[3]
check_binary.take(check_binary.carried(kdecode.Elf(path).bytes_of(".ode.proof")), None)
klin.Facts.PROOFS = varith.unpack(check_binary.ARITH[symbol]) if symbol in check_binary.ARITH else {}
t = time.time()
rows, what, _ = check_binary.check(path, symbol)
print(len(rows), 1000 * (time.time() - t), what)
'''
SIZE = 100_000          # bytes of a proof
TIMES = float(os.environ.get("ODE_LIMIT_TIMES", "5"))          # the Lean verifier's time over kcheck's (to see the test fail: ODE_LIMIT_TIMES=1)
SMALL = 0.015           # seconds: under this a program's start is most of the time


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Limits(unittest.TestCase):
    def test_no_proof_is_large_and_no_verification_five_times_slower_than_kchecks(self):
        built.built("odeverify")
        lines, kchecks = [], {}
        for folder, obj, spec, symbol in SHOWN + [(None, "b3hashr.o", k, k.symbol) for k, _ in KERNELS]:
            proof = os.path.join(HERE, "proofs", symbol + ".proof")
            if folder is None: obj, spec_text = os.path.join(KCHECK, obj), test_kernel.spec_text(contract=spec.contract)
            else:
                obj = os.path.join(PROGRAMS, folder, obj)
                with open(os.path.join(PROGRAMS, folder, spec)) as f: spec_text = f.read()
            size = os.path.getsize(proof)
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
                if folder is None:
                    r = subprocess.run([sys.executable, "-c", ONE, KCHECK, obj, symbol], capture_output=True, text=True)
                    said = r.stdout.split(None, 2)
                    self.assertEqual((r.returncode, said[0], said[2]), (0, str(spec.instructions), "a one-block kernel\n"), (r.stdout[-300:], r.stderr[-300:]))
                    took = float(said[1]) / 1000
                else:
                    r = subprocess.run([sys.executable, os.path.join(PROGRAMS, "check_file.py"), obj, "--maintain"], capture_output=True, text=True)
                    m = re.search(r"^\s+" + re.escape(symbol) + r"\s+at\s.*?([0-9.]+) ms\s+meets its public contract", r.stdout, re.M)
                    self.assertTrue(m, (symbol, r.stdout[-300:]))
                    took = float(m.group(1)) / 1000
                python = took if python is None else min(python, took)
            kchecks[symbol] = python
            name = symbol if folder is not None else dict((k.symbol, n) for k, n in KERNELS)[symbol]
            lines.append(f"  {name:<20} the proof {size:>6} bytes; the Lean verifier {1000 * lean:6.1f} ms; kcheck's {1000 * python:5.1f} ms; {lean / python:4.1f} times")
            with self.subTest(symbol=symbol):
                self.assertLessEqual(size, SIZE, f"{symbol}: the proof is {size} bytes")
                self.assertTrue(lean <= SMALL or lean <= TIMES * python, f"{symbol}: the Lean verifier takes {1000 * lean:.1f} ms, kcheck's {1000 * python:.1f} ms")
        # the function that calls both kernels, with them
        symbols = [test_node.NODE, test_node.AVX512, test_node.SSE41]
        size = os.path.getsize(os.path.join(HERE, "proofs", test_node.NODE + ".proof"))
        with tempfile.TemporaryDirectory() as d:
            path, proof = os.path.join(d, "statement"), os.path.join(d, "proof")
            with open(path, "w") as f: f.write("\n".join(statement.statement(test_node.spec_text(), test_node.FUNCTIONS)) + "\n")
            with open(proof, "w") as out:
                for symbol in symbols:
                    with open(os.path.join(HERE, "proofs", symbol + ".proof")) as f: out.write(f.read())
            lean = None
            for _ in range(7):
                t = time.time()
                r = subprocess.run([lean_verify.EXE, lean_verify.TABLE, path, proof], capture_output=True, text=True)
                took = time.time() - t
                self.assertEqual(r.stdout, "shown\n", test_node.NODE)
                lean = took if lean is None else min(lean, took)
        python = None
        for _ in range(5):
            r = subprocess.run([sys.executable, "-c", ONE, KCHECK, test_node.OBJ, test_node.NODE], capture_output=True, text=True)
            said = r.stdout.split(None, 2)
            self.assertEqual((r.returncode, said[0], said[2]), (0, "18", "everything its contract allows\n"), (r.stdout[-300:], r.stderr[-300:]))
            took = float(said[1]) / 1000
            python = took if python is None else min(python, took)
        three = python + kchecks[test_node.AVX512] + kchecks[test_node.SSE41]
        lines.append(f"  {'b3l_node_out':<20} the proof {size:>6} bytes; with the two kernels: the Lean verifier {1000 * lean:6.1f} ms; "
                     f"kcheck's {1000 * three:5.1f} ms ({1000 * python:.1f} ms its own); {lean / three:4.1f} times")
        with self.subTest(symbol=test_node.NODE):
            self.assertLessEqual(size, SIZE)
            self.assertTrue(lean <= SMALL or lean <= TIMES * three, f"b3l_node_out: the Lean verifier takes {1000 * lean:.1f} ms, kcheck's {1000 * three:.1f} ms")
        # the 16-way kernel, for every count of blocks
        size = os.path.getsize(os.path.join(HERE, "proofs", test_p16.NAME + ".proof"))
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "statement")
            with open(path, "w") as f: f.write("\n".join(statement.statement(test_p16.spec_text(), [(test_p16.OBJ, test_p16.NAME)])) + "\n")
            lean = None
            for _ in range(7):
                t = time.time()
                r = subprocess.run([lean_verify.EXE, lean_verify.TABLE, path, os.path.join(HERE, "proofs", test_p16.NAME + ".proof")], capture_output=True, text=True)
                took = time.time() - t
                self.assertEqual(r.stdout, "shown\n", test_p16.NAME)
                lean = took if lean is None else min(lean, took)
        python = None
        for _ in range(5):
            r = subprocess.run([sys.executable, "-c", ONE, KCHECK, test_p16.OBJ, test_p16.NAME], capture_output=True, text=True)
            said = r.stdout.split(None, 2)
            self.assertEqual((r.returncode, said[0], said[2]), (0, "460", "a wide kernel: every number of blocks, by induction at the place its proof names\n"), (r.stdout[-300:], r.stderr[-300:]))
            took = float(said[1]) / 1000
            python = took if python is None else min(python, took)
        lines.append(f"  {'the 16-way kernel':<20} the proof {size:>6} bytes; the Lean verifier {1000 * lean:6.1f} ms; kcheck's {1000 * python:5.1f} ms; {lean / python:4.1f} times")
        with self.subTest(symbol=test_p16.NAME):
            self.assertLessEqual(size, SIZE)
            self.assertTrue(lean <= SMALL or lean <= TIMES * python, f"the 16-way kernel: the Lean verifier takes {1000 * lean:.1f} ms, kcheck's {1000 * python:.1f} ms")
        # the 32-way kernel, for every count of blocks
        size = os.path.getsize(os.path.join(HERE, "proofs", test_p32.NAME + ".proof"))
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "statement")
            with open(path, "w") as f: f.write("\n".join(statement.statement(test_p32.spec_text(), [(test_p32.OBJ, test_p32.NAME)])) + "\n")
            lean = None
            for _ in range(7):
                t = time.time()
                r = subprocess.run([lean_verify.EXE, lean_verify.TABLE, path, os.path.join(HERE, "proofs", test_p32.NAME + ".proof")], capture_output=True, text=True)
                took = time.time() - t
                self.assertEqual(r.stdout, "shown\n", test_p32.NAME)
                lean = took if lean is None else min(lean, took)
        python = None
        for _ in range(5):
            r = subprocess.run([sys.executable, "-c", ONE, KCHECK, test_p32.OBJ, test_p32.NAME], capture_output=True, text=True)
            said = r.stdout.split(None, 2)
            # (kcheck counts the three instructions of the other entry, which lie before it, with its 699)
            self.assertEqual((r.returncode, said[0], said[2]), (0, "702", "a wide kernel: every number of blocks, by induction at the place its proof names\n"), (r.stdout[-300:], r.stderr[-300:]))
            took = float(said[1]) / 1000
            python = took if python is None else min(python, took)
        lines.append(f"  {'the 32-way kernel':<20} the proof {size:>6} bytes; the Lean verifier {1000 * lean:6.1f} ms; kcheck's {1000 * python:5.1f} ms; {lean / python:4.1f} times")
        with self.subTest(symbol=test_p32.NAME):
            self.assertLessEqual(size, SIZE)
            self.assertTrue(lean <= SMALL or lean <= TIMES * python, f"the 32-way kernel: the Lean verifier takes {1000 * lean:.1f} ms, kcheck's {1000 * python:.1f} ms")
        # the 32-way kernel by the entry the hash calls, for every count of blocks
        size = os.path.getsize(os.path.join(HERE, "proofs", test_k32.NAME + ".proof"))
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "statement")
            with open(path, "w") as f: f.write("\n".join(statement.statement(test_k32.spec_text(), [(test_k32.OBJ, test_k32.NAME)])) + "\n")
            lean = None
            for _ in range(7):
                t = time.time()
                r = subprocess.run([lean_verify.EXE, lean_verify.TABLE, path, os.path.join(HERE, "proofs", test_k32.NAME + ".proof")], capture_output=True, text=True)
                took = time.time() - t
                self.assertEqual(r.stdout, "shown\n", test_k32.NAME)
                lean = took if lean is None else min(lean, took)
        python = None
        for _ in range(5):
            r = subprocess.run([sys.executable, "-c", ONE, KCHECK, test_k32.OBJ, test_k32.NAME], capture_output=True, text=True)
            said = r.stdout.split(None, 2)
            self.assertEqual((r.returncode, said[0], said[2]), (0, "702", "a wide kernel: every number of blocks, by induction at the place its proof names\n"), (r.stdout[-300:], r.stderr[-300:]))
            took = float(said[1]) / 1000
            python = took if python is None else min(python, took)
        lines.append(f"  {'the 32-way kernel':<20} the proof {size:>6} bytes; the Lean verifier {1000 * lean:6.1f} ms; kcheck's {1000 * python:5.1f} ms; {lean / python:4.1f} times  (the entry the hash calls)")
        with self.subTest(symbol=test_k32.NAME):
            self.assertLessEqual(size, SIZE)
            self.assertTrue(lean <= SMALL or lean <= TIMES * python, f"the 32-way kernel's other entry: the Lean verifier takes {1000 * lean:.1f} ms, kcheck's {1000 * python:.1f} ms")
        # b3l_pad, by its loop's place
        size = os.path.getsize(os.path.join(HERE, "proofs", test_pad.PAD + ".proof"))
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "statement")
            with open(path, "w") as f: f.write("\n".join(statement.statement(test_pad.spec_text(), [(test_pad.OBJ, test_pad.PAD)])) + "\n")
            lean = None
            for _ in range(7):
                t = time.time()
                r = subprocess.run([lean_verify.EXE, lean_verify.TABLE, path, os.path.join(HERE, "proofs", test_pad.PAD + ".proof")], capture_output=True, text=True)
                took = time.time() - t
                self.assertEqual(r.stdout, "shown\n", test_pad.PAD)
                lean = took if lean is None else min(lean, took)
        python = None
        for _ in range(5):
            r = subprocess.run([sys.executable, "-c", ONE, KCHECK, test_pad.OBJ, test_pad.PAD], capture_output=True, text=True)
            said = r.stdout.split(None, 2)
            self.assertEqual((r.returncode, said[0]), (0, "39"), (r.stdout[-300:], r.stderr[-300:]))
            took = float(said[1]) / 1000
            python = took if python is None else min(python, took)
        lines.append(f"  {'b3l_pad':<20} the proof {size:>6} bytes; the Lean verifier {1000 * lean:6.1f} ms; kcheck's {1000 * python:5.1f} ms; {lean / python:4.1f} times")
        with self.subTest(symbol=test_pad.PAD):
            self.assertLessEqual(size, SIZE)
            self.assertTrue(lean <= SMALL or lean <= TIMES * python, f"b3l_pad: the Lean verifier takes {1000 * lean:.1f} ms, kcheck's {1000 * python:.1f} ms")
        print("\nthe limits (a proof under 100 kB; verifying no more than five times kcheck's time):\n" + "\n".join(lines), file=sys.stderr)


if __name__ == "__main__":
    unittest.main()
