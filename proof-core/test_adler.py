#!/usr/bin/env python3
"""A second shipped function in the verifier in Lean (Core.lean): `ode_adler32` of
../kcheck/programs/adler32/odeadler32.o, the Adler-32 checksum, against its public contract. Its
specification is two sequences, each a remainder by 65521 of the one before; statement.py writes a sequence
as the definition it is. The loop's place says that the two sums are the sequences' values at the place
reached, and the proof shows it again each time round by the remainder's two unknowns (x = 65521 q + r).
With the function, the specification, the contract or the place changed in one place it is not shown, nor
does the prover find a proof (it is given four times the runs of the verifier it finds the right proof in).

    python3 test_adler.py        (skipped where Lean's `lake` is not installed)"""
import os, shutil, subprocess, sys, tempfile, time, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lean_verify, prove, statement
ADLER = os.path.join(HERE, "..", "kcheck", "programs", "adler32")
LAKE = lean_verify.LAKE
STATEMENT = ("fn", "i", "arg", "returns", "stack", "def")    # the kinds of line that say what is to be shown

# (what is changed, the line or the part of a line as it is, changed)
CHANGED = [
    ("the function starts the first sum at 0", "i 14 21 .mov 64 (.reg .rax) (.imm 0x1)", "i 14 21 .mov 64 (.reg .rax) (.imm 0x0)"),
    ("the function takes 65520 from the first sum", "i 93 99 .sub 64 (.reg .rax) (.imm 0xFFF1)", "i 93 99 .sub 64 (.reg .rax) (.imm 0xFFF0)"),
    ("the function lets the first sum reach 65521", "i 76 83 .mov 64 (.reg .rcx) (.imm 0xFFF1)", "i 76 83 .mov 64 (.reg .rcx) (.imm 0xFFF2)"),
    ("the function leaves the second sum as it is where it is 65521 or more", "i 124 126 .jae 0x80", "i 124 126 .jae 0x8C"),
    ("the function adds the byte to the second sum", "i 105 108 .add 64 (.reg .rax) (.reg .r12)", "i 105 108 .add 64 (.reg .rax) (.reg .rcx)"),
    ("the function reads the byte one place on", "i 64 67 .movzx8 .rcx (.mem .rcx 0x0)", "i 64 67 .movzx8 .rcx (.mem .rcx 0x1)"),
    ("the function goes on past the last byte", "i 53 55 .jae 0x98", "i 53 55 .jb 0x98"),
    ("the function counts by two", "i 143 147 .add 64 (.reg .rax) (.imm 0x1)", "i 143 147 .add 64 (.reg .rax) (.imm 0x2)"),
    ("the function shifts the second sum by 15", "i 155 159 .shl64 .rax 16", "i 155 159 .shl64 .rax 15"),
    ("the function returns the second sum twice", "i 159 162 .add 64 (.reg .rax) (.reg .r12)", "i 159 162 .add 64 (.reg .rax) (.reg .r13)"),
    ("the function does not give r12 back", "i 166 168 .pop .r12", "i 166 168 .pop .rcx"),
    ("the contract allows less stack", "stack 40", "stack 32"),
    ("the specification's first sum is by another number", "(index (name bytes) (bin - (name place) (num 1)))) (num 65521))", "(index (name bytes) (bin - (name place) (num 1)))) (num 65519))"),
    ("the specification's first sum starts at 0", "def s1 bytes place = (ifx (bin == (name place) (num 0)) (num 1)", "def s1 bytes place = (ifx (bin == (name place) (num 0)) (num 0)"),
    ("the specification's second sum takes the first sum of one place before", "(call s1 (name bytes) (bin + (bin - (name place) (num 1)) (num 1)))", "(call s1 (name bytes) (bin - (name place) (num 1)))"),
    ("the specification multiplies by another number", "(bin * (num 65536)", "(bin * (num 65535)"),
    ("the place says the first sum is the second sequence's", "fact (bin == (name a) (call s1 (name input) (name i)))", "fact (bin == (name a) (call s2 (name input) (name i)))"),
    ("the place lets the first sum be anything", "fact (bin <= (name a) (num 65520))", "fact (bin <= (name a) (num 18446744073709551615))"),
    ("the place's number does not decrease", "decreases (bin - (name len) (name i))", "decreases (bin + (name len) (name i))"),
]


@unittest.skipUnless(LAKE, "Lean's lake is not installed")
class Adler(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        env = dict(os.environ, PATH=os.path.dirname(LAKE) + os.pathsep + os.environ["PATH"])
        r = subprocess.run([LAKE, "build", "odeverify"], cwd=HERE, capture_output=True, text=True, env=env)
        if r.returncode != 0: raise AssertionError("lake build failed:\n" + r.stdout[-2000:] + r.stderr[-2000:])
        cls.dir = tempfile.mkdtemp(prefix="odeadler-")
        cls.obj = os.path.join(ADLER, "odeadler32.o")
        cls.statement, cls.proof = os.path.join(cls.dir, "adler.statement"), os.path.join(cls.dir, "adler.proof")
        cls.kept = os.path.join(HERE, "proofs", "ode_adler32.proof")
        with open(os.path.join(ADLER, "adler32.spec")) as f: cls.spec = f.read()
        with open(os.path.join(HERE, "examples", "adler32", "adler32.places")) as f: cls.places = f.read()
        t = time.time()
        cls.runs, cls.items = prove.prove(cls.spec, [(cls.obj, "ode_adler32", cls.places)], cls.statement, cls.proof)["ode_adler32"]
        cls.found_in = time.time() - t
        cls.lines = []                                      # the statement's lines, then the proof's
        for path in (cls.statement, cls.proof):
            with open(path) as f: cls.lines += [l for l in f.read().split("\n") if l]

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.dir)

    def split(self, lines, name):
        paths = os.path.join(self.dir, name + ".statement"), os.path.join(self.dir, name + ".proof")
        for path, want in zip(paths, (True, False)):
            with open(path, "w") as f: f.write("".join(l + "\n" for l in lines if (l.split()[0] in STATEMENT) == want))
        return paths

    def says(self, lines, name="t"):
        statement_path, proof_path = self.split(lines, name)
        r = subprocess.run([prove.EXE, prove.TABLE, statement_path, proof_path], capture_output=True, text=True)
        self.assertEqual(r.returncode == 0, r.stdout == "shown\n", r.stdout[:200])
        return r.stdout

    def test_shown(self):
        t = time.time()
        self.assertEqual(self.says(self.lines), "shown\n")
        took = time.time() - t
        with open(self.proof) as f: whole = f.read()
        print(f"\node_adler32: shown in {1000 * took:.0f} ms; the proof: {whole.count(chr(10))} lines, {len(whole)} bytes "
              f"({whole.count(chr(10) + 'q' + chr(10))} proofs of arithmetic); the statement: {os.path.getsize(self.statement)} bytes; "
              f"found in {self.runs} runs of the verifier, {self.found_in:.1f} s", file=sys.stderr)

    def test_the_kept_proof_shows_from_the_files(self):
        self.assertEqual(lean_verify.verify(self.spec, [(self.obj, "ode_adler32")], self.kept), (True, "shown"))

    def test_changed_in_one_place(self):
        for what, old, new in CHANGED:
            with self.subTest(what=what):
                hits = [k for k, l in enumerate(self.lines) if old in l]
                self.assertEqual(len(hits), 1, (what, old))
                lines = list(self.lines); lines[hits[0]] = lines[hits[0]].replace(old, new)
                self.assertFalse(self.says(lines).startswith("shown"), what)
                # and no other proof is found for it
                rest = [l for l in lines if not (l[:2] in ("t ", "p ", "s ") or l == "q")]
                statement_path, _ = self.split(rest, "again")
                p = prove.Prover(statement_path, [l for l in rest if l.split()[0] not in STATEMENT], os.path.join(self.dir, "again.found"),
                                 budget=4 * self.runs)
                p.last = ""
                try: found = p.solve([])
                except (prove.Unkept, prove.GaveUp): found = None
                self.assertIsNone(found, f"{what}: the prover found a proof")

    def test_the_proof_changed(self):
        proof_at = [k for k, l in enumerate(self.lines) if l[:2] in ("t ", "p ", "s ") or l == "q"]
        kinds = {}
        for k in proof_at:
            l = self.lines[k]
            trials = [("left out", None)]
            if l.startswith("t held"): trials.append(("another value held", "t held 0" if l != "t held 0" else "t held 1"))
            if l.startswith("t carry"): trials.append(("another value carried", "t carry 1" if l != "t carry 1" else "t carry 0"))
            if l.startswith("t open"): trials.append(("another opened", "t open 0" if l != "t open 0" else "t open 1"))
            if l in ("t lt", "t eq", "t gt"): trials.append(("another order", "t gt" if l != "t gt" else "t lt"))
            if l.startswith("s "): w = l.split(); trials.append(("a step's multiplier", " ".join(w[:2] + [str(int(w[2]) + 1)] + w[3:])))
            for kind, new in trials:
                lines = list(self.lines)
                if new is None: del lines[k]
                else: lines[k] = new
                self.assertFalse(self.says(lines).startswith("shown"), (k, l, kind))
                kinds[kind] = kinds.get(kind, 0) + 1
        print(f"\nthe proof of ode_adler32 changed in one place: {kinds}", file=sys.stderr)
        self.assertGreater(kinds.get("left out", 0), 50)


if __name__ == "__main__":
    unittest.main()
