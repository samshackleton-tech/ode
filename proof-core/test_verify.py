#!/usr/bin/env python3
"""The verifier in Lean (Core.lean) on a shipped function, from the file's bytes as ../kcheck/kdecode.py reads
them: `ode_common` of ../kcheck/programs/common/odecommon.o against its public contract. What is to be shown
is written by statement.py; the prover (prove.py) finds a proof; the verifier says `shown` of the two by
itself. With the function, the specification, the contract, the place or the proof changed in one place it
does not, nor does the prover find another proof. A proof cannot add to what is to be shown, and a contract
with a line the account in Lean says nothing of is refused before the verifier sees it.

    python3 test_verify.py        (skipped where Lean's `lake` is not installed)"""
import os, shutil, subprocess, sys, tempfile, time, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import prove, statement
COMMON = os.path.join(HERE, "..", "kcheck", "programs", "common")
LAKE = shutil.which("lake") or (os.path.expanduser("~/.elan/bin/lake") if os.path.exists(os.path.expanduser("~/.elan/bin/lake")) else None)

STATEMENT = ("fn", "i", "arg", "returns", "stack", "def")    # the kinds of line that say what is to be shown

# (what is changed, the line as it is, the line changed)
CHANGED = [
    ("the function counts by two", "i 89 93 .add 64 (.reg .rax) (.imm 0x1)", "i 89 93 .add 64 (.reg .rax) (.imm 0x2)"),
    ("the function reads the first run twice", "i 72 75 .mov 64 (.reg .rcx) (.reg .rbp)", "i 72 75 .mov 64 (.reg .rcx) (.reg .rbx)"),
    ("the function reads one byte past the count", "i 61 63 .jae 0x6E", "i 61 63 .jb 0x6E"),
    ("the function goes on where the bytes differ", "i 84 86 .jne 0x62", "i 84 86 .je 0x62"),
    ("the function returns the count plus one", "i 122 125 .mov 64 (.reg .rax) (.reg .r13)", "i 122 125 .lea .rax .r13 1"),
    ("the function does not give rbx back", "i 132 133 .pop .rbx", "i 132 133 .pop .rcx"),
    ("the function gives two registers back exchanged", "i 125 127 .pop .r14", "i 125 127 .pop .r13"),
    ("the function reads below the stack pointer", "i 125 127 .pop .r14", "i 125 127 .mov 64 (.reg .r14) (.mem .rsp -8)"),
    ("the function writes above its frame", "i 0 1 .push .rbx", "i 0 1 .mov 64 (.mem .rsp 8) (.reg .rbx)"),
    ("the contract allows less stack", "stack 40", "stack 32"),
    ("the specification counts on past a difference", "(bin != (index (name a) (name at)) (index (name b) (name at)))", "(bin < (index (name a) (name at)) (index (name b) (name at)))"),
    ("the specification stops one early", "def common a b = (call alike (name a) (name b) (num 0))", "def common a b = (bin - (call alike (name a) (name b) (num 0)) (num 1))"),
    ("the contract returns another thing", "returns (call common (name a) (name b))", "returns (call alike (name a) (name b) (num 1))"),
    ("the second run may be shorter", "arg b bytes n", "arg b bytes a"),
    ("the place says less", "fact (bin <= (name i) (name n))", "fact (bin <= (name i) (bin + (name n) (num 1)))"),
    ("the place's number does not decrease", "decreases (bin - (name n) (name i))", "decreases (bin + (name n) (name i))"),
    ("the place's number may go below zero", "decreases (bin - (name n) (name i))", "decreases (bin - (bin - (name n) (name i)) (num 1))"),
    ("the place keeps a register the loop changes", "keep rcx", "keep rax rcx"),
]


class Verify(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.exe = None
        if LAKE:
            env = dict(os.environ, PATH=os.path.dirname(LAKE) + os.pathsep + os.environ["PATH"])
            r = subprocess.run([LAKE, "build", "odeverify"], cwd=HERE, capture_output=True, text=True, env=env)
            if r.returncode != 0: raise AssertionError("lake build failed:\n" + r.stdout[-2000:] + r.stderr[-2000:])
            cls.exe = prove.EXE
            cls.dir = tempfile.mkdtemp(prefix="odeverify-")
            cls.statement, cls.proof = os.path.join(cls.dir, "common.statement"), os.path.join(cls.dir, "common.proof")
            with open(os.path.join(COMMON, "common.spec")) as f: cls.spec = f.read()
            with open(os.path.join(COMMON, "common.proof")) as f: cls.places = f.read()
            t = time.time()
            cls.runs, cls.items = prove.prove(cls.spec, [(os.path.join(COMMON, "odecommon.o"), "ode_common", cls.places)], cls.statement, cls.proof)["ode_common"]
            cls.found_in = time.time() - t
            cls.lines = []                                  # the statement's lines, then the proof's
            for path in (cls.statement, cls.proof):
                with open(path) as f: cls.lines += [l for l in f.read().split("\n") if l]

    @classmethod
    def tearDownClass(cls):
        if cls.exe: shutil.rmtree(cls.dir)

    def setUp(self):
        if self.exe is None: self.skipTest("no Lean (lake) here")

    def split(self, lines, name):
        """The lines in two files, each line in the one its kind belongs in: (the statement's path, the proof's)."""
        paths = os.path.join(self.dir, name + ".statement"), os.path.join(self.dir, name + ".proof")
        for path, want in zip(paths, (True, False)):
            with open(path, "w") as f: f.write("".join(l + "\n" for l in lines if (l.split()[:1] or [""])[0] in STATEMENT) if want else
                                               "".join(l + "\n" for l in lines if (l.split()[:1] or [""])[0] not in STATEMENT))
        return paths

    def run_files(self, statement_path, proof_path):
        r = subprocess.run([self.exe, prove.TABLE, statement_path, proof_path], capture_output=True, text=True)
        self.assertEqual(r.returncode == 0, r.stdout.startswith("shown"), r.stdout[:200])
        return r.stdout

    def says(self, lines):
        return self.run_files(*self.split(lines, "t"))

    def test_shown(self):
        t = time.time()
        said = self.says(self.lines)
        took = time.time() - t
        self.assertEqual(said, "shown\n")
        proof = [l for l in self.lines if l[:2] in ("t ", "p ", "s ") or l == "q"]
        self.assertEqual(len(proof), self.items)
        with open(self.proof) as f: whole = f.read()
        print(f"\node_common: shown in {1000 * took:.0f} ms; the proof: {whole.count(chr(10))} lines, {len(whole)} bytes "
              f"(the place: {whole.count(chr(10)) - len(proof) - 1} lines; {sum(l == 'q' for l in proof)} proofs of arithmetic); "
              f"the statement: {os.path.getsize(self.statement)} bytes; found in {self.runs} runs of the verifier, {self.found_in:.1f} s", file=sys.stderr)

    def test_changed_in_one_place(self):
        for what, old, new in CHANGED:
            with self.subTest(what=what):
                hits = [k for k, l in enumerate(self.lines) if l == old or (old.startswith("(") and old in l) or (old == "keep rcx" and l.startswith(old))]
                self.assertEqual(len(hits), 1, (what, old))
                lines = list(self.lines); lines[hits[0]] = lines[hits[0]].replace(old, new)
                said = self.says(lines)
                self.assertFalse(said.startswith("shown"), what)
                # and no other proof is found for it
                rest = [l for l in lines if not (l[:2] in ("t ", "p ", "s ") or l == "q")]
                statement_path, _ = self.split(rest, "again")
                p = prove.Prover(statement_path, [l for l in rest if l.split()[0] not in STATEMENT], os.path.join(self.dir, "again.found")); p.last = ""
                try: found = p.solve([])
                except prove.Unkept: found = None
                self.assertIsNone(found, f"{what}: the prover found a proof")

    def test_the_proof_changed(self):
        proof_at = [k for k, l in enumerate(self.lines) if l[:2] in ("t ", "p ", "s ") or l == "q"]
        kinds = {}
        for k in proof_at:
            l = self.lines[k]
            trials = [("left out", None)]
            if l.startswith("t live"): trials.append(("live made dead", "t dead"))
            if l.startswith("t dead"): trials.append(("dead made live", "t live"))
            if l.startswith("t open"): trials.append(("another opened", "t open 0" if l != "t open 0" else "t open 1"))
            if l in ("t lt", "t eq", "t gt"): trials.append(("another order", "t gt" if l != "t gt" else "t lt"))
            if l.startswith("p "): w = l.split(); trials.append(("another row to start from", " ".join(w[:1] + [str(int(w[1]) + 1)] + w[2:])))
            if l.startswith("s "): w = l.split(); trials.append(("a step's multiplier", " ".join(w[:2] + [str(int(w[2]) + 1)] + w[3:])))
            for kind, new in trials:
                lines = list(self.lines)
                if new is None: del lines[k]
                else: lines[k] = new
                said = self.says(lines)
                if said.startswith("shown"):
                    # a proof of arithmetic that starts from another row the verifier holds may be a proof too
                    self.assertEqual(kind, "another row to start from", (k, l, kind))
                    kinds[kind + ": still shown"] = kinds.get(kind + ": still shown", 0) + 1
                else: kinds[kind] = kinds.get(kind, 0) + 1
        print(f"\nthe proof changed in one place: {kinds}", file=sys.stderr)
        self.assertGreater(kinds.get("left out", 0), 20)

    def test_what_is_not_read_is_not_shown(self):
        self.assertFalse(self.says([l for l in self.lines if not l.startswith("i 133 ")]).startswith("shown"))       # the return left out
        self.assertFalse(self.says(self.lines + ["t live"]).startswith("shown"))                                    # a proof that says more
        self.assertFalse(self.says([l.replace(".ret", ".hlt") for l in self.lines]).startswith("shown"))            # no row of the table
        self.assertFalse(self.says([]).startswith("shown"))

    def test_a_proof_cannot_add_to_what_is_to_be_shown(self):
        with open(self.proof) as f: proof = f.read()
        for extra in ("stack 4000", "returns (num 0)", "def common a b = (num 0)", "arg x number", "i 0 1 .ret", "fn other"):
            for text in (proof + extra + "\n", extra + "\n" + proof):
                path = os.path.join(self.dir, "more.proof")
                with open(path, "w") as f: f.write(text)
                said = self.run_files(self.statement, path)
                self.assertTrue(said.startswith("refused: a line of the statement in the proof"), said[:200])
        # a proof speaks only of the statement's functions, and says of which
        self.assertEqual(proof.count("for ode_common\n"), 1)
        for text, why in ((proof.replace("for ode_common\n", "for ode_other\n"), "refused: the proof speaks of ode_other, which is no function of the statement"),
                          (proof.replace("for ode_common\n", ""), "refused: a line of a proof before any `for NAME`")):
            path = os.path.join(self.dir, "more.proof")
            with open(path, "w") as f: f.write(text)
            said = self.run_files(self.statement, path)
            self.assertTrue(said.startswith(why), said[:200])
        # and a proof's line in the statement is refused too
        with open(self.statement) as f: text = f.read()
        path = os.path.join(self.dir, "more.statement")
        with open(path, "w") as f: f.write(text + "t live\n")
        self.assertTrue(self.run_files(path, self.proof).startswith("refused: a line of a proof in the statement"))

    def test_the_kept_proof_shows_from_the_files(self):
        import lean_verify
        obj, kept = os.path.join(COMMON, "odecommon.o"), os.path.join(HERE, "proofs", "ode_common.proof")
        self.assertEqual(lean_verify.verify(self.spec, [(obj, "ode_common")], kept), (True, "shown"))
        self.assertEqual(self.spec.count("stack 40"), 1)
        shown, said = lean_verify.verify(self.spec.replace("stack 40", "stack 32"), [(obj, "ode_common")], kept)
        self.assertFalse(shown); self.assertTrue(said.startswith("refused"), said[:200]); self.assertTrue(said.endswith("\nin ode_common"), said[-200:])
        self.assertEqual(self.spec.count("a[at] != b[at]"), 1)
        shown, said = lean_verify.verify(self.spec.replace("a[at] != b[at]", "a[at] < b[at]"), [(obj, "ode_common")], kept)
        self.assertFalse(shown)

    def test_a_contract_line_the_account_lacks_is_refused(self):
        obj = os.path.join(COMMON, "odecommon.o")
        self.assertIn("    trace depends on a, b\n", self.spec)
        statement.statement(self.spec, [(obj, "ode_common")])                          # as it is: written
        for what, old, new in (("the trace may not depend on the bytes", "    trace depends on a, b\n", ""),
                               ("the trace may depend on one run only", "trace depends on a, b", "trace depends on a"),
                               ("the function needs an instruction set", "    stack 40\n", "    stack 40\n    needs sse41\n"),
                               ("the function asks something of its caller", "    returns common(a, b)\n", "    requires n < 4096\n    returns common(a, b)\n"),
                               ("the specification has a layout", "def common(a, b)", "layout pair 16 { x: number at 0, y: number at 8 }\n\ndef common(a, b)"),
                               ("the specification has a constant", "def common(a, b)", "const NO = 7\n\ndef common(a, b)")):
            with self.subTest(what=what):
                self.assertEqual(self.spec.count(old), 1)
                with self.assertRaises(SystemExit) as e: statement.statement(self.spec.replace(old, new), [(obj, "ode_common")])
                self.assertIn("does not", str(e.exception))


if __name__ == "__main__":
    unittest.main()
