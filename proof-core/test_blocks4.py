#!/usr/bin/env python3
"""The Adler-32 checksum that takes four bytes a turn, in the verifier in Lean (Core.lean):
`ode_adler32_blocks4` of ../kcheck/programs/adler32/odeadler32.o, against the same public contract as the
plain `ode_adler32`. It is the function of the three that is fast (87% of the usual C: ../kcheck/README.md).
Three places: the head of the loop over the blocks, of the loop that takes four bytes, and of the loop that
takes the bytes left over.

What is new here, with its part in the theorem (SoundSpec.lean, `sevalWith_sound`, `opener_sound`): a use of
a definition that is met while another is opened, and whose value nothing holds, is opened in turn where the
proof says so. The sum four places on is by the sum three places on, and so on down to the one the place
holds.

With the function or the specification changed in one place it is not shown, nor does the prover find a
proof within the runs of the verifier, and three quarters of the time, in which it finds the right one.

    python3 test_blocks4.py        (skipped where Lean's `lake` is not installed)"""
import os, shutil, subprocess, sys, tempfile, time, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, "..", "lang"))
import lean_verify, odec, prove, statement
import built
ADLER = os.path.join(HERE, "..", "kcheck", "programs", "adler32")
LAKE = lean_verify.LAKE
STATEMENT = ("fn", "i", "arg", "returns", "stack", "def")    # the kinds of line that say what is to be shown
SYMBOL = "ode_adler32_blocks4"

# (what is changed, the line or the part of a line as it is, changed)
CHANGED = [
    ("the function takes four bytes where three are left", "i 111 118 .mov 64 (.reg .rax) (.imm 0x3)", "i 111 118 .mov 64 (.reg .rax) (.imm 0x2)"),
    ("the function takes the third byte for the second", "i 169 173 .add 64 (.reg .rcx) (.imm 0x1)", "i 169 173 .add 64 (.reg .rcx) (.imm 0x2)"),
    ("the function goes on three bytes after taking four", "i 256 260 .add 64 (.reg .rax) (.imm 0x4)", "i 256 260 .add 64 (.reg .rax) (.imm 0x3)"),
    ("the specification's second sum takes the first sum of one place before", "(call s1 (name bytes) (bin + (bin - (name place) (num 1)) (num 1)))", "(call s1 (name bytes) (bin - (name place) (num 1)))"),
]


@unittest.skipUnless(LAKE, "Lean's lake is not installed")
class Blocks4(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        env = dict(os.environ, PATH=os.path.dirname(LAKE) + os.pathsep + os.environ["PATH"])
        built.built("odeverify")
        cls.dir = tempfile.mkdtemp(prefix="odeblocks4-")
        cls.obj = os.path.join(ADLER, "odeadler32.o")
        cls.statement, cls.proof = os.path.join(cls.dir, "blocks.statement"), os.path.join(cls.dir, "blocks.proof")
        cls.kept = os.path.join(HERE, "proofs", "ode_adler32_blocks4.proof")
        with open(os.path.join(ADLER, "adler32.spec")) as f: cls.spec = f.read()
        cls.places = odec.places(os.path.join(ADLER, "blocks4.ode"), "adler32_blocks4")           # the loops' places, written at the loops in the source
        t = time.time()
        cls.runs, cls.items = prove.prove(cls.spec, [(cls.obj, SYMBOL, cls.places)], cls.statement, cls.proof)[SYMBOL]
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
        self.assertEqual(sum(l.startswith("place ") for l in self.lines), 3)
        self.assertGreater(sum(l == "t open" for l in self.lines), 5)      # uses of definitions opened where they are met
        print(f"\n{SYMBOL}: shown in {1000 * took:.0f} ms; three places; the proof: {whole.count(chr(10))} lines, {len(whole)} bytes "
              f"({whole.count(chr(10) + 'q' + chr(10))} proofs of arithmetic); the statement: {os.path.getsize(self.statement)} bytes; "
              f"found in {self.runs} runs of the verifier, {self.found_in:.1f} s", file=sys.stderr)

    def test_the_kept_proof_shows_from_the_files(self):
        self.assertEqual(lean_verify.verify(self.spec, [(self.obj, SYMBOL)], self.kept), (True, "shown"))
        with open(self.kept) as f, open(self.proof) as g: self.assertEqual(f.read(), g.read())

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
                                 budget=self.runs, until=time.time() + 0.75 * self.found_in)
                p.last = ""
                try: found = p.solve([])
                except (prove.Unkept, prove.GaveUp): found = None
                self.assertIsNone(found, f"{what}: the prover found a proof")

    def test_the_proof_changed(self):
        proof_at = [k for k, l in enumerate(self.lines) if l[:2] in ("t ", "p ", "s ") or l == "q"]
        kinds = {}
        for k in proof_at[::11]:                             # (every eleventh line of the proof: it has some two thousand)
            l = self.lines[k]
            trials = [("left out", None)]
            if l.startswith("t held"): trials.append(("another value held", "t held 0" if l != "t held 0" else "t held 1"))
            if l.startswith("t carry"): trials.append(("another value carried", "t carry 1" if l != "t carry 1" else "t carry 0"))
            if l.startswith("t open "): trials.append(("another opened", "t open 0" if l != "t open 0" else "t open 1"))     # (a plain `t open` is where a number is needed: it names no use)
            if l in ("t lt", "t eq", "t gt"): trials.append(("another order", "t gt" if l != "t gt" else "t lt"))
            if l.startswith("s "): w = l.split(); trials.append(("a step's multiplier", " ".join(w[:2] + [str(int(w[2]) + 1)] + w[3:])))
            for kind, new in trials:
                lines = list(self.lines)
                if new is None: del lines[k]
                else: lines[k] = new
                self.assertFalse(self.says(lines).startswith("shown"), (k, l, kind))
                kinds[kind] = kinds.get(kind, 0) + 1
        print(f"\nthe proof of {SYMBOL} changed in one place: {kinds}", file=sys.stderr)
        self.assertGreater(kinds.get("left out", 0), 50)


if __name__ == "__main__":
    unittest.main()
