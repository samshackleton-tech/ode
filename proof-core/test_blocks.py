#!/usr/bin/env python3
"""A function with two loops, one inside the other, in the verifier in Lean (Core.lean): `ode_adler32_blocks`
of ../kcheck/programs/adler32/odeadler32.o, the Adler-32 checksum taken in blocks of at most 5552 bytes, the
two sums reduced once a block (by shifts and masks: 65536 is 15 more than 65521). It is shown against the
same public contract as the plain `ode_adler32`. The proof has two places: at the head of the loop over the
blocks the sums are the specification's; at the head of the loop over a block's bytes they are the same as
the specification's by 65521, and bounded by how far the block has still to go.

What is new here, each with its part in the theorem (SoundTop.lean, `explore_sound`): more than one place a
function; a place's general state keeps what the path knew when it first came there; a shift to the right
by a number and an and with one less than a power of two, as the quotient and the remainder of one division.

With the function, the specification, the contract or a place changed in one place it is not shown, nor
does the prover find a proof within the runs of the verifier, and one and a half times the time, in which it
finds the right one.

    python3 test_blocks.py        (skipped where Lean's `lake` is not installed)"""
import os, shutil, subprocess, sys, tempfile, time, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lean_verify, prove, statement
ADLER = os.path.join(HERE, "..", "kcheck", "programs", "adler32")
LAKE = lean_verify.LAKE
STATEMENT = ("fn", "i", "arg", "returns", "stack", "def")    # the kinds of line that say what is to be shown
SYMBOL = "ode_adler32_blocks"

# (what is changed, the line or the part of a line as it is, changed)
CHANGED = [
    ("the function takes what is above 15 bits of the first sum", "i 173 177 .shr64 .rcx 16", "i 173 177 .shr64 .rcx 15"),
    ("the function keeps 17 bits of the first sum", "i 164 170 .and 64 (.reg .rax) (.imm 0xFFFF)", "i 164 170 .and 64 (.reg .rax) (.imm 0x1FFFF)"),
    ("the function counts what is above 16 bits 8 times", "i 177 181 .shl64 .rcx 4", "i 177 181 .shl64 .rcx 3"),
    ("the function leaves the first sum as it is where it is 65521 or more", "i 246 248 .jae 0xFA", "i 246 248 .jae 0x106"),
    ("the function reads the byte one place on", "i 131 134 .movzx8 .rcx (.mem .rcx 0x0)", "i 131 134 .movzx8 .rcx (.mem .rcx 0x1)"),
    ("the function goes on in a block past its end", "i 120 122 .jae 0xA1", "i 120 122 .jb 0xA1"),
    ("the function shifts the second sum by 15", "i 371 375 .shl64 .rax 16", "i 371 375 .shl64 .rax 15"),
    ("the function does not give r15 back", "i 382 384 .pop .r15", "i 382 384 .pop .rcx"),
    ("the contract allows less stack", "stack 56", "stack 48"),
    ("the specification's first sum is by another number", "(index (name bytes) (bin - (name place) (num 1)))) (num 65521))", "(index (name bytes) (bin - (name place) (num 1)))) (num 65519))"),
    ("the first place says the first sum is the second sequence's", "fact (bin == (name a) (call s1 (name input) (name i)))", "fact (bin == (name a) (call s2 (name input) (name i)))"),
    ("the second place says nothing of how large the first sum is", "(num 1481280))", "(num 18446744073709551615))"),
    ("the second place's number does not decrease", "decreases (bin - (name end) (name i))", "decreases (bin + (name end) (name i))"),
    ("the second place does not keep the block's end", " r11 r15", " r11"),
]


@unittest.skipUnless(LAKE, "Lean's lake is not installed")
class Blocks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        env = dict(os.environ, PATH=os.path.dirname(LAKE) + os.pathsep + os.environ["PATH"])
        r = subprocess.run([LAKE, "build", "odeverify"], cwd=HERE, capture_output=True, text=True, env=env)
        if r.returncode != 0: raise AssertionError("lake build failed:\n" + r.stdout[-2000:] + r.stderr[-2000:])
        cls.dir = tempfile.mkdtemp(prefix="odeblocks-")
        cls.obj = os.path.join(ADLER, "odeadler32.o")
        cls.statement, cls.proof = os.path.join(cls.dir, "blocks.statement"), os.path.join(cls.dir, "blocks.proof")
        cls.kept = os.path.join(HERE, "proofs", "ode_adler32_blocks.proof")
        with open(os.path.join(ADLER, "adler32.spec")) as f: cls.spec = f.read()
        with open(os.path.join(HERE, "examples", "adler32", "blocks.places")) as f: cls.places = f.read()
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
        self.assertEqual(sum(l.startswith("place ") for l in self.lines), 2)
        print(f"\n{SYMBOL}: shown in {1000 * took:.0f} ms; two places; the proof: {whole.count(chr(10))} lines, {len(whole)} bytes "
              f"({whole.count(chr(10) + 'q' + chr(10))} proofs of arithmetic); the statement: {os.path.getsize(self.statement)} bytes; "
              f"found in {self.runs} runs of the verifier, {self.found_in:.1f} s", file=sys.stderr)

    def test_the_kept_proof_shows_from_the_files(self):
        self.assertEqual(lean_verify.verify(self.spec, [(self.obj, SYMBOL)], self.kept), (True, "shown"))

    def test_changed_in_one_place(self):
        for what, old, new in CHANGED:
            with self.subTest(what=what):
                hits = [k for k, l in enumerate(self.lines) if old in l]
                self.assertEqual(len(hits), 1, (what, old))
                lines = list(self.lines); lines[hits[0]] = lines[hits[0]].replace(old, new)
                self.assertFalse(self.says(lines).startswith("shown"), what)
                # and no other proof is found for it
                rest = [l for l in lines if not (l[:2] in ("t ", "r ", "s ") or l == "q")]
                statement_path, _ = self.split(rest, "again")
                p = prove.Prover(statement_path, [l for l in rest if l.split()[0] not in STATEMENT], os.path.join(self.dir, "again.found"),
                                 budget=self.runs, until=time.time() + 1.5 * self.found_in)
                p.last = ""
                try: found = p.solve([])
                except (prove.Unkept, prove.GaveUp): found = None
                self.assertIsNone(found, f"{what}: the prover found a proof")

    def test_the_proof_changed(self):
        proof_at = [k for k, l in enumerate(self.lines) if l[:2] in ("t ", "r ", "s ") or l == "q"]
        kinds = {}
        for k in proof_at[::7]:                              # (every seventh line of the proof: it has some two thousand)
            l = self.lines[k]
            trials = [("left out", None)]
            if l.startswith("t held"): trials.append(("another value held", "t held 0" if l != "t held 0" else "t held 1"))
            if l.startswith("t carry"): trials.append(("another value carried", "t carry 1" if l != "t carry 1" else "t carry 0"))
            if l.startswith("t open"): trials.append(("another opened", "t open 0" if l != "t open 0" else "t open 1"))
            if l in ("t lt", "t eq", "t gt"): trials.append(("another order", "t gt" if l != "t gt" else "t lt"))
            if l.startswith("s "): w = l.split(); trials.append(("a step's multiplier", " ".join(w[:2] + [str(int(w[2]) + 1)] + w[3:])))
            for kind, new in trials:
                if kind == "left out" and l.startswith("r "): continue       # (a start row a proof does not use may go: test_verify.py counts those)
                lines = list(self.lines)
                if new is None: del lines[k]
                else: lines[k] = new
                self.assertFalse(self.says(lines).startswith("shown"), (k, l, kind))
                kinds[kind] = kinds.get(kind, 0) + 1
        print(f"\nthe proof of {SYMBOL} changed in one place: {kinds}", file=sys.stderr)
        self.assertGreater(kinds.get("left out", 0), 50)


if __name__ == "__main__":
    unittest.main()
