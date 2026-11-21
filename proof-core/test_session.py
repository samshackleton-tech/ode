#!/usr/bin/env python3
"""The prover's helper says what the verifier says.

    python3 test_session.py        (skipped where Lean's `lake` is not installed)

`odeprove` (ProveMain.lean, through session.py) stands in for `odeverify` while a proof is being found: it
keeps its place in the proof, where `odeverify` goes through the proof from its first line. For kept proofs
of three functions, the proof is cut after each of its lines in turn (for the longest, each seventh), and
at every cut the two must say the same, word for word: going forward a line at a time, going back from the
far end, and with the session made to begin again every few batches (as it does when many processes wait).
(One thing only the helper says: `need know`, with the rows it would try, where the proof file has run out
at a point where rows may stand. None of these three proofs has a row; test_split.py has that case.)

Two controls. A session that does not go back when the proof gets shorter must be told apart. And a
helper that says `shown` of everything does not get a proof past prove.py: what the prover hands out has
been through `odeverify`."""
import os, subprocess, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import built, lean_verify, prove, session
K = os.path.join(HERE, "..", "kcheck", "programs")
LAKE = lean_verify.LAKE
# (the function, its object, its specification, each how-manieth cut is tried)
KEPT = [("ode_varint", "varint/odevarint.o", "varint/varint.spec", 1),
        ("ode_adler32", "adler32/odeadler32.o", "adler32/adler32.spec", 1),
        ("ode_adler32_blocks4", "adler32/odeadler32.o", "adler32/adler32.spec", 7)]
HEAD = ("for", "place", "name", "keep", "fact", "decreases")


@unittest.skipUnless(LAKE, "Lean's lake is not installed")
class Helper(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.dir = tempfile.mkdtemp()
        cls.cases = []
        for name, obj, spec, step in KEPT:
            st = os.path.join(cls.dir, name + ".statement")
            subprocess.run([sys.executable, os.path.join(HERE, "statement.py"), os.path.join(K, spec), st, f"{os.path.join(K, obj)}:{name}"],
                           check=True, capture_output=True)
            with open(os.path.join(HERE, "proofs", name + ".proof")) as f: lines = f.read().split("\n")[:-1]
            k = max(i for i, l in enumerate(lines) if l.split()[0] in HEAD) + 1
            head, body = lines[:k], lines[k:]
            cuts = [i for i in range(len(body) + 1) if session.whole(body[:i])][::step]
            if cuts[-1] != len(body): cuts.append(len(body))
            cls.cases.append((name, st, head, body, cuts, [cls.verifier(st, head + body[:n]) for n in cuts]))

    @classmethod
    def verifier(cls, statement_path, lines):
        path = os.path.join(cls.dir, "cut.proof")
        with open(path, "w") as f: f.write("".join(l + "\n" for l in lines))
        return subprocess.run([prove.EXE, prove.TABLE, statement_path, path], capture_output=True, text=True).stdout

    def test_at_every_cut_the_helper_says_what_the_verifier_says(self):
        for name, st, head, body, cuts, want in self.cases:
            with self.subTest(function=name):
                self.assertTrue(want[-1].startswith("shown"))
                self.assertGreater(len({w for w in want}), 20)         # (the verifier says many different things on the way)
                s = session.Session(st, head, name)
                try:
                    self.assertEqual([s.ask(body[:n]) for n in cuts], want)
                    self.assertEqual(s.sent, len(body))                # each line was sent once
                    self.assertEqual([s.ask(body[:n]) for n in reversed(cuts[::3])], list(reversed(want[::3])))
                    self.assertEqual(s.begun, 1 + (len(cuts) - 1) // (session.DEPTH + 1))
                finally: s.close()

    def test_the_same_when_the_session_begins_again_every_few_batches(self):
        name, st, head, body, cuts, want = self.cases[0]
        depth, session.DEPTH = session.DEPTH, 5
        try:
            s = session.Session(st, head, name)
            got = [s.ask(body[:n]) for n in cuts] + [s.ask(body[:n]) for n in reversed(cuts[::3])]
            self.assertGreater(s.begun, 10)
            s.close()
        finally: session.DEPTH = depth
        self.assertEqual(got, want + list(reversed(want[::3])))

    def test_a_session_that_does_not_go_back_is_told_apart(self):
        name, st, head, body, cuts, want = self.cases[0]

        class Forward(session.Session):                                # takes a shorter proof for the one it was at
            def ask(self, lines):
                at = len(self.base) + sum(len(b) for b in self.batches)
                return self.said[-1] if len(lines) < at else super().ask(lines)
        s = Forward(st, head, name)
        try:
            for n in cuts: s.ask(body[:n])
            self.assertNotEqual([s.ask(body[:n]) for n in reversed(cuts[::3])], list(reversed(want[::3])))
        finally: s.close()

    def test_what_the_prover_hands_out_has_been_through_the_verifier(self):
        real = session.Session.ask
        session.Session.ask = lambda self, lines: "shown\n"
        try:
            with open(os.path.join(K, "varint", "varint.spec")) as f: spec = f.read()
            with self.assertRaises(SystemExit) as e:
                prove.prove(spec, [(os.path.join(K, "varint", "odevarint.o"), "ode_varint", "")],
                            os.path.join(self.dir, "lie.statement"), os.path.join(self.dir, "lie.proof"))
            self.assertIn("the verifier does not take the proof", str(e.exception))
        finally: session.Session.ask = real


if __name__ == "__main__":
    unittest.main()
