"""The adversarial game as a regression corpus (SPEC s9).

Every attack directory under game/attacks/ is replayed by the referee:
Bob, holding only Sam's bootstrap, must never ACCEPT and then print a
wrong G. Each attack Mallory ever lost stays here forever; an attack he
wins becomes a fix and then a line in this corpus.

Run: pypy3 -m unittest discover -s tests
"""
import glob
import os
import subprocess
import sys
import unittest

ROOT = os.path.join(os.path.dirname(__file__), "..")
GAME = os.path.join(ROOT, "game")


class GameTest(unittest.TestCase):
    def test_bootstrap_matches_the_toolchain(self):
        # The bootstrap is a copy of the checker; a copy that drifts from
        # the toolchain would silently test something else.
        for name in ("blake3.py", "canon.py", "store.py", "wcheck.py",
                     "word.py"):
            with open(os.path.join(ROOT, "ode", name), "rb") as f:
                a = f.read()
            with open(os.path.join(GAME, "bootstrap", "ode-base", "ode", name), "rb") as f:
                b = f.read()
            self.assertEqual(a, b, f"bootstrap/ode/{name} differs from ode/")

    def test_mallory_loses_every_recorded_attack(self):
        attacks = sorted(glob.glob(os.path.join(GAME, "attacks", "*")))
        self.assertGreaterEqual(len(attacks), 10)
        p = subprocess.run(["pypy3", os.path.join(GAME, "referee.py")]
                           + attacks, capture_output=True, text=True,
                           timeout=600)
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertNotIn("MALLORY WINS", p.stdout)
        self.assertIn("0 win(s) for Mallory", p.stdout)


if __name__ == "__main__":
    unittest.main()
