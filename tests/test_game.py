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
        for name in ("canon.py", "store.py", "wcheck.py",
                     "word.py"):
            with open(os.path.join(ROOT, "ode", name), "rb") as f:
                a = f.read()
            with open(os.path.join(GAME, "ode-base", "ode", name), "rb") as f:
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
        self.assertIn("0 failure(s)", p.stdout)
        self.assertNotIn("CONTROL FAILED", p.stdout)


if __name__ == "__main__":
    unittest.main()


class PinTest(unittest.TestCase):
    def test_package_pins_the_public_ode_base(self):
        sys.path.insert(0, os.path.join(GAME, "bootstrap", "root"))
        from launch import read_tree, tree_hash
        import re
        with open(os.path.join(GAME, "bootstrap", "blake3", "RELIANCE"), "rb") as f:
            pins = re.findall(rb"\(ode-base #([0-9a-f]{64})\)", f.read())
        self.assertEqual(len(pins), 1)
        self.assertEqual(pins[0].decode(),
                         tree_hash(read_tree(os.path.join(GAME, "ode-base"))).hex(),
                         "run pypy3 game/pin_ode_base.py")

    def test_root_holds_only_the_hash_and_the_launcher(self):
        root = os.path.join(GAME, "bootstrap", "root")
        self.assertEqual(sorted(f for f in os.listdir(root) if f != "__pycache__"),
                         ["blake3.py", "launch.py"])
        with open(os.path.join(root, "blake3.py"), "rb") as f:
            a = f.read()
        with open(os.path.join(ROOT, "ode", "blake3.py"), "rb") as f:
            self.assertEqual(a, f.read())
