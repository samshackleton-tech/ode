"""The adversarial game as a regression corpus (SPEC s9).

The referee replays every recorded attack: Bob, holding only the root
and the pins, must never ACCEPT and print a wrong answer, and must
accept every control. The distributed copies must match the toolchain:
ode-base by its pinned tree hash (game/pin_ode_base.py refreshes both),
and the root's BLAKE3 byte for byte.
"""
import glob
import os
import re
import subprocess
import sys
import unittest

ROOT = os.path.join(os.path.dirname(__file__), "..")
GAME = os.path.join(ROOT, "game")
sys.path.insert(0, os.path.join(GAME, "bootstrap", "root"))
from launch import read_tree, tree_hash  # noqa: E402


def _bytes(path):
    with open(path, "rb") as f:
        return f.read()


class GameTest(unittest.TestCase):
    def test_ode_base_is_the_toolchain_and_is_pinned(self):
        for name in os.listdir(os.path.join(GAME, "ode-base", "ode")):
            if name.endswith(".py"):
                self.assertEqual(_bytes(os.path.join(ROOT, "ode", name)),
                                 _bytes(os.path.join(GAME, "ode-base", "ode", name)),
                                 f"{name}: run pypy3 game/pin_ode_base.py")
        pins = re.findall(rb"\(ode-base #([0-9a-f]{64})\)", _bytes(
            os.path.join(GAME, "bootstrap", "game-targets", "RELIANCE")))
        self.assertEqual(pins, [tree_hash(read_tree(os.path.join(GAME, "ode-base")))
                                .hex().encode()], "run pypy3 game/pin_ode_base.py")

    def test_root_holds_hash_domains_and_launcher(self):
        root = os.path.join(GAME, "bootstrap", "root")
        self.assertEqual(sorted(f for f in os.listdir(root) if f != "__pycache__"),
                         ["blake3.py", "domains.py", "launch.py"])
        self.assertEqual(_bytes(os.path.join(root, "blake3.py")),
                         _bytes(os.path.join(ROOT, "ode", "blake3.py")))
        self.assertEqual(_bytes(os.path.join(root, "domains.py")),
                         _bytes(os.path.join(ROOT, "ode", "domains.py")))

    def test_mallory_loses_and_controls_pass(self):
        # The corpus is generated, not committed: regenerate, then replay.
        subprocess.run(["pypy3", os.path.join(GAME, "make_attacks.py")],
                       check=True, capture_output=True, timeout=600)
        attacks = sorted(glob.glob(os.path.join(GAME, "attacks", "*")))
        self.assertGreaterEqual(len(attacks), 20)
        p = subprocess.run(["pypy3", os.path.join(GAME, "referee.py")] + attacks,
                           capture_output=True, text=True, timeout=600)
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertIn("0 failure(s)", p.stdout)


if __name__ == "__main__":
    unittest.main()
