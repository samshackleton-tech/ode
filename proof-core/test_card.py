#!/usr/bin/env python3
"""Verify that `docs/QUICKSTART.md` stays compact and that the worked `.ode` examples it points to
compile, prove, and pass Lean `odeverify` as `shown`."""
import os, subprocess, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
CARD = os.path.join(ROOT, "docs", "QUICKSTART.md")
sys.path.insert(0, os.path.join(ROOT, "lang"))
sys.path.insert(0, HERE)
import built

QUICKSTART_EXAMPLES = [
    ("paper/examples/all_zero.ode", "x86_64"),
    ("paper/examples/all_zero.ode", "arm64"),
    ("proof-core/examples/hasher/hash_eq_ct.ode", "x86_64"),
    ("proof-core/examples/hasher/hash_eq_ct.ode", "arm64"),
    ("paper/examples/quad.ode", "x86_64"),
]


class ReferenceCardTests(unittest.TestCase):
    def test_card_exists_is_compact_and_has_examples(self):
        with open(CARD) as f:
            text = f.read()
        words = len(text.split())
        self.assertLessEqual(words, 3500, f"QUICKSTART.md has {words} words (target <= 3500)")
        self.assertIn("```ode", text)

    @unittest.skipUnless(built.LAKE is not None, "Lean toolchain not installed")
    def test_every_card_example_verifies_shown(self):
        built.built("odeverify")
        with tempfile.TemporaryDirectory() as d:
            for rel, target in QUICKSTART_EXAMPLES:
                with self.subTest(example=rel, target=target):
                    src = os.path.join(ROOT, rel)
                    out_o = os.path.join(d, f"{os.path.basename(rel)}_{target}.o")
                    out_p = os.path.join(d, f"{os.path.basename(rel)}_{target}.proof")
                    r = subprocess.run(
                        [sys.executable, os.path.join(ROOT, "lang", "ode_tool.py"), "pack", src,
                         "--target", target, "--out", out_o, "--proof", out_p],
                        capture_output=True, text=True,
                    )
                    self.assertEqual(r.returncode, 0, f"{rel} ({target}) failed:\n{r.stdout}\n{r.stderr}")
                    self.assertIn("shown", r.stdout)


if __name__ == "__main__":
    unittest.main()
