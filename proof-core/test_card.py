#!/usr/bin/env python3
"""Verify that every worked example in docs/ODE-CARD.md compiles, proves, and passes Lean `odeverify`
as `shown`, and that the reference card stays compact (under 2,500 words)."""
import os, re, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
CARD = os.path.join(ROOT, "docs", "ODE-CARD.md")
sys.path.insert(0, os.path.join(ROOT, "lang"))
sys.path.insert(0, HERE)
import built, ode_tool


def extract_examples(text):
    """Extract all `<!-- card-example: NAME TARGET -->` followed by ```spec ... ``` and ```ode ... ```."""
    pat = re.compile(
        r"<!--\s*card-example:\s*(\w+)\s+(\w+)\s*-->\s*"
        r"```spec\n(.*?)\n```\s*"
        r"```ode\n(.*?)\n```",
        re.S,
    )
    return pat.findall(text)


class ReferenceCardTests(unittest.TestCase):
    def test_card_exists_is_compact_and_has_examples(self):
        with open(CARD) as f:
            text = f.read()
        words = len(text.split())
        self.assertLessEqual(words, 2500, f"ODE-CARD.md has {words} words (target <= 2500)")
        exs = extract_examples(text)
        self.assertEqual(len(exs), 5, f"expected 5 card examples, found {len(exs)}")

    @unittest.skipUnless(built.LAKE is not None, "Lean toolchain not installed")
    def test_every_card_example_verifies_shown(self):
        built.built("odeverify")
        with open(CARD) as f:
            exs = extract_examples(f.read())
        self.assertGreaterEqual(len(exs), 4)
        with tempfile.TemporaryDirectory() as d:
            for name, target, spec_src, ode_src in exs:
                with self.subTest(example=name, target=target):
                    sp = os.path.join(d, f"{name}.spec")
                    op = os.path.join(d, f"{name}.ode")
                    with open(sp, "w") as f:
                        f.write(spec_src + "\n")
                    with open(op, "w") as f:
                        f.write(ode_src + "\n")
                    res = ode_tool.run_check(op, sp, do_trace=True)
                    self.assertEqual(res["verdict"], "shown", f"{name}: {res.get('diagnostic')}")
                    self.assertEqual(res["target"], target)


if __name__ == "__main__":
    unittest.main()
