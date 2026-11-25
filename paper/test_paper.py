#!/usr/bin/env pypy3
"""Tests of the language report: what it prints is what the repository says.

    pypy3 paper/test_paper.py

- facts.json is what make_facts.py gives now (the report reads its numbers from that file);
- the places that the report's listings are cut from exist in the files they are read from;
- every command the report names is a command of the tool;
- where the verifier is built: the report's example is packed and audited for both processors, the
  answer is `shown`, the contract's identifier is the one in facts.json, and the counts of instructions
  and bytes are those of measured.json.
"""
import json
import os
import re
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path[:0] = [HERE]

import make_facts

HAVE_VERIFIER = os.path.isfile(os.path.join(ROOT, "proof-core", ".lake", "build", "bin", "odeverify"))


def read(*parts):
    with open(os.path.join(ROOT, *parts), "r", encoding="utf-8") as f:
        return f.read()


class PaperTests(unittest.TestCase):
    def test_facts_are_current(self):
        self.assertEqual(json.loads(read("paper", "facts.json")), make_facts.facts(),
                         "paper/facts.json is stale: run pypy3 paper/render-paper.py")

    def test_figure_2_shows_the_identifier_of_facts(self):
        cid = json.loads(read("paper", "facts.json"))["all_zero"]["id"]
        svg = read("paper", "figures", "fig2-canon.svg")
        for part in (cid[:18], cid[18:36], cid[36:]):
            self.assertIn(part, svg)

    def test_listings_are_cut_from_places_that_exist(self):
        az = read("paper", "examples", "all_zero.ode")
        for mark in ("\n{\n", "    for x86_64 {", "    for arm64 {"):
            self.assertEqual(az.count(mark), 1, mark)
        quad = read("paper", "examples", "quad.ode")
        step = quad[quad.index("fn step("):]
        self.assertIn("    for arm64 calling {", step)
        self.assertLess(step.index("    for arm64 calling {"), step.index("fn quad("))
        self.assertEqual(read("proof-core", "examples", "arm64", "pad_arm64.spec").count("contract b3l_pad_arm64("), 1)
        trace = read("proof-core", "test_trace_proposal.py")
        first = trace[trace.index("contract t_equal_ct("):]
        first = first[:first.index("\n}") + 2]
        self.assertIn("returns same_ct(a, b)", first)
        self.assertIn("trace depends on n\n", first)
        # the caller's line that the report quotes is one that the trace tests verify
        self.assertIn("trace depends on n, same_ct(want, tag)", trace)
        self.assertIn("trace depends on n, same_ct(want, tag)", read("paper", "ode.typ"))

    def test_commands_named_are_commands_of_the_tool(self):
        tool = read("lang", "ode_tool.py")
        commands = set(re.findall(r'add_parser\("([\w-]+)"', tool))
        typ = read("paper", "ode.typ")
        named = set(re.findall(r"`ode ([a-z][a-z-]*)", typ))
        self.assertTrue(named, "no command found in the report")
        self.assertEqual(named - commands, set())
        appendix = typ[typ.index("Appendix A"):]
        listed = set(re.findall(r"\[`([a-z][a-z-]*)[ `]", appendix))
        self.assertEqual(listed, commands)

    @unittest.skipUnless(HAVE_VERIFIER, "the verifier (proof-core odeverify) is not built here")
    def test_example_is_shown_for_both_processors(self):
        facts = json.loads(read("paper", "facts.json"))["all_zero"]
        measured = json.loads(read("paper", "measured.json"))["all_zero"]
        tool = os.path.join(ROOT, "lang", "ode_tool.py")
        src = os.path.join(HERE, "examples", "all_zero.ode")
        with tempfile.TemporaryDirectory() as d:
            for target in ("x86_64", "arm64"):
                obj, proof = os.path.join(d, target + ".o"), os.path.join(d, target + ".proof")
                r = subprocess.run([sys.executable, tool, "pack", src, "--fn", "all_zero", "--target", target,
                                    "--out", obj, "--proof", proof], capture_output=True, text=True)
                self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
                r = subprocess.run([sys.executable, tool, "audit", obj, "--proof", proof,
                                    "--expect-contract", facts["id"]], capture_output=True, text=True)
                self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
                self.assertRegex(r.stdout, r"VERDICT:\s+shown")
                self.assertIn("ode_" + facts["id"], r.stdout)
                m = re.search(r"\(1 function, (\d+) instructions, (\d+) B, 1 exported symbol, 0 hooks\)", r.stdout)
                self.assertIsNotNone(m, r.stdout)
                self.assertEqual({"instructions": int(m.group(1)), "bytes": int(m.group(2))}, measured[target])


if __name__ == "__main__":
    unittest.main()
