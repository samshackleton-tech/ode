#!/usr/bin/env python3
"""Offline tests for lang/ode_tool.py `advise` and `compare` on both x86-64 and AArch64.
Runs under CPython and PyPy without Lean. End-to-end `check` tests live in proof-core/test_ode_tool.py."""
import os, subprocess, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
TOOL = os.path.join(HERE, "ode_tool.py")
MIX_ODE = os.path.join(ROOT, "proof-core", "examples", "arm64", "mix.ode")
MIX_SPEC = os.path.join(ROOT, "proof-core", "examples", "arm64", "mix.spec")
ADLER_ODE = os.path.join(ROOT, "kcheck", "programs", "adler32", "adler32.ode")
ADLER_SPEC = os.path.join(ROOT, "kcheck", "programs", "adler32", "adler32.spec")


def _run_tool(args):
    return subprocess.run([sys.executable, TOOL] + args, capture_output=True, text=True)


class OfflineTests(unittest.TestCase):
    def test_advise_arm64_aligned_vs_misaligned_budget(self):
        r_ok = _run_tool(["advise", MIX_ODE, "--fn", "mix16_6", "--spec", MIX_SPEC,
                          "--arch", "ampere1", "--trace", "--max-line-splits", "0"])
        self.assertEqual(r_ok.returncode, 0, r_ok.stdout + r_ok.stderr)
        self.assertIn("0 line split(s)", r_ok.stdout)

        r_bad = _run_tool(["advise", MIX_ODE, "--fn", "mix16_6", "--spec", MIX_SPEC,
                           "--arch", "ampere1", "--trace", "--align", "7", "--max-line-splits", "0"])
        self.assertEqual(r_bad.returncode, 2, r_bad.stdout + r_bad.stderr)
        self.assertIn("4 line split(s)", r_bad.stdout)
        self.assertIn("FAIL:", r_bad.stdout)

    def test_advise_x86_adler32_loop_alignment(self):
        r = _run_tool(["advise", ADLER_ODE, "--spec", ADLER_SPEC, "--arch", "zen5", "--trace"])
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("aligning loop top saves 1 i-cache line(s)", r.stdout)
        self.assertIn("returned=True", r.stdout)

    def test_compare_two_variants_offline(self):
        src_a = """target arm64
fn f as "f_sym" {
  sub sp, sp, 16
  str x0, [sp, 0]
  ldr x1, [sp, 0]
  add sp, sp, 16
  ret
}
"""
        src_b = """target arm64
fn f as "f_sym" {
  sub sp, sp, 16
  str x0, [sp, 0]
  str x1, [sp, 8]
  add x2, sp, 0
  ld1 {v0.4s}, [x2]
  add sp, sp, 16
  ret
}
"""
        with tempfile.TemporaryDirectory() as d:
            pa, pb = os.path.join(d, "a.ode"), os.path.join(d, "b.ode")
            with open(pa, "w") as f: f.write(src_a)
            with open(pb, "w") as f: f.write(src_b)
            r = _run_tool(["compare", pa, pb, "--arch", "apple_m", "--trace"])
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("partial STLF stalls", r.stdout)
            self.assertIn("+1", r.stdout)


if __name__ == "__main__":
    unittest.main()
