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

    def test_refute_clean_and_planted_bugs_both_targets(self):
        vdir = os.path.join(ROOT, "proof-core", "examples", "verifier")
        zero_ode, zero_spec = os.path.join(vdir, "zero_x86.ode"), os.path.join(vdir, "zero_x86.spec")
        tag_ode, tag_spec = os.path.join(vdir, "tag_arm64.ode"), os.path.join(vdir, "tag_arm64.spec")

        # Clean functions: none refuted
        for ode_p, spec_p in ((MIX_ODE, MIX_SPEC), (tag_ode, tag_spec), (zero_ode, zero_spec), (ADLER_ODE, ADLER_SPEC)):
            r = _run_tool(["refute", ode_p, spec_p])
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("none found", r.stdout)

        with tempfile.TemporaryDirectory() as d:
            # 1. AArch64 wrong math (drop rev32) -> FALSE with differing output word
            with open(MIX_ODE) as f: m = f.read()
            p1 = os.path.join(d, "bad_math.ode")
            with open(p1, "w") as f: f.write(m.replace("  rev32 d.8h, d.8h\n", ""))
            r1 = _run_tool(["refute", p1, MIX_SPEC])
            self.assertEqual(r1.returncode, 1)
            self.assertIn("FALSE on probe", r1.stdout)
            self.assertIn("output `out[0]` disagrees", r1.stdout)

            # 2. AArch64 wrong callee-saved restore -> FALSE naming x19
            p2 = os.path.join(d, "bad_x19.ode")
            with open(p2, "w") as f: f.write(m.replace("x19 := saved_out[0]", "x19 := saved_a[0]"))
            r2 = _run_tool(["refute", p2, MIX_SPEC])
            self.assertEqual(r2.returncode, 1)
            self.assertIn("callee-saved register x19 changed", r2.stdout)

            # 3. x86-64 off-by-one step (add idx, 2) -> FALSE on a=[0, 1], n=2
            with open(zero_ode) as f: z = f.read()
            p3 = os.path.join(d, "bad_step.ode")
            with open(p3, "w") as f: f.write(z.replace("add idx, 1", "add idx, 2"))
            r3 = _run_tool(["refute", p3, zero_spec])
            self.assertEqual(r3.returncode, 1)
            self.assertIn("a=[0, 1], n=2", r3.stdout)
            self.assertIn("expected: 0", r3.stdout)
            self.assertIn("actual:   1", r3.stdout)

            # 4. Read-only input modified on AArch64 (even when `out` is right!) -> FALSE naming read-only input `a`
            with open(tag_ode) as f: tg = f.read()
            p4 = os.path.join(d, "bad_ro.ode")
            with open(p4, "w") as f: f.write(tg.replace("st1 {va.4s}, [out]", "st1 {va.4s}, [out]\n  st1 {va.4s}, [ap]", 1))
            r4 = _run_tool(["refute", p4, tag_spec, "--fn", "xor64"])
            self.assertEqual(r4.returncode, 1)
            self.assertIn("read-only input `a` modified", r4.stdout)

    def test_table_driven_compile_hints_and_empty_source(self):
        import ode_tool
        h_x86 = ode_tool._compile_error_hint("s.ode: line 3: `cmp edx, 0`: instruction not in x86.tab")
        self.assertIsNotNone(h_x86)
        self.assertIn("cmp D64, I", h_x86)
        h_arm = ode_tool._compile_error_hint("s.ode: line 4: `ldr x6, [x1, x3]`: not an instance of a row in arm64.tab")
        self.assertIsNotNone(h_arm)
        self.assertIn("ldr D64, [B64, N]", h_arm)
        with tempfile.TemporaryDirectory() as d:
            empty = os.path.join(d, "empty.ode")
            with open(empty, "w") as f: f.write("// no fn\n")
            resp = ode_tool.handle_request({"cmd": "check", "source": empty, "spec": MIX_SPEC})
            self.assertFalse(resp["ok"])
            self.assertIn("no `fn` definitions", resp["error"])
            self.assertIn("hint:", resp.get("hint", ""))


if __name__ == "__main__":
    unittest.main()
