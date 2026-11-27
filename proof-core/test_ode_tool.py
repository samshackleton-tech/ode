#!/usr/bin/env python3
"""End-to-end tests for lang/ode_tool.py `check`: compiles Ode source on both AArch64 and x86-64,
proves, verifies with the Lean `odeverify` binary, checks exact source-line refusal diagnostics
(including fast termination on loops with no place and trace refusals), and checks budget enforcement."""
import json, os, re, subprocess, sys, tempfile, time, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
TOOL = os.path.join(ROOT, "lang", "ode_tool.py")
MIX_ODE = os.path.join(HERE, "examples", "arm64", "mix.ode")
MIX_SPEC = os.path.join(HERE, "examples", "arm64", "mix.spec")
ADLER_ODE = os.path.join(ROOT, "kcheck", "programs", "adler32", "adler32.ode")
ADLER_SPEC = os.path.join(ROOT, "kcheck", "programs", "adler32", "adler32.spec")

sys.path.insert(0, HERE)
import built


def _run_tool(args):
    return subprocess.run([sys.executable, TOOL] + args, capture_output=True, text=True)


@unittest.skipUnless(built.LAKE is not None, "Lean toolchain not installed")
class EndToEndToolTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")

    def test_check_arm64_and_out_dir(self):
        with tempfile.TemporaryDirectory() as d:
            r = _run_tool(["check", MIX_ODE, MIX_SPEC, "--arch", "apple_m", "--trace", "--out", d])
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("shown: arm_mix16_3, arm_mix16_again, arm_mix16_6", r.stdout)
            self.assertIn("0 line split(s)", r.stdout)
            self.assertTrue(os.path.exists(os.path.join(d, "arm_mix16_6.o")))
            self.assertTrue(os.path.exists(os.path.join(d, "out.statement")))
            self.assertTrue(os.path.exists(os.path.join(d, "out.proof")))

    def test_check_x86_adler32(self):
        r = _run_tool(["check", ADLER_ODE, ADLER_SPEC, "--arch", "zen5", "--trace"])
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("shown: ode_adler32", r.stdout)
        self.assertIn("aligning loop top saves 1 i-cache line(s)", r.stdout)

    def test_planted_diagnostics_pin_exact_source_lines(self):
        with tempfile.TemporaryDirectory() as d:
            with open(MIX_ODE) as f: m = f.read()

            # A: wrong callee-saved restore in AArch64 mix16_6 -> line 81 (`ret`) + regs + frame
            bad_arm = os.path.join(d, "bad_arm.ode")
            with open(bad_arm, "w") as f: f.write(m.replace("x19 := saved_out[0]", "x19 := saved_a[0]"))
            ra = _run_tool(["check", bad_arm, MIX_SPEC])
            self.assertEqual(ra.returncode, 1)
            self.assertIn("bad_arm.ode:81", ra.stdout)
            self.assertIn("x19=keep_out", ra.stdout)
            self.assertIn("a register a callee keeps", ra.stdout)
            self.assertIn("FALSE on probe", ra.stdout)
            self.assertIn("callee-saved register x19 changed", ra.stdout)

            # B: misaligned sp in AArch64 mix16_6 -> line 62 (`saved_lr[0] := x30` / `str x30, [sp, 64]`)
            bad_sp = os.path.join(d, "bad_sp.ode")
            with open(bad_sp, "w") as f:
                f.write(m.replace("sub sp, sp, frame.size", "sub sp, sp, 88", 2).replace("sub sp, sp, 88", "sub sp, sp, frame.size", 1))
            rb = _run_tool(["check", bad_sp, MIX_SPEC])
            self.assertEqual(rb.returncode, 1)
            self.assertIn("bad_sp.ode:62", rb.stdout)
            self.assertIn("saved_lr[0] := x30", rb.stdout)
            self.assertIn("multiple of 16", rb.stdout)
            self.assertIn("FALSE on probe", rb.stdout)

            # C1: linear loop with no place (common.ode) -> terminates quickly and names the loop head line
            t0 = time.time()
            rc1 = _run_tool(["check", os.path.join(ROOT, "kcheck", "programs", "common", "common.ode"),
                             os.path.join(ROOT, "kcheck", "programs", "common", "common.spec")])
            dt1 = time.time() - t0
            self.assertEqual(rc1.returncode, 1)
            self.assertLess(dt1, 15.0, f"linear loop with no place took {dt1:.2f}s")
            self.assertIn("common.ode:28", rc1.stdout)
            self.assertIn("with no place", rc1.stdout)
            self.assertIn("none found on 16 concrete probe", rc1.stdout)

            # C2: multi-branch loop with no place (adler32.ode with place removed) -> terminates and names line 34
            with open(ADLER_ODE) as f: c = f.read()
            bad_loop = os.path.join(d, "bad_loop.ode")
            with open(bad_loop, "w") as f: f.write(re.sub(r"  place \{.*?\n  \}\n", "", c, flags=re.S))
            t0 = time.time()
            rc = _run_tool(["check", bad_loop, ADLER_SPEC])
            dt = time.time() - t0
            self.assertEqual(rc.returncode, 1)
            self.assertLess(dt, 60.0, f"loop with no place took {dt:.2f}s")
            self.assertIn("bad_loop.ode:34", rc.stdout)
            self.assertIn("with no place", rc.stdout)
            self.assertIn("none found on 16 concrete probe", rc.stdout)

            # D: x86-64 adler32 branch on value kept out of the trace -> line 48 (`jae @l1`)
            with open(ADLER_SPEC) as f: sp = f.read()
            bad_spec = os.path.join(d, "bad.spec")
            with open(bad_spec, "w") as f: f.write(re.sub(r"    trace depends on .*\n", "", sp))
            rd = _run_tool(["check", ADLER_ODE, bad_spec])
            self.assertEqual(rd.returncode, 1)
            self.assertIn("adler32.ode:48", rd.stdout)
            self.assertIn("jae @l1", rd.stdout)
            self.assertIn("values kept out of the trace", rd.stdout)
            self.assertIn("none found on 16 concrete probe", rd.stdout)

            # E: budget enforcement after `shown` returns exit code 2
            re_b = _run_tool(["check", MIX_ODE, MIX_SPEC, "--arch", "ampere1", "--trace", "--align", "7", "--max-line-splits", "0"])
            self.assertEqual(re_b.returncode, 2)
            self.assertIn("shown:", re_b.stdout)
            self.assertIn("FAIL:", re_b.stdout)

    def test_verifier_in_ode_two_targets_and_in_source_budgets(self):
        vdir = os.path.join(HERE, "examples", "verifier")
        # 1. x86-64: zero_x86.ode (reg names in place {}, zero stack, in-source budget {})
        rx = _run_tool(["check", os.path.join(vdir, "zero_x86.ode"), os.path.join(vdir, "zero_x86.spec"),
                        "--arch", "zen5", "--trace"])
        self.assertEqual(rx.returncode, 0, rx.stdout + rx.stderr)
        self.assertIn("shown: v_all_zero", rx.stdout)

        # 2. AArch64: tag_arm64.ode (3 composed functions, in-source budget {})
        ra = _run_tool(["check", os.path.join(vdir, "tag_arm64.ode"), os.path.join(vdir, "tag_arm64.spec"),
                        "--arch", "apple_m", "--trace"])
        self.assertEqual(ra.returncode, 0, ra.stdout + ra.stderr)
        self.assertIn("shown: v_xor64, v_fold32, v_diff32", ra.stdout)

        # 3. In-source budget max_line_splits=0 catches --align 7 on AmpereOne with NO CLI --max flag!
        rb = _run_tool(["check", os.path.join(vdir, "tag_arm64.ode"), os.path.join(vdir, "tag_arm64.spec"),
                        "--arch", "ampere1", "--trace", "--align", "7"])
        self.assertEqual(rb.returncode, 2, rb.stdout + rb.stderr)
        self.assertIn("shown: v_xor64, v_fold32, v_diff32", rb.stdout)
        self.assertIn("max_line_splits=0", rb.stdout)

        # 4. AArch64 verified loop: zero_arm64.ode (cmp, b.hs, b.ne, b, ldrb, reg names in place {}, budget {})
        rz = _run_tool(["check", os.path.join(vdir, "zero_arm64.ode"), os.path.join(vdir, "zero_arm64.spec"),
                        "--arch", "apple_m", "--trace"])
        self.assertEqual(rz.returncode, 0, rz.stdout + rz.stderr)
        self.assertIn("shown: arm_all_zero", rz.stdout)
        # Planted off-by-one / wrong return in AArch64 loop -> refused AND caught as FALSE on probe!
        with open(os.path.join(vdir, "zero_arm64.ode")) as f:
            z_src = f.read()
        with tempfile.TemporaryDirectory() as d:
            bad_z = os.path.join(d, "bad_zero.ode")
            with open(bad_z, "w") as f:
                f.write(z_src.replace("x0 := 0", "x0 := 1"))
            r_bad = _run_tool(["check", bad_z, os.path.join(vdir, "zero_arm64.spec")])
            self.assertEqual(r_bad.returncode, 1)
            self.assertIn("FALSE on probe", r_bad.stdout)
            # Planted loop with no place on AArch64 -> fast termination and exact loop-head line!
            no_pl = os.path.join(d, "no_place.ode")
            with open(no_pl, "w") as f:
                f.write(re.sub(r"  place \{.*?\n  \}\n", "", z_src, flags=re.S))
            t0 = time.time()
            r_np = _run_tool(["check", no_pl, os.path.join(vdir, "zero_arm64.spec")])
            self.assertEqual(r_np.returncode, 1)
            self.assertLess(time.time() - t0, 15.0)
            self.assertIn("with no place", r_np.stdout)

    def test_compare_with_spec_verifies_both_variants(self):
        with open(ADLER_ODE) as f: orig = f.read()
        nops = "".join("  nop\n" for _ in range(20))
        aligned = orig.replace("@l0:\n", nops + "@l0:\n", 1)
        with tempfile.TemporaryDirectory() as d:
            p_al = os.path.join(d, "adler_aligned.ode")
            with open(p_al, "w") as f: f.write(aligned)
            r = _run_tool(["compare", ADLER_ODE, p_al, "--spec", ADLER_SPEC, "--arch", "zen5", "--trace"])
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("verdicts: A=shown, B=shown", r.stdout)
            self.assertIn("code bytes", r.stdout)

    def test_include_json_serve_and_surgical_arithmetic_diagnostics(self):
        b3spec = os.path.join(ROOT, "kcheck", "blake3.spec")
        comp_ode = os.path.join(HERE, "examples", "arm64", "compress_arm64.ode")
        comp_spec = os.path.join(HERE, "examples", "arm64", "compress_arm64.spec")
        pad_ode = os.path.join(HERE, "examples", "arm64", "pad_arm64.ode")
        pad_spec = os.path.join(HERE, "examples", "arm64", "pad_arm64.spec")
        z_ode = os.path.join(HERE, "examples", "verifier", "zero_x86.ode")
        z_spec = os.path.join(HERE, "examples", "verifier", "zero_x86.spec")

        # 1. --include + --json verifies AArch64 BLAKE3 compress kernel directly
        r = _run_tool(["check", comp_ode, comp_spec, "--include", b3spec, "--json"])
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        d = json.loads(r.stdout)
        self.assertEqual(d["verdict"], "shown")
        self.assertEqual(d["target"], "arm64")
        self.assertGreater(d["proof_bytes"], 0)
        self.assertLess(d["proof_bytes"], 1024)

        # 2. Persistent `serve` JSON-lines worker handles multiple check/advise/refute requests
        p = subprocess.Popen([sys.executable, TOOL, "serve"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
        try:
            reqs = [
                {"cmd": "check", "source": pad_ode, "spec": pad_spec, "include": [b3spec]},
                {"cmd": "check", "source": z_ode, "spec": z_spec},
                {"cmd": "advise", "source": comp_ode},
            ]
            for req in reqs:
                p.stdin.write(json.dumps(req) + "\n")
                p.stdin.flush()
                resp = json.loads(p.stdout.readline())
                self.assertTrue(resp["ok"], resp)
        finally:
            p.stdin.close()
            p.stdout.close()
            p.wait()

        # 3. Surgical arithmetic diagnostics decode `need entail` into readable parameter/register names + hint
        with open(z_ode) as f:
            z_src = f.read()
        with tempfile.TemporaryDirectory() as td:
            bp = os.path.join(td, "bad_inv.ode")
            with open(bp, "w") as f:
                f.write(z_src.replace("i <= n", "i <= n + 1"))
            rb = _run_tool(["check", bp, z_spec, "--json"])
            self.assertEqual(rb.returncode, 1)
            db = json.loads(rb.stdout)
            self.assertEqual(db["verdict"], "no proof found")
            self.assertIsNotNone(db["arithmetic"])
            self.assertIn(db["arithmetic"]["kind"], ("entail", "compare"))
            self.assertIn("rsi(n)", db["diagnostic"])
            self.assertIn("relevant facts:", db["diagnostic"])
            self.assertIn("hint:", db["diagnostic"])


if __name__ == "__main__":
    unittest.main()
