#!/usr/bin/env pypy3
"""End-to-end tests for Step A: unified `.ode` source files, single canonical `.ocl` extraction,
multi-architecture `for <arch>` blocks, `calling` on `fn` inside `.ode`, hash-named `.ocl`
filename verification, and refusal of contractless functions.

    pypy3 test_unified_ode.py
"""
import json, os, platform, shutil, subprocess, sys, tempfile, textwrap, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path[:0] = [HERE, os.path.join(ROOT, "lang"), os.path.join(ROOT, "kcheck"), os.path.join(ROOT, "arm64")]
import built, lean_verify, obj as aobj, ode_audit, ode_canon, ode_tool, ode_unified, odec

LAKE = lean_verify.LAKE
X86_LINUX = platform.system() == "Linux" and platform.machine() in ("x86_64", "amd64")
ARM_MACHINE = platform.machine() in ("arm64", "aarch64")

# The same file the language report prints (paper/ode.typ reads it): what the report shows is what is tested here.
with open(os.path.join(ROOT, "paper", "examples", "quad.ode"), "r", encoding="utf-8") as _f:
    QUAD_UNIFIED_ODE = _f.read()

INC_UNIFIED_ODE = textwrap.dedent("""\
    // Single-function multi-arch unified `.ode` sharing the exact same canonical `.ocl` hash!
    def add_seven(n) { n + 7 }

    inline fn bump for x86_64 (r: gpr) changes r {
        add r, 7
    }

    inline fn bump for arm64 (r: gpr) changes r {
        add r, r, 7
    }

    fn inc7(x: number)
        requires x < 1000000
        returns add_seven(x)
        trace depends on x
        stack 0
    {
        for x86_64 {
            mov rax, rdi
            bump(rax)
            ret
        }
        for arm64 {
            bump(x0)
            ret
        }
    }
""")


class UnifiedFrontEndTests(unittest.TestCase):
    """Fast front-end, canonicalization, and hash-filename tests (no Lean required)."""

    def test_step_shares_identical_ocl_hash_across_x86_and_arm64(self):
        c_x86 = ode_canon.canonicalize_ode(QUAD_UNIFIED_ODE, fn_name="step", target="x86_64")
        c_arm = ode_canon.canonicalize_ode(QUAD_UNIFIED_ODE, fn_name="step", target="arm64")
        self.assertEqual(c_x86["contract_id"], c_arm["contract_id"])
        self.assertEqual(c_x86["canonical"], c_arm["canonical"])
        # Zero register names and zero `calling` block in canonical `.ocl`!
        self.assertNotIn("calling", c_x86["canonical"])
        self.assertNotIn("r10", c_x86["canonical"])
        self.assertNotIn("x9", c_arm["canonical"])

    def test_quad_ocl_is_unaffected_by_helper_step_changes(self):
        c1 = ode_canon.canonicalize_ode(QUAD_UNIFIED_ODE, fn_name="quad", target="x86_64")
        self.assertNotIn("step", c1["canonical"])
        self.assertNotIn("1000000", c1["canonical"])
        # Refactor `step`'s register assignment and precondition: `quad`'s `.ocl` hash must stay identical!
        mut = QUAD_UNIFIED_ODE.replace("requires a < 1000000", "requires a < 500000", 1)
        mut = mut.replace("in a = r10, b = r11", "in a = rcx, b = r11", 1)
        c2 = ode_canon.canonicalize_ode(mut, fn_name="quad", target="x86_64")
        self.assertEqual(c1["contract_id"], c2["contract_id"])
        self.assertEqual(c1["canonical"], c2["canonical"])

    def test_contract_first_declaration_without_body(self):
        src = textwrap.dedent("""\
            def double(x) { x + x }
            fn dbl(x: number)
                requires x < 1000
                returns double(x)
                trace depends on x
                stack 0
            {}
        """)
        c = ode_canon.canonicalize_ode(src, fn_name="dbl")
        self.assertTrue(ode_canon.B32_RE.fullmatch(c["contract_id"]))
        self.assertTrue(ode_canon.is_canonical(c["canonical"]))

    def test_contractless_and_malformed_unified_ode_refused(self):
        bad_cases = [
            ("bare fn without params/contract", "fn foo {\n    ret\n}\n", "no parameter list and contract"),
            ("fn with empty contract clauses", "fn foo(x: number) {\n    for x86_64 { ret }\n}\n", "no contract clauses"),
            ("standalone contract block in .ode", "def f(x) { x }\ncontract f(x: number) { returns x stack 0 }\n", "standalone `contract`"),
            ("duplicate top-level name", "def f(x) { x }\ndef f(y) { y }\n", "duplicate name"),
            ("duplicate for target", "fn f(x: number) returns x stack 0 {\n for x86_64 { ret }\n for x86_64 { ret }\n}\n", "more than once"),
        ]
        for label, src, expected in bad_cases:
            with self.subTest(label=label):
                with self.assertRaises(ode_unified.UnifiedErr) as ctx:
                    ode_unified.parse_unified(src, "bad.ode")
                self.assertIn(expected, str(ctx.exception))

    def test_hash_named_ocl_file_write_and_spoof_rejection(self):
        with tempfile.TemporaryDirectory() as d:
            inc_p = os.path.join(d, "inc.ode")
            with open(inc_p, "w") as f:
                f.write(INC_UNIFIED_ODE)
            # CLI `canon --out-dir` writes `<52-char-b32>.ocl`
            rc = ode_tool.main(["canon", inc_p, "--fn", "inc7", "--target", "x86_64", "--out-dir", d, "--json"])
            self.assertEqual(rc, 0)
            c = ode_canon.canonicalize_ode(INC_UNIFIED_ODE, fn_name="inc7", target="x86_64")
            ocl_p = os.path.join(d, ode_canon.ocl_filename(c["contract_id"]))
            self.assertTrue(os.path.isfile(ocl_p))
            # Reading the genuine hash-named `.ocl` succeeds in both canonicalize_file & spec-test
            c_back = ode_canon.canonicalize_file(ocl_p)
            self.assertEqual(c_back["contract_id"], c["contract_id"])
            self.assertEqual(ode_audit.run_spec_test(ocl_p, "f0", ["5"]), 12)
            # Tampering with contents under the original hash filename MUST be refused!
            tampered_p = os.path.join(d, ode_canon.ocl_filename(c["contract_id"]))
            with open(tampered_p, "w") as f:
                f.write(c["canonical"].replace("+ 7", "+ 8"))
            with self.assertRaises(ValueError) as ctx1:
                ode_canon.canonicalize_file(tampered_p)
            self.assertIn("contract filename mismatch", str(ctx1.exception))
            with self.assertRaises(ValueError) as ctx2:
                ode_audit.run_spec_test(tampered_p, "f0", ["5"])
            self.assertIn("contract filename mismatch", str(ctx2.exception))

    def test_legacy_contractless_ode_refused_without_spec(self):
        with tempfile.TemporaryDirectory() as d:
            leg_p = os.path.join(d, "legacy.ode")
            with open(leg_p, "w") as f:
                f.write('fn f as "ode_f" {\n  mov rax, rdi\n  ret\n}\n')
            with self.assertRaises(ValueError) as ctx:
                ode_audit.pack_verified(leg_p, None, os.path.join(d, "a.o"), os.path.join(d, "a.proof"))
            self.assertIn("must have a contract", str(ctx.exception))


@unittest.skipUnless(LAKE, "Lean's lake is not installed")
class UnifiedEndToEndVerification(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        built.built("odeprove")

    def test_quad_unified_ode_verified_both_arches(self):
        """One unified `quad.ode` with custom `calling { ... }` proves and verifies `shown` on
        BOTH x86-64 and AArch64 with zero duplicate contracts."""
        with tempfile.TemporaryDirectory() as d:
            q_p = os.path.join(d, "quad.ode")
            with open(q_p, "w") as f:
                f.write(QUAD_UNIFIED_ODE)
            for tgt in ("x86_64", "arm64"):
                with self.subTest(target=tgt):
                    res = ode_tool.run_check(q_p, target=tgt)
                    self.assertEqual(res["verdict"], "shown", f"{tgt} failed:\n{res.get('diagnostic')}")
                    self.assertEqual(res["functions"], ["step", "quad"])

    def test_inc7_unified_pack_audit_and_spoofed_contract_filename(self):
        """One unified `inc.ode` packs on BOTH x86-64 and AArch64 to the EXACT SAME 52-char
        contract hash and `ode_<52>` symbol, passes `ode audit`, and refuses a spoofed `<hash>.ocl`."""
        with tempfile.TemporaryDirectory() as d:
            inc_p = os.path.join(d, "inc.ode")
            with open(inc_p, "w") as f:
                f.write(INC_UNIFIED_ODE)
            r_x86 = ode_audit.pack_verified(
                inc_p, None, os.path.join(d, "inc_x86.o"), os.path.join(d, "inc_x86.proof"),
                fn_name="inc7", target="x86_64",
            )
            r_arm = ode_audit.pack_verified(
                inc_p, None, os.path.join(d, "inc_arm.o"), os.path.join(d, "inc_arm.proof"),
                fn_name="inc7", target="arm64",
            )
            self.assertEqual(r_x86["verdict"], "shown", r_x86.get("errors"))
            self.assertEqual(r_arm["verdict"], "shown", r_arm.get("errors"))
            self.assertEqual(r_x86["contract_b32"], r_arm["contract_b32"])
            self.assertEqual(r_x86["symbol"], r_arm["symbol"])

            # Write genuine hash-named `.ocl` and pass to `audit_binary`: passes!
            cid = r_x86["contract_b32"]
            ocl_p = os.path.join(d, ode_canon.ocl_filename(cid))
            with open(ocl_p, "w") as f:
                f.write(r_x86["canonical_ocl"])
            ok_res = ode_audit.audit_binary(
                os.path.join(d, "inc_x86.o"), os.path.join(d, "inc_x86.proof"),
                expect_contract=cid, contract_path=ocl_p,
            )
            self.assertEqual(ok_res["verdict"], "shown", ok_res.get("errors"))

            # Tamper contents under the same `<52>.ocl` filename: `audit_binary` MUST refuse!
            with open(ocl_p, "w") as f:
                f.write(r_x86["canonical_ocl"].replace("+ 7", "+ 9"))
            bad_res = ode_audit.audit_binary(
                os.path.join(d, "inc_x86.o"), os.path.join(d, "inc_x86.proof"),
                contract_path=ocl_p,
            )
            self.assertNotEqual(bad_res["verdict"], "shown")
            self.assertTrue(any("contract filename mismatch" in e for e in bad_res["errors"]), bad_res["errors"])

    def test_pack_refuses_exporting_custom_calling_as_c_abi(self):
        with tempfile.TemporaryDirectory() as d:
            q_p = os.path.join(d, "quad.ode")
            with open(q_p, "w") as f:
                f.write(QUAD_UNIFIED_ODE)
            with self.assertRaises(ValueError) as ctx:
                ode_audit.pack_verified(
                    q_p, None, os.path.join(d, "step.o"), os.path.join(d, "step.proof"),
                    fn_name="step", target="x86_64",
                )
            self.assertIn("calling", str(ctx.exception))


if __name__ == "__main__":
    unittest.main()
