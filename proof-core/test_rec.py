#!/usr/bin/env python3
"""Stage 1A tests: direct self-recursion (`decreases`), logarithmic stack budgets (`stackbits`),
multi-variable linear preconditions (`linpre`), and `atLeast` at calls, with positive and negative controls.

    python3 test_rec.py        (skipped where Lean's `lake` is not installed)"""
import os, subprocess, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "lang"))
import built, lean_verify, odec, prove, statement

LAKE = lean_verify.LAKE

SPEC = """\
def strip_even(n) {
    if n == 0 then 0 else if n % 2 == 1 then n else strip_even(n / 2)
}

contract ode_halves(n: number, t: number) {
    requires n >= 0
    requires 1024 * t + n <= 1000000
    decreases n
    trace depends on n, t
    returns strip_even(n)
    stack 128 + 64 * bits(n)
}

contract ode_halves_small(n: number) {
    requires n <= 63
    trace depends on n
    returns strip_even(n)
    stack 576
}

contract ode_halves_wrap(n: number, t: number) {
    requires 1024 * t + n <= 1000000
    trace depends on n, t
    returns strip_even(n)
    stack 192 + 64 * bits(n)
}
"""

ODE_SRC = """\
fn halves as "ode_halves" {
  cmp rdi, 0
  jne @nonzero
  xor eax, eax
  jmp @done
@nonzero:
  mov rax, rdi
  and rax, 1
  cmp rax, 0
  je @rec
  mov rax, rdi
  jmp @done
@rec:
  sub rsp, 24
  shr rdi, 1
  call ode_halves
  add rsp, 24
@done:
  ret
}

fn halves_small as "ode_halves_small" {
  xor esi, esi
  sub rsp, 24
  call ode_halves
  add rsp, 24
  ret
}

fn halves_wrap as "ode_halves_wrap" {
  sub rsp, 24
  call ode_halves
  add rsp, 24
  ret
}
"""

FN_NAMES = {"ode_halves": "halves", "ode_halves_small": "halves_small", "ode_halves_wrap": "halves_wrap"}


def build_objs(src, fns, d):
    ode_path = os.path.join(d, "rec.ode")
    with open(ode_path, "w") as f:
        f.write(src)
    out = []
    for sym in fns:
        o_path = os.path.join(d, f"{sym}.o")
        odec.build(ode_path, FN_NAMES[sym], o_path)
        out.append((o_path, sym))
    return out


def run_verifier(stmt_path, proof_path):
    r = subprocess.run([prove.EXE, prove.TABLE, stmt_path, proof_path], capture_output=True, text=True)
    return r.returncode, r.stdout


@unittest.skipUnless(LAKE, "Lean's lake is not installed")
class Recursion(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        built.built("odeprove")

    def check_case(self, spec_text, src_text, fns, expect_ok=True, expect_in=None):
        with tempfile.TemporaryDirectory() as d:
            objs = build_objs(src_text, fns, d)
            stmt_path = os.path.join(d, "stmt.txt")
            proof_path = os.path.join(d, "proof.txt")
            if expect_ok:
                prove.prove(spec_text, [(o, fn, "") for o, fn in objs], stmt_path, proof_path)
                rc, out = run_verifier(stmt_path, proof_path)
                self.assertEqual(rc, 0, out)
                self.assertEqual(out.strip(), "shown", out)
            else:
                lines = statement.statement(spec_text, objs)
                with open(stmt_path, "w") as f:
                    f.write("".join(l + "\n" for l in lines))
                with open(proof_path, "w") as f:
                    f.write("")
                rc0, out0 = run_verifier(stmt_path, proof_path)
                self.assertNotEqual(out0.strip(), "shown")
                try:
                    prove.prove(spec_text, [(o, fn, "") for o, fn in objs], stmt_path, proof_path)
                    rc, out = run_verifier(stmt_path, proof_path)
                    self.assertNotEqual(out.strip(), "shown", "expected refusal, got shown")
                    msg = out
                except SystemExit as e:
                    msg = str(e)
                if expect_in is not None:
                    self.assertIn(expect_in, msg)

    def test_positive_recursive_and_callers(self):
        self.check_case(SPEC, ODE_SRC, ["ode_halves", "ode_halves_small", "ode_halves_wrap"], expect_ok=True)

    def test_negative_non_decreasing_self_call(self):
        bad = ODE_SRC.replace("  shr rdi, 1\n", "")
        self.check_case(SPEC, bad, ["ode_halves"], expect_ok=False)

    def test_negative_missing_decreases_clause(self):
        bad_spec = SPEC.replace("    decreases n\n", "")
        self.check_case(bad_spec, ODE_SRC, ["ode_halves"], expect_ok=False)

    def test_negative_hidden_decreases_arg(self):
        bad_spec = SPEC.replace("    trace depends on n, t\n", "    trace depends on t\n", 1)
        self.check_case(bad_spec, ODE_SRC, ["ode_halves"], expect_ok=False, expect_in="trace depends on")

    def test_negative_insufficient_stack_step(self):
        bad_spec = SPEC.replace("stack 128 + 64 * bits(n)", "stack 128 + 16 * bits(n)")
        self.check_case(bad_spec, ODE_SRC, ["ode_halves"], expect_ok=False, expect_in="stack")

    def test_negative_linpre_violated_at_call(self):
        parts = SPEC.split("contract ode_halves_wrap")
        bad_spec = parts[0] + "contract ode_halves_wrap" + parts[1].replace("1000000", "2000000")
        self.check_case(bad_spec, ODE_SRC, ["ode_halves", "ode_halves_wrap"], expect_ok=False)

    def test_negative_fixed_caller_bound_too_large(self):
        bad_spec = SPEC.replace("requires n <= 63", "requires n <= 1023")
        self.check_case(bad_spec, ODE_SRC, ["ode_halves", "ode_halves_small"], expect_ok=False)


if __name__ == "__main__":
    unittest.main()
