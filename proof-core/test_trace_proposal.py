#!/usr/bin/env python3
"""Tests for paper/TRACE-PROPOSAL.md (section 12 & section 13):
- computed values in `trace depends on`
- `returns E` imposing no trace restriction on the returned number
- `result depends on` widening the default return-value rule for `returns r`
- `clear` steps at any instruction (inline and after calls)
- all 10 cases of section 5, all 6 refusal controls of section 13, inline forms,
  `result depends on` controls, and AArch64 equivalents.

Written before building the rule (section 13)."""
import os, subprocess, sys, tempfile, unittest

os.environ.setdefault("ODE_PROVE_EFFORT", "deep")

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path[:0] = [HERE, os.path.join(ROOT, "kcheck"), os.path.join(ROOT, "lang"), os.path.join(ROOT, "arm64"), os.path.join(ROOT, "core")]
import built, ode, odec, prove, statement

X86_TAB = os.path.join(ROOT, "core", "x86.tab")
ARM_TAB = os.path.join(ROOT, "arm64", "arm64.tab")

SPEC_DEFS = """
def same_from(a, b, at) {
    if at == len(a) then 1
    else if a[at] != b[at] then 0
    else same_from(a, b, at + 1)
}
def same(a, b) { same_from(a, b, 0) }

def same_ct_from(a, b, at, diff) {
    if at == len(a) then 1 - diff
    else same_ct_from(a, b, at + 1, (diff + ((256 + a[at] - b[at]) % 256) + 255) / 256)
}
def same_ct(a, b) { same_ct_from(a, b, 0, 0) }

def first_byte(p) { if len(p) == 0 then 0 else p[0] }
"""

X86_SRC = """target x86_64

fn equal_early as "t_equal_early" {
  xor ecx, ecx
  place {
    name i = rcx
    fact i <= n
    fact same_from(a, b, i) == same(a, b)
    decreases n - i
  }
@loop:
  cmp rcx, rdx
  jae @same
  mov r8, rdi
  add r8, rcx
  movzx eax, byte ptr [r8 + 0]
  mov r9, rsi
  add r9, rcx
  movzx r9d, byte ptr [r9 + 0]
  cmp rax, r9
  jne @differ
  add rcx, 1
  jmp @loop
@same:
  mov rax, 1
  jmp @done
@differ:
  xor eax, eax
@done:
  ret
}

fn equal_ct as "t_equal_ct" {
  xor ecx, ecx
  xor r10d, r10d
  place {
    name i = rcx
    name d = r10
    fact i <= n
    fact d <= 1
    fact same_ct_from(a, b, i, d) == same_ct(a, b)
    decreases n - i
  }
@loop:
  cmp rcx, rdx
  jae @end
  mov r8, rdi
  add r8, rcx
  movzx eax, byte ptr [r8 + 0]
  mov r9, rsi
  add r9, rcx
  movzx r9d, byte ptr [r9 + 0]
  add rax, 256
  sub rax, r9
  and rax, 255
  add r10, rax
  add r10, 255
  shr r10, 8
  add rcx, 1
  jmp @loop
@end:
  mov rax, 1
  sub rax, r10
  ret
}

fn differ_ct as "t_differ_ct" {
  xor ecx, ecx
  xor r10d, r10d
  place {
    name i = rcx
    fact i <= n
    decreases n - i
  }
@loop:
  cmp rcx, rdx
  jae @end
  mov r8, rdi
  add r8, rcx
  movzx eax, byte ptr [r8 + 0]
  mov r9, rsi
  add r9, rcx
  movzx r9d, byte ptr [r9 + 0]
  add rax, 256
  sub rax, r9
  and rax, 255
  or r10, rax
  add rcx, 1
  jmp @loop
@end:
  mov rax, r10
  ret
}

fn check_ct as "t_check_ct" {
  sub rsp, 8
  call t_equal_ct
  add rsp, 8
  cmp rax, 0
  je @bad
  mov rax, 10
  jmp @done
@bad:
  mov rax, 20
@done:
  ret
}

fn check_early as "t_check_early" {
  sub rsp, 8
  call t_equal_early
  add rsp, 8
  cmp rax, 0
  je @bad
  mov rax, 10
  jmp @done
@bad:
  mov rax, 20
@done:
  ret
}

fn check_swap as "t_check_swap" {
  sub rsp, 8
  mov r8, rdi
  mov rdi, rsi
  mov rsi, r8
  call t_equal_ct
  add rsp, 8
  cmp rax, 0
  je @bad
  mov rax, 10
  jmp @done
@bad:
  mov rax, 20
@done:
  ret
}

fn check_byte0 as "t_check_byte0" {
  cmp rdx, 0
  je @bad
  movzx eax, byte ptr [rdi + 0]
  cmp rax, 0
  je @bad
  mov rax, 10
  jmp @done
@bad:
  mov rax, 20
@done:
  ret
}

fn check_inline as "t_check_inline" {
  xor ecx, ecx
  xor r10d, r10d
  place {
    name i = rcx
    name d = r10
    fact i <= n
    fact d <= 1
    fact same_ct_from(want, tag, i, d) == same_ct(want, tag)
    decreases n - i
  }
@loop:
  cmp rcx, rdx
  jae @end
  mov r8, rdi
  add r8, rcx
  movzx eax, byte ptr [r8 + 0]
  mov r9, rsi
  add r9, rcx
  movzx r9d, byte ptr [r9 + 0]
  add rax, 256
  sub rax, r9
  and rax, 255
  add r10, rax
  add r10, 255
  shr r10, 8
  add rcx, 1
  jmp @loop
@end:
  mov rax, 1
  sub rax, r10
  cmp rax, 0
  je @bad
  mov rax, 10
  jmp @done
@bad:
  mov rax, 20
@done:
  ret
}

fn pick_ct as "t_pick_ct" {
  // args: want (rdi), tag (rsi), n (rdx), tab (rcx: tlen bytes), tlen (r8)
  push rbx
  mov rbx, rcx
  call t_equal_ct
  and rax, 1
  add rbx, rax
  movzx eax, byte ptr [rbx + 0]
  pop rbx
  ret
}

fn keep_ct as "t_keep_ct" {
  // args: want (rdi), tag (rsi), n (rdx), out (rcx: 1 bytes)
  push rbx
  mov rbx, rcx
  call t_equal_ct
  mov byte ptr [rbx + 0], al
  pop rbx
  ret
}

fn check_differ as "t_check_differ" {
  sub rsp, 8
  call t_differ_ct
  add rsp, 8
  cmp rax, 0
  je @bad
  mov rax, 10
  jmp @done
@bad:
  mov rax, 20
@done:
  ret
}

fn keep_differ as "t_keep_differ" {
  sub rsp, 8
  call t_differ_ct
  add rsp, 8
  ret
}

fn far_x as "t_far_x" {
  mov rax, rdi
  shr rax, 1
  ret
}

fn sign_far as "t_sign_far" {
  sub rsp, 8
  call t_far_x
  add rsp, 8
  cmp rax, 5
  je @hit
  mov rax, 0
  jmp @done
@hit:
  mov rax, 1
@done:
  ret
}
"""

ARM_SRC = """target arm64

fn arm_far as "t_arm_far" {
  cmp x1, 0
  b.eq @zero
  ldrb w0, [x0, 0]
  ret
@zero:
  mov x0, 0
  ret
}

fn arm_sign as "t_arm_sign" {
  sub sp, sp, 16
  str x30, [sp, 0]
  bl t_arm_far
  ldr x30, [sp, 0]
  add sp, sp, 16
  cmp x0, 5
  b.eq @hit
  mov x0, 0
  b @done
@hit:
  mov x0, 1
@done:
  ret
}

fn arm_sign_inline as "t_arm_sign_inline" {
  cmp x1, 0
  b.eq @zero
  ldrb w0, [x0, 0]
  b @check
@zero:
  mov x0, 0
@check:
  cmp x0, 5
  b.eq @hit
  mov x0, 0
  b @done
@hit:
  mov x0, 1
@done:
  ret
}

fn arm_keep as "t_arm_keep" {
  sub sp, sp, 32
  str x30, [sp, 0]
  str x19, [sp, 8]
  mov x19, x2
  bl t_arm_far
  strb w0, [x19, 0]
  ldr x19, [sp, 8]
  ldr x30, [sp, 0]
  add sp, sp, 32
  ret
}
"""


class ParserAndStatementTests(unittest.TestCase):
    """Offline tests: parsing `trace depends on` expressions and `result depends on`."""

    def test_trace_expr_parses_and_emits_traceexpr(self):
        spec = SPEC_DEFS + """
contract f(want: n bytes, tag: n bytes, n: number) {
    returns r
    trace depends on n, same_ct(want, tag)
    stack 0
}
"""
        s = ode.Spec(spec)
        c = s.contracts["f"]
        self.assertEqual(c["trace"], ["n"])
        self.assertEqual(len(c["trace_exprs"]), 1)
        with tempfile.TemporaryDirectory() as d:
            ode_p = os.path.join(d, "f.ode")
            obj_p = os.path.join(d, "f.o")
            with open(ode_p, "w") as f:
                f.write('target x86_64\nfn f as "f" {\n  xor eax, eax\n  ret\n}\n')
            odec.build(ode_p, "f", obj_p)
            lines = statement.statement(spec, [(obj_p, "f")])
            self.assertIn("hidden want", lines)
            self.assertIn("hidden tag", lines)
            self.assertNotIn("hidden n", lines)
            self.assertTrue(any(l.startswith("traceexpr (call same_ct ") for l in lines), lines)

    def test_result_depends_on_parses_and_emits_resultdep(self):
        spec = """
contract differ_ct(a: n bytes, b: n bytes, n: number) {
    returns r
    trace depends on n
    result depends on a, b
    stack 0
}
"""
        s = ode.Spec(spec)
        c = s.contracts["differ_ct"]
        self.assertEqual(c["trace"], ["n"])
        self.assertEqual(c["result_dep"], ["a", "b"])
        with tempfile.TemporaryDirectory() as d:
            ode_p = os.path.join(d, "d.ode")
            obj_p = os.path.join(d, "d.o")
            with open(ode_p, "w") as f:
                f.write('target x86_64\nfn d as "differ_ct" {\n  xor eax, eax\n  ret\n}\n')
            odec.build(ode_p, "d", obj_p)
            lines = statement.statement(spec, [(obj_p, "differ_ct")])
            self.assertIn("hidden a", lines)
            self.assertIn("hidden b", lines)
            self.assertIn("resultdep", lines)

    def test_result_depends_on_controls_refused(self):
        # 1. `result depends on` with `returns E` (not `returns r`) refused by statement
        bad1 = """
contract f(x: number) {
    returns x + 1
    result depends on x
    stack 0
}
"""
        with tempfile.TemporaryDirectory() as d:
            ode_p = os.path.join(d, "f.ode")
            obj_p = os.path.join(d, "f.o")
            with open(ode_p, "w") as f:
                f.write('target x86_64\nfn f as "f" {\n  mov rax, rdi\n  add rax, 1\n  ret\n}\n')
            odec.build(ode_p, "f", obj_p)
            with self.assertRaises(SystemExit):
                statement.statement(bad1, [(obj_p, "f")])

        # 2. unknown argument in `result depends on` refused
        bad2 = """
contract f(x: number) {
    returns r
    result depends on ghost
    stack 0
}
"""
        with tempfile.TemporaryDirectory() as d:
            ode_p = os.path.join(d, "f.ode")
            obj_p = os.path.join(d, "f.o")
            with open(ode_p, "w") as f:
                f.write('target x86_64\nfn f as "f" {\n  xor eax, eax\n  ret\n}\n')
            odec.build(ode_p, "f", obj_p)
            with self.assertRaises(SystemExit):
                statement.statement(bad2, [(obj_p, "f")])

        # 3. duplicate `result depends on` refused by parser
        bad3 = """
contract f(x: number) {
    returns r
    result depends on x
    result depends on x
    stack 0
}
"""
        with self.assertRaises(ode.Err):
            ode.Spec(bad3)


@unittest.skipUnless(built.LAKE is not None, "Lean toolchain not installed")
class TraceProposalVerifierTests(unittest.TestCase):
    """End-to-end prover + odeverify tests for all cases of TRACE-PROPOSAL.md."""

    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.exe = prove.EXE
        cls.tmp = tempfile.TemporaryDirectory()
        d = cls.tmp.name
        cls.x86_ode = os.path.join(d, "x86.ode")
        with open(cls.x86_ode, "w") as f:
            f.write(X86_SRC)
        cls.arm_ode = os.path.join(d, "arm.ode")
        with open(cls.arm_ode, "w") as f:
            f.write(ARM_SRC)
        cls.objs = {}
        cls.places = {}
        for fn in ("equal_early", "equal_ct", "differ_ct", "check_ct", "check_early",
                   "check_swap", "check_byte0", "check_inline", "pick_ct", "keep_ct",
                   "check_differ", "keep_differ", "far_x", "sign_far"):
            info = odec.compile_info(cls.x86_ode, fn)
            sym = info["symbol"]
            p = os.path.join(d, f"{sym}.o")
            with open(p, "wb") as f:
                f.write(info["elf"])
            cls.objs[sym] = p
            cls.places[sym] = info["places"].get(sym, "")
        for fn in ("arm_far", "arm_sign", "arm_sign_inline", "arm_keep"):
            info = odec.compile_info(cls.arm_ode, fn)
            sym = info["symbol"]
            p = os.path.join(d, f"{sym}.o")
            with open(p, "wb") as f:
                f.write(info["elf"])
            cls.objs[sym] = p
            cls.places[sym] = info["places"].get(sym, "")

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def run_verify(self, spec_text, syms, arm64=False):
        with tempfile.TemporaryDirectory() as d:
            st = os.path.join(d, "s.statement")
            pf = os.path.join(d, "s.proof")
            fns = [(self.objs[s], s, self.places[s]) for s in syms]
            prove.prove(spec_text, fns, st, pf)
            tab = ARM_TAB if arm64 else X86_TAB
            r = subprocess.run([self.exe, tab, st, pf], capture_output=True, text=True)
            return r.returncode, r.stdout + r.stderr, st, pf

    def verify_raw(self, spec_text, syms, proof_text, arm64=False):
        with tempfile.TemporaryDirectory() as d:
            st = os.path.join(d, "s.statement")
            pf = os.path.join(d, "s.proof")
            lines = statement.statement(spec_text, [(self.objs[s], s) for s in syms])
            with open(st, "w") as f:
                f.write("\n".join(lines) + "\n")
            with open(pf, "w") as f:
                f.write(proof_text)
            tab = ARM_TAB if arm64 else X86_TAB
            r = subprocess.run([self.exe, tab, st, pf], capture_output=True, text=True)
            return r.returncode, r.stdout + r.stderr

    # --- Section 5, Cases 1 to 10 ---

    def test_case1_equal_ct_shown(self):
        spec = SPEC_DEFS + """
contract t_equal_ct(a: n bytes, b: n bytes, n: number) {
    returns same_ct(a, b)
    trace depends on n
    stack 0
}
"""
        rc, out, _, _ = self.run_verify(spec, ["t_equal_ct"])
        self.assertEqual(rc, 0, out)
        self.assertIn("shown", out)

    def test_case2_and_3_check_calling_equal_ct(self):
        base = SPEC_DEFS + """
contract t_equal_ct(a: n bytes, b: n bytes, n: number) {
    returns same_ct(a, b)
    trace depends on n
    stack 0
}
"""
        # Case 2: trace depends on n, same_ct(want, tag) -> shown
        spec2 = base + """
contract t_check_ct(want: n bytes, tag: n bytes, n: number) {
    returns r
    trace depends on n, same_ct(want, tag)
    stack 16
}
"""
        rc, out, _, _ = self.run_verify(spec2, ["t_equal_ct", "t_check_ct"])
        self.assertEqual(rc, 0, out)
        self.assertIn("shown", out)

        # Case 3: trace depends on n alone -> refused at jump!
        spec3 = spec2.replace("trace depends on n, same_ct(want, tag)", "trace depends on n")
        with self.assertRaises((Exception, SystemExit)) as cm:
            self.run_verify(spec3, ["t_equal_ct", "t_check_ct"])
        self.assertIn("jump", str(cm.exception).lower())

    def test_case4_and_5_pick_calling_equal_ct(self):
        base = SPEC_DEFS + """
contract t_equal_ct(a: n bytes, b: n bytes, n: number) {
    returns same_ct(a, b)
    trace depends on n
    stack 0
}
"""
        # Case 5: trace depends on n, tlen, same_ct(want, tag) -> shown (reads table entry)
        spec5 = base + """
contract t_pick_ct(want: n bytes, tag: n bytes, n: number, tab: tlen bytes, tlen: number) {
    requires tlen >= 2
    returns r
    trace depends on n, tlen, same_ct(want, tag)
    result depends on tab
    stack 16
}
"""
        rc, out, _, _ = self.run_verify(spec5, ["t_equal_ct", "t_pick_ct"])
        self.assertEqual(rc, 0, out)
        self.assertIn("shown", out)

        # Case 4: trace depends on n, tlen alone -> refused at memory read!
        spec4 = spec5.replace("trace depends on n, tlen, same_ct(want, tag)", "trace depends on n, tlen")
        with self.assertRaises((Exception, SystemExit)) as cm:
            self.run_verify(spec4, ["t_equal_ct", "t_pick_ct"])
        self.assertTrue("address" in str(cm.exception).lower() or "read" in str(cm.exception).lower() or "trace" in str(cm.exception).lower(), str(cm.exception))

    def test_case6_keep_calling_equal_ct(self):
        spec = SPEC_DEFS + """
contract t_equal_ct(a: n bytes, b: n bytes, n: number) {
    returns same_ct(a, b)
    trace depends on n
    stack 0
}
contract t_keep_ct(want: n bytes, tag: n bytes, n: number, out: 1 bytes) {
    requires disjoint(want, tag, out, 1)
    ensures out[0 .. 1] = [same_ct(want, tag) % 256]
    trace depends on n
    stack 16
}
"""
        rc, out, _, _ = self.run_verify(spec, ["t_equal_ct", "t_keep_ct"])
        self.assertEqual(rc, 0, out)
        self.assertIn("shown", out)

    def test_case7_and_8_check_calling_equal_early(self):
        base = SPEC_DEFS + """
contract t_equal_early(a: n bytes, b: n bytes, n: number) {
    returns same(a, b)
    trace depends on a, b, n
    stack 0
}
"""
        # Case 8: trace depends on want, tag, n -> shown
        spec8 = base + """
contract t_check_early(want: n bytes, tag: n bytes, n: number) {
    returns r
    trace depends on want, tag, n
    stack 16
}
"""
        rc, out, _, _ = self.run_verify(spec8, ["t_equal_early", "t_check_early"])
        self.assertEqual(rc, 0, out)
        self.assertIn("shown", out)

        # Case 7: trace depends on n, same(want, tag) -> refused at call!
        spec7 = spec8.replace("trace depends on want, tag, n", "trace depends on n, same(want, tag)")
        with self.assertRaises((Exception, SystemExit)) as cm:
            self.run_verify(spec7, ["t_equal_early", "t_check_early"])
        self.assertIn("call", str(cm.exception).lower())

    def test_case9_and_10_sign_calling_far(self):
        base = """
contract t_far_x(x: number) {
    returns x / 2
    stack 0
}
"""
        # Case 10: trace depends on x -> shown (and also `trace depends on x / 2` -> shown)
        spec10 = base + """
contract t_sign_far(x: number) {
    returns r
    trace depends on x
    stack 16
}
"""
        rc, out, _, _ = self.run_verify(spec10, ["t_far_x", "t_sign_far"])
        self.assertEqual(rc, 0, out)
        self.assertIn("shown", out)

        spec10b = spec10.replace("trace depends on x", "trace depends on x / 2")
        rc, out, _, _ = self.run_verify(spec10b, ["t_far_x", "t_sign_far"])
        self.assertEqual(rc, 0, out)
        self.assertIn("shown", out)

        # Case 9: no trace depends on -> refused at jump!
        spec9 = spec10.replace("    trace depends on x\n", "")
        with self.assertRaises((Exception, SystemExit)) as cm:
            self.run_verify(spec9, ["t_far_x", "t_sign_far"])
        self.assertIn("jump", str(cm.exception).lower())

    # --- Section 13: six refusal controls + inline form ---

    def test_section13_refusals(self):
        # Refusal 1: equal_ct contract over equal_early code (jump on byte)
        spec_r1 = SPEC_DEFS + """
contract t_equal_early(a: n bytes, b: n bytes, n: number) {
    returns same(a, b)
    trace depends on n
    stack 0
}
"""
        with self.assertRaises((Exception, SystemExit)):
            self.run_verify(spec_r1, ["t_equal_early"])

        # Refusal 2: check with `trace depends on n, same_ct(want, tag)` jumping on want[0]
        spec_r2 = SPEC_DEFS + """
contract t_check_byte0(want: n bytes, tag: n bytes, n: number) {
    returns r
    trace depends on n, same_ct(want, tag)
    stack 0
}
"""
        with self.assertRaises((Exception, SystemExit)) as cm:
            self.run_verify(spec_r2, ["t_check_byte0"])
        self.assertIn("jump", str(cm.exception).lower())

        # Refusal 3 & 4: forged `clear` items refused directly by odeverify
        # Refusal 3: proof says rax holds `same_ct(want, tag)` at pc 0 (when rax does not!)
        bad_clear_val = "for t_check_byte0\nclear 0 rax (call same_ct (name want) (name tag))\n"
        rc, out = self.verify_raw(spec_r2, ["t_check_byte0"], bad_clear_val)
        self.assertNotEqual(rc, 0, out)
        self.assertNotIn("cannot read", out)
        self.assertNotIn("a line of the statement", out)

        # Refusal 4: proof says rax holds `want[0]` (not computed from listed things)
        bad_clear_unlisted = "for t_check_byte0\nclear 0 rax (index (name want) (num 0))\n"
        rc, out = self.verify_raw(spec_r2, ["t_check_byte0"], bad_clear_unlisted)
        self.assertNotEqual(rc, 0, out)
        self.assertIn("trace-clear", out)

        # Refusal 5: check calling equal_ct(tag, want, n) (reversed argument order!)
        spec_r5 = SPEC_DEFS + """
contract t_equal_ct(a: n bytes, b: n bytes, n: number) {
    returns same_ct(a, b)
    trace depends on n
    stack 0
}
contract t_check_swap(want: n bytes, tag: n bytes, n: number) {
    returns r
    trace depends on n, same_ct(want, tag)
    stack 16
}
"""
        with self.assertRaises((Exception, SystemExit)) as cm:
            self.run_verify(spec_r5, ["t_equal_ct", "t_check_swap"])
        self.assertIn("jump", str(cm.exception).lower())

        # Refusal 6: Case 2 with `returns` taken out of equal_ct's contract
        spec_r6 = SPEC_DEFS + """
contract t_equal_ct(a: n bytes, b: n bytes, n: number) {
    returns r
    trace depends on n
    result depends on a, b
    stack 0
}
contract t_check_ct(want: n bytes, tag: n bytes, n: number) {
    returns r
    trace depends on n, same_ct(want, tag)
    stack 16
}
"""
        with self.assertRaises((Exception, SystemExit)) as cm:
            self.run_verify(spec_r6, ["t_equal_ct", "t_check_ct"])
        self.assertIn("jump", str(cm.exception).lower())

    def test_inline_equal_ct_with_clear(self):
        # Section 12 Q2a: inline equal_ct inside check, cleared by value before jump
        spec_ok = SPEC_DEFS + """
contract t_check_inline(want: n bytes, tag: n bytes, n: number) {
    returns r
    trace depends on n, same_ct(want, tag)
    stack 0
}
"""
        rc, out, _, _ = self.run_verify(spec_ok, ["t_check_inline"])
        self.assertEqual(rc, 0, out)
        self.assertIn("shown", out)

        # Without `same_ct(want, tag)` in trace depends on: refused!
        spec_bad = spec_ok.replace("trace depends on n, same_ct(want, tag)", "trace depends on n")
        with self.assertRaises((Exception, SystemExit)):
            self.run_verify(spec_bad, ["t_check_inline"])

    # --- Section 12 Q4: `result depends on` ---

    def test_section12_q4_result_depends_on(self):
        # 1. differ_ct with `trace depends on n` and `result depends on a, b` -> shown
        spec_d = """
contract t_differ_ct(a: n bytes, b: n bytes, n: number) {
    returns r
    trace depends on n
    result depends on a, b
    stack 0
}
"""
        rc, out, _, _ = self.run_verify(spec_d, ["t_differ_ct"])
        self.assertEqual(rc, 0, out)
        self.assertIn("shown", out)

        # 2. differ_ct omitting `b` from `result depends on` -> refused!
        spec_d_bad = spec_d.replace("result depends on a, b", "result depends on a")
        with self.assertRaises((Exception, SystemExit)):
            self.run_verify(spec_d_bad, ["t_differ_ct"])

        # 3. check (`trace depends on want, tag, n`) calling differ_ct -> shown
        spec_chk_ok = spec_d + """
contract t_check_differ(want: n bytes, tag: n bytes, n: number) {
    returns r
    trace depends on want, tag, n
    stack 16
}
"""
        rc, out, _, _ = self.run_verify(spec_chk_ok, ["t_differ_ct", "t_check_differ"])
        self.assertEqual(rc, 0, out)
        self.assertIn("shown", out)

        # 4. check (`trace depends on n, same_ct(want, tag)`) calling differ_ct -> refused at jump!
        spec_chk_bad = SPEC_DEFS + spec_d + """
contract t_check_differ(want: n bytes, tag: n bytes, n: number) {
    returns r
    trace depends on n, same_ct(want, tag)
    stack 16
}
"""
        with self.assertRaises((Exception, SystemExit)) as cm:
            self.run_verify(spec_chk_bad, ["t_differ_ct", "t_check_differ"])
        self.assertIn("jump", str(cm.exception).lower())

        # 5. keep (`trace depends on n`, `result depends on want, tag`) forwarding differ_ct -> shown!
        spec_keep = spec_d + """
contract t_keep_differ(want: n bytes, tag: n bytes, n: number) {
    returns r
    trace depends on n
    result depends on want, tag
    stack 16
}
"""
        rc, out, _, _ = self.run_verify(spec_keep, ["t_differ_ct", "t_keep_differ"])
        self.assertEqual(rc, 0, out)
        self.assertIn("shown", out)

    # --- AArch64 equivalents ---

    def test_arm64_trace_proposal_call_and_inline(self):
        base = SPEC_DEFS + """
contract t_arm_far(p: n bytes, n: number) {
    returns first_byte(p)
    trace depends on n
    stack 0
}
"""
        # 1. arm_far with `trace depends on n` (p kept out of trace) -> shown
        rc, out, _, _ = self.run_verify(base, ["t_arm_far"], arm64=True)
        self.assertEqual(rc, 0, out)
        self.assertIn("shown", out)

        # 2. arm_sign calling arm_far with `trace depends on n, first_byte(p)` -> shown
        spec_ok = base + """
contract t_arm_sign(p: n bytes, n: number) {
    returns r
    trace depends on n, first_byte(p)
    stack 16
}
"""
        rc, out, _, _ = self.run_verify(spec_ok, ["t_arm_far", "t_arm_sign"], arm64=True)
        self.assertEqual(rc, 0, out)
        self.assertIn("shown", out)

        # 3. arm_sign with `trace depends on n` alone -> refused at jump!
        spec_bad = spec_ok.replace("trace depends on n, first_byte(p)", "trace depends on n")
        with self.assertRaises((Exception, SystemExit)) as cm:
            self.run_verify(spec_bad, ["t_arm_far", "t_arm_sign"], arm64=True)
        self.assertIn("jump", str(cm.exception).lower())

        # 4. inline arm_sign_inline with `trace depends on n, first_byte(p)` -> shown (via `clear`)!
        spec_in = SPEC_DEFS + """
contract t_arm_sign_inline(p: n bytes, n: number) {
    returns r
    trace depends on n, first_byte(p)
    stack 0
}
"""
        rc, out, _, _ = self.run_verify(spec_in, ["t_arm_sign_inline"], arm64=True)
        self.assertEqual(rc, 0, out)
        self.assertIn("shown", out)

        # 5. arm_keep calling arm_far and storing result with `trace depends on n` -> shown!
        spec_keep = base + """
contract t_arm_keep(p: n bytes, n: number, out: 1 bytes) {
    requires disjoint(p, out, 1)
    ensures out[0 .. 1] = [first_byte(p) % 256]
    trace depends on n
    stack 32
}
"""
        rc, out, _, _ = self.run_verify(spec_keep, ["t_arm_far", "t_arm_keep"], arm64=True)
        self.assertEqual(rc, 0, out)
        self.assertIn("shown", out)

    def test_void_result_depends_on_refused_by_verifier(self):
        """A function with no return value must be refused if its statement carries `resultdep`."""
        spec = """
contract t_void(x: number, out: 1 bytes) {
    ensures out[0 .. 1] = [0]
    stack 0
}
"""
        ode_src = 'target x86_64\nfn t_void as "t_void" {\n  xor eax, eax\n  mov byte ptr [rsi], al\n  ret\n}\n'
        with tempfile.TemporaryDirectory() as d:
            ode_p = os.path.join(d, "v.ode")
            obj_p = os.path.join(d, "v.o")
            st_p = os.path.join(d, "v.statement")
            pf_p = os.path.join(d, "v.proof")
            with open(ode_p, "w") as f: f.write(ode_src)
            odec.build(ode_p, "t_void", obj_p)
            prove.prove(spec, [(obj_p, "t_void", "")], st_p, pf_p)
            with open(st_p) as f: orig = f.read()
            self.assertIn("hidden x", orig)
            with open(st_p, "w") as f: f.write(orig.replace("hidden x\n", "hidden x\nresultdep x\n", 1))
            r = subprocess.run([os.path.join(HERE, ".lake", "build", "bin", "odeverify"),
                                os.path.join(HERE, "..", "core", "x86.tab"), st_p, pf_p],
                               capture_output=True, text=True)
            self.assertNotEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("result depends on requires a named return value", r.stdout + r.stderr)


if __name__ == "__main__":
    unittest.main()
