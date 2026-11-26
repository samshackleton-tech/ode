#!/usr/bin/env pypy3
"""Test the independent second verifier (`proof-core/verify2.py`) against Lean's `odeverify`
on the exact same `.statement` and order-independent (`r ...`) `.proof` files across both
x86-64 and AArch64, including shuffled-facts order-independence and 4 negative controls each.
"""
import os
import random
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path[:0] = [
    HERE,
    os.path.join(ROOT, "lang"),
    os.path.join(ROOT, "core"),
    os.path.join(ROOT, "kcheck"),
]

import ode_audit
import statement
import verify2

HAVE_LEAN = os.path.isfile(os.path.join(HERE, ".lake", "build", "bin", "odeverify"))
ALL_ZERO = os.path.join(ROOT, "paper", "examples", "all_zero.ode")


def _extract_stmt_and_proof(src, target, tmp_dir):
    out_o = os.path.join(tmp_dir, f"a_{target}.o")
    out_p = os.path.join(tmp_dir, f"a_{target}.proof")
    res = ode_audit.pack_verified(src, None, out_o, out_p, target=target)
    assert res["verdict"] == "shown", res
    with open(out_o, "rb") as f:
        elf = ode_audit.parse_elf64(f.read())
    ocl = elf["by_name"][".ode.ocl"][0]["body"].decode("utf-8")
    sym = res["symbol"]
    bound = ocl.replace("contract (", f"contract {sym}(", 1)
    with open(out_p, "r", encoding="utf-8") as f:
        txt = f.read()
    idx = txt.find("\nfor ")
    pf_txt = txt[idx + 1:] if idx >= 0 else txt
    st_txt = "\n".join(statement.statement(bound, [(out_o, sym)])) + "\n"
    st_p = os.path.join(tmp_dir, f"a_{target}.statement")
    pf_p = os.path.join(tmp_dir, f"a_{target}.rawproof")
    with open(st_p, "w", encoding="utf-8") as f:
        f.write(st_txt)
    with open(pf_p, "w", encoding="utf-8") as f:
        f.write(pf_txt)
    tab = os.path.join(ROOT, "core", "x86.tab") if target == "x86_64" else os.path.join(ROOT, "arm64", "arm64.tab")
    return tab, st_p, pf_p, st_txt, pf_txt


@unittest.skipUnless(HAVE_LEAN, "requires built proof-core odeverify binary")
class TestVerify2(unittest.TestCase):
    def _run_dual(self, target):
        odeverify = os.path.join(HERE, ".lake", "build", "bin", "odeverify")
        with tempfile.TemporaryDirectory() as d:
            tab, st_p, pf_p, st_txt, pf_txt = _extract_stmt_and_proof(ALL_ZERO, target, d)
            # Proof must use order-independent `r ...` rows (no index-coupled `p ...` lines)
            self.assertTrue(any(l.startswith("r ") for l in pf_txt.splitlines()))
            self.assertFalse(any(l.startswith("p ") for l in pf_txt.splitlines()))

            # Positive: both independent verifiers approve the exact same statement + proof
            r1 = subprocess.run([odeverify, tab, st_p, pf_p], capture_output=True, text=True)
            r2 = subprocess.run([sys.executable, os.path.join(HERE, "verify2.py"), tab, st_p, pf_p],
                                capture_output=True, text=True)
            self.assertEqual(r1.returncode, 0, r1.stdout + r1.stderr)
            self.assertEqual(r1.stdout.strip(), "shown")
            self.assertEqual(r2.returncode, 0, r2.stdout + r2.stderr)
            self.assertIn("shown", r2.stdout)

            # Order-independence check: shuffle `given` facts inside verify2 before every check
            orig_ref = verify2.r_refutes_rows
            rng = random.Random(42)

            def shuffled_ref(given, starts, steps):
                g2 = list(given)
                rng.shuffle(g2)
                return orig_ref(g2, starts, steps)

            verify2.r_refutes_rows = shuffled_ref
            try:
                verify2.verify_files(tab, st_p, pf_p)
            finally:
                verify2.r_refutes_rows = orig_ref

            # Negative 1: corrupted arithmetic step
            pf_bad1 = os.path.join(d, "bad1.pf")
            self.assertIn("s 0 1 3 1 1", pf_txt)
            with open(pf_bad1, "w", encoding="utf-8") as f:
                f.write(pf_txt.replace("s 0 1 3 1 1", "s 0 1 2 1 1", 1))
            b1a = subprocess.run([odeverify, tab, st_p, pf_bad1], capture_output=True, text=True)
            b1b = subprocess.run([sys.executable, os.path.join(HERE, "verify2.py"), tab, st_p, pf_bad1],
                                 capture_output=True, text=True)
            self.assertNotEqual(b1a.returncode, 0)
            self.assertNotEqual(b1b.returncode, 0)

            # Negative 2: forged starting row not in given facts
            pf_bad2 = os.path.join(d, "bad2.pf")
            lines = pf_txt.splitlines()
            idx_r = next(i for i, l in enumerate(lines) if l.startswith("r "))
            lines[idx_r] = "r -999 0 0 1"
            with open(pf_bad2, "w", encoding="utf-8") as f:
                f.write("\n".join(lines) + "\n")
            b2a = subprocess.run([odeverify, tab, st_p, pf_bad2], capture_output=True, text=True)
            b2b = subprocess.run([sys.executable, os.path.join(HERE, "verify2.py"), tab, st_p, pf_bad2],
                                 capture_output=True, text=True)
            self.assertNotEqual(b2a.returncode, 0)
            self.assertNotEqual(b2b.returncode, 0)

            # Negative 3: trace violation (buffer kept out of trace, yet function branches on its byte)
            st_bad3 = os.path.join(d, "bad3.st")
            with open(st_bad3, "w", encoding="utf-8") as f:
                f.write(st_txt.replace("\nreturns ", "\nhidden a0\nreturns ", 1))
            b3a = subprocess.run([odeverify, tab, st_bad3, pf_p], capture_output=True, text=True)
            b3b = subprocess.run([sys.executable, os.path.join(HERE, "verify2.py"), tab, st_bad3, pf_p],
                                 capture_output=True, text=True)
            self.assertNotEqual(b3a.returncode, 0)
            self.assertNotEqual(b3b.returncode, 0)

            # Negative 4: mutated return instruction (`1` -> `0`)
            st_bad4 = os.path.join(d, "bad4.st")
            if target == "x86_64":
                mut = st_txt.replace(".mov 64 (.reg .rax) (.imm 0x1)", ".mov 64 (.reg .rax) (.imm 0x0)")
            else:
                mut = st_txt.replace(".movi .x0 0x1", ".movi .x0 0x0")
            self.assertNotEqual(mut, st_txt)
            with open(st_bad4, "w", encoding="utf-8") as f:
                f.write(mut)
            b4a = subprocess.run([odeverify, tab, st_bad4, pf_p], capture_output=True, text=True)
            b4b = subprocess.run([sys.executable, os.path.join(HERE, "verify2.py"), tab, st_bad4, pf_p],
                                 capture_output=True, text=True)
            self.assertNotEqual(b4a.returncode, 0)
            self.assertNotEqual(b4b.returncode, 0)

    def test_01_dual_verify_x86_64(self):
        self._run_dual("x86_64")

    def test_02_dual_verify_arm64(self):
        self._run_dual("arm64")

    def test_03_neq_dispatch_both_targets(self):
        """Chained unsorted equality dispatch uses `t neq 0` (linear paths) and passes both verifiers."""
        odeverify = os.path.join(HERE, ".lake", "build", "bin", "odeverify")
        if not os.path.exists(odeverify):
            self.skipTest("odeverify binary not built here")
        import odec, prove
        src = """
def op_code(x) {
    if x == 149 then 1
    else if x == 5 then 2
    else if x == 183 then 3
    else if x == 7 then 4
    else if x == 23 then 5
    else if x == 85 then 6
    else 0
}

fn dispatch6(x: number)
    requires x < 256
    returns op_code(x)
    trace depends on x
    stack 0
{
    for x86_64 {
        cmp rdi, 149
        je @c1
        cmp rdi, 5
        je @c2
        cmp rdi, 183
        je @c3
        cmp rdi, 7
        je @c4
        cmp rdi, 23
        je @c5
        cmp rdi, 85
        je @c6
        mov rax, 0
        ret
    @c1:
        mov rax, 1
        ret
    @c2:
        mov rax, 2
        ret
    @c3:
        mov rax, 3
        ret
    @c4:
        mov rax, 4
        ret
    @c5:
        mov rax, 5
        ret
    @c6:
        mov rax, 6
        ret
    }
    for arm64 {
        cmp x0, 149
        b.eq @c1
        cmp x0, 5
        b.eq @c2
        cmp x0, 183
        b.eq @c3
        cmp x0, 7
        b.eq @c4
        cmp x0, 23
        b.eq @c5
        cmp x0, 85
        b.eq @c6
        mov x0, 0
        ret
    @c1:
        mov x0, 1
        ret
    @c2:
        mov x0, 2
        ret
    @c3:
        mov x0, 3
        ret
    @c4:
        mov x0, 4
        ret
    @c5:
        mov x0, 5
        ret
    @c6:
        mov x0, 6
        ret
    }
}
"""
        for target in ("x86_64", "arm64"):
            with tempfile.TemporaryDirectory() as d:
                src_p = os.path.join(d, "disp.ode")
                with open(src_p, "w", encoding="utf-8") as f:
                    f.write(src)
                tab, st_p, pf_p, st_txt, pf_txt = _extract_stmt_and_proof(src_p, target, d)
                self.assertIn("t neq 0", pf_txt)
                r1 = subprocess.run([odeverify, tab, st_p, pf_p], capture_output=True, text=True)
                self.assertEqual(r1.returncode, 0, r1.stdout + r1.stderr)
                self.assertTrue(r1.stdout.startswith("shown"))
                r2 = subprocess.run([sys.executable, os.path.join(HERE, "verify2.py"), tab, st_p, pf_p],
                                    capture_output=True, text=True)
                self.assertEqual(r2.returncode, 0, r2.stdout + r2.stderr)
                self.assertTrue(r2.stdout.startswith("shown"))

    def test_04_hi_ls_ja_jbe_both_targets(self):
        """Unsigned `ja`/`jbe` (x86-64) and `b.hi`/`b.ls` (AArch64) verify in both Lean and verify2.py."""
        odeverify = os.path.join(HERE, ".lake", "build", "bin", "odeverify")
        if not os.path.exists(odeverify):
            self.skipTest("odeverify binary not built here")
        src = """
def cmp3(a, b) {
    if a > b then 2
    else if a <= b then
        if a == b then 1 else 0
    else 0
}

fn cmp3_fn(a: number, b: number)
    returns cmp3(a, b)
    trace depends on a, b
    stack 0
{
    for x86_64 {
        cmp rdi, rsi
        ja @gt
        cmp rdi, rsi
        jbe @le
        mov rax, 99
        ret
    @gt:
        mov rax, 2
        ret
    @le:
        cmp rdi, rsi
        je @eq
        mov rax, 0
        ret
    @eq:
        mov rax, 1
        ret
    }
    for arm64 {
        cmp x0, x1
        b.hi @gt
        cmp x0, x1
        b.ls @le
        mov x0, 99
        ret
    @gt:
        mov x0, 2
        ret
    @le:
        cmp x0, x1
        b.eq @eq
        mov x0, 0
        ret
    @eq:
        mov x0, 1
        ret
    }
}
"""
        for target in ("x86_64", "arm64"):
            with tempfile.TemporaryDirectory() as d:
                src_p = os.path.join(d, "hi.ode")
                with open(src_p, "w", encoding="utf-8") as f:
                    f.write(src)
                tab, st_p, pf_p, st_txt, pf_txt = _extract_stmt_and_proof(src_p, target, d)
                r1 = subprocess.run([odeverify, tab, st_p, pf_p], capture_output=True, text=True)
                self.assertEqual(r1.returncode, 0, r1.stdout + r1.stderr)
                self.assertTrue(r1.stdout.startswith("shown"))
                r2 = subprocess.run([sys.executable, os.path.join(HERE, "verify2.py"), tab, st_p, pf_p],
                                    capture_output=True, text=True)
                self.assertEqual(r2.returncode, 0, r2.stdout + r2.stderr)
                self.assertTrue(r2.stdout.startswith("shown"))

    def test_05_multi_fn_custom_calling_and_ebpf_dual_verify(self):
        """Multi-function custom-calling programs (`quad.ode` and full 6-fn `ebpf_unified.ode`) pass both verifiers."""
        odeverify = os.path.join(HERE, ".lake", "build", "bin", "odeverify")
        if not os.path.exists(odeverify):
            self.skipTest("odeverify binary not built here")
        sys.path.insert(0, os.path.join(ROOT, "lang"))
        import ode_audit
        cases = [
            (os.path.join(ROOT, "paper", "examples", "quad.ode"), None, "quad", 2),
            (os.path.join(HERE, "examples", "ebpf", "ebpf_unified.ode"),
             os.path.join(HERE, "examples", "ebpf", "ebpf_spec.ode"), "ebpf_run", 6),
            # two runs of bytes read in one loop (the run an address lies in is found, then shown)
            (os.path.join(HERE, "examples", "hasher", "hash_eq_ct.ode"),
             os.path.join(HERE, "examples", "hasher", "hash_eq_ct_spec.ode"), "ct_bytes_eq", 1),
        ]
        for src, spec, fn, expect_fns in cases:
            for target in ("x86_64", "arm64"):
                with tempfile.TemporaryDirectory() as d:
                    if spec:
                        shutil.copy2(spec, os.path.join(d, os.path.basename(spec)))
                    cand = os.path.join(d, os.path.basename(src))
                    shutil.copy2(src, cand)
                    out_o = os.path.join(d, "out.o")
                    out_p = os.path.join(d, "out.proof")
                    res = ode_audit.pack_verified(cand, None, out_o, out_p, fn_name=fn, target=target)
                    self.assertEqual(res["verdict"], "shown", res)
                    dump = os.path.join(d, "dump.sh")
                    st_p = os.path.join(d, "st.txt")
                    pf_p = os.path.join(d, "pf.txt")
                    with open(dump, "w", encoding="utf-8") as f:
                        f.write(f"#!/bin/sh\ncp \"$2\" {st_p}\ncp \"$3\" {pf_p}\necho shown\n")
                    os.chmod(dump, 0o755)
                    ode_audit.audit_binary(out_o, out_p, verify_bin=dump)
                    tab = os.path.join(ROOT, "arm64", "arm64.tab") if target == "arm64" else os.path.join(ROOT, "core", "x86.tab")
                    r1 = subprocess.run([odeverify, tab, st_p, pf_p], capture_output=True, text=True)
                    self.assertEqual(r1.returncode, 0, r1.stdout + r1.stderr)
                    r2 = subprocess.run([sys.executable, os.path.join(HERE, "verify2.py"), tab, st_p, pf_p],
                                        capture_output=True, text=True)
                    self.assertEqual(r2.returncode, 0, r2.stdout + r2.stderr)
                    self.assertIn(f"shown ({expect_fns} function{'s' if expect_fns != 1 else ''}, verify2)", r2.stdout)

    def test_06_mid_function_join_places(self):
        """Acyclic mid-function `place` join points (without `decreases`) compress 2^20 paths to linear
        time and work inside loops on both x86-64 and AArch64 in both Lean `odeverify` and `verify2.py`."""
        odeverify = os.path.join(HERE, ".lake", "build", "bin", "odeverify")
        if not os.path.exists(odeverify):
            self.skipTest("odeverify binary not built here")
        sys.path.insert(0, os.path.join(ROOT, "lang"))
        import ode_audit

        # (1) 20 sequential diamonds: 2^20 = 1,048,576 paths -> 40 linear paths.
        n_diam = 20
        defs = ["def step(x, k) { if x >= k then 1 else 2 }", "def acc0(x) { step(x, 0) }"]
        for k in range(1, n_diam):
            defs.append(f"def acc{k}(x) {{ acc{k-1}(x) + step(x, {k}) }}")
        x86, arm = ["mov rax, 0"], ["mov x9, 0"]
        for k in range(n_diam):
            x86 += [f"cmp rdi, {k}", f"jb @lt{k}", "add rax, 1", f"jmp @j{k}", f"@lt{k}:", "add rax, 2",
                    "place {", "    name acc = rax", "    fact 0 <= acc", f"    fact acc <= {2*(k+1)}",
                    f"    fact acc == acc{k}(x)", "}", f"@j{k}:"]
            arm += [f"cmp x0, {k}", f"b.lo @lt{k}", "add x9, x9, 1", f"b @j{k}", f"@lt{k}:", "add x9, x9, 2",
                    "place {", "    name acc = x9", "    fact 0 <= acc", f"    fact acc <= {2*(k+1)}",
                    f"    fact acc == acc{k}(x)", "}", f"@j{k}:"]
        x86.append("ret")
        arm += ["mov x0, x9", "ret"]
        chain_src = "\n".join(defs) + (
            f"\nfn chain20(x: number)\n    requires x < 1000\n    returns acc{n_diam-1}(x)\n"
            f"    trace depends on x\n    stack 0\n{{\n    for x86_64 {{\n        "
            + "\n        ".join(x86) + "\n    }\n    for arm64 {\n        "
            + "\n        ".join(arm) + "\n    }\n}\n"
        )

        # (2) 3-way diamond merged by a join `place` inside a byte loop.
        loop_join_src = """
def step_v(b) { if b == 0 then 1 else if b == 1 then 3 else 5 }
def sum_from(buf, i, acc) {
    if i >= len(buf) then acc
    else sum_from(buf, i + 1, acc + step_v(buf[i]))
}
def total(buf) { sum_from(buf, 0, 0) }

fn sum_steps(buf: n bytes, n: number)
    requires n < 100000
    returns total(buf)
    trace depends on buf, n
    stack 0
{
    for x86_64 {
        mov rcx, 0
        mov r10, 0
        place {
            name i = rcx
            name acc = r10
            fact 0 <= i
            fact i <= n
            fact 0 <= acc
            fact acc <= 5 * i
            fact total(buf) == sum_from(buf, i, acc)
            decreases n - i
        }
    @loop:
        cmp rcx, rsi
        jae @done
        mov r8, rdi
        add r8, rcx
        movzx eax, byte ptr [r8]
        cmp rax, 0
        je @z
        cmp rax, 1
        je @one
        mov r9, 5
        jmp @merged
    @z:
        mov r9, 1
        jmp @merged
    @one:
        mov r9, 3
        place {
            name i = rcx
            name dv = r9
            fact i < n
            fact 0 <= dv
            fact dv <= 5
            fact dv == step_v(buf[i])
        }
    @merged:
        add r10, r9
        add rcx, 1
        jmp @loop
    @done:
        mov rax, r10
        ret
    }
    for arm64 {
        mov x3, 0
        mov x4, 0
        place {
            name i = x3
            name acc = x4
            fact 0 <= i
            fact i <= n
            fact 0 <= acc
            fact acc <= 5 * i
            fact total(buf) == sum_from(buf, i, acc)
            decreases n - i
        }
    @loop:
        cmp x3, x1
        b.hs @done
        add x5, x0, x3
        ldrb w6, [x5, 0]
        cmp x6, 0
        b.eq @z
        cmp x6, 1
        b.eq @one
        mov x9, 5
        b @merged
    @z:
        mov x9, 1
        b @merged
    @one:
        mov x9, 3
        place {
            name i = x3
            name dv = x9
            fact i < n
            fact 0 <= dv
            fact dv <= 5
            fact dv == step_v(buf[i])
        }
    @merged:
        add x4, x4, x9
        add x3, x3, 1
        b @loop
    @done:
        mov x0, x4
        ret
    }
}
"""
        for nm, src in (("chain20", chain_src), ("sum_steps", loop_join_src)):
            for target in ("x86_64", "arm64"):
                with tempfile.TemporaryDirectory() as d:
                    p = os.path.join(d, f"{nm}.ode")
                    with open(p, "w", encoding="utf-8") as f:
                        f.write(src)
                    out_o = os.path.join(d, "out.o")
                    out_p = os.path.join(d, "out.proof")
                    res = ode_audit.pack_verified(p, None, out_o, out_p, fn_name=nm, target=target)
                    self.assertEqual(res["verdict"], "shown", res)
                    dump = os.path.join(d, "dump.sh")
                    st_p = os.path.join(d, "st.txt")
                    pf_p = os.path.join(d, "pf.txt")
                    with open(dump, "w", encoding="utf-8") as f:
                        f.write(f"#!/bin/sh\ncp \"$2\" {st_p}\ncp \"$3\" {pf_p}\necho shown\n")
                    os.chmod(dump, 0o755)
                    ode_audit.audit_binary(out_o, out_p, verify_bin=dump)
                    with open(pf_p, "r", encoding="utf-8") as f:
                        self.assertIn("\njoin ", f.read())
                    tab = os.path.join(ROOT, "arm64", "arm64.tab") if target == "arm64" else os.path.join(ROOT, "core", "x86.tab")
                    r1 = subprocess.run([odeverify, tab, st_p, pf_p], capture_output=True, text=True)
                    self.assertEqual(r1.returncode, 0, r1.stdout + r1.stderr)
                    r2 = subprocess.run([sys.executable, os.path.join(HERE, "verify2.py"), tab, st_p, pf_p],
                                        capture_output=True, text=True)
                    self.assertEqual(r2.returncode, 0, r2.stdout + r2.stderr)
                    self.assertIn("shown (1 function, verify2)", r2.stdout)

    def test_07_deep_unroll_lea_and_guarded_loop_entry(self):
        """Guarded loop entry (`Sym.general` path facts) + x86-64 `lea` (`at`) + 8x unroll pass both verifiers."""
        odeverify = os.path.join(HERE, ".lake", "build", "bin", "odeverify")
        if not os.path.exists(odeverify):
            self.skipTest("odeverify binary not built here")
        sys.path.insert(0, os.path.join(ROOT, "lang"))
        import ode_audit
        src = """
def sum_from(a, i, acc) {
    if i >= len(a) then acc
    else sum_from(a, i + 1, acc + a[i])
}
def total(a) { sum_from(a, 0, 0) }

fn fast_sum(a: n bytes, n: number)
    requires n <= 1048576
    returns total(a)
    trace depends on n
    stack 0
{
    for x86_64 {
        rcx := 0
        rax := 0
        cmp rsi, 8
        jb @tail
        place {
            fact 0 <= rcx
            fact rcx + 8 <= n
            fact 0 <= rax
            fact rax <= rcx * 255
            fact total(a) == sum_from(a, rcx, rax)
            decreases n - rcx
        }
    @bulk:
        mov r8, rdi
        add r8, rcx
        movzx edx, byte ptr [r8 + 0]
        add rax, rdx
        movzx edx, byte ptr [r8 + 1]
        add rax, rdx
        movzx edx, byte ptr [r8 + 2]
        add rax, rdx
        movzx edx, byte ptr [r8 + 3]
        add rax, rdx
        movzx edx, byte ptr [r8 + 4]
        add rax, rdx
        movzx edx, byte ptr [r8 + 5]
        add rax, rdx
        movzx edx, byte ptr [r8 + 6]
        add rax, rdx
        movzx edx, byte ptr [r8 + 7]
        add rax, rdx
        lea rcx, [rcx + 8]
        lea r9, [rcx + 8]
        cmp r9, rsi
        jbe @bulk
        place {
            fact 0 <= rcx
            fact rcx <= n
            fact 0 <= rax
            fact rax <= rcx * 255
            fact total(a) == sum_from(a, rcx, rax)
            decreases n - rcx
        }
    @tail:
        cmp rcx, rsi
        jae @done
        mov r8, rdi
        add r8, rcx
        movzx edx, byte ptr [r8 + 0]
        add rax, rdx
        lea rcx, [rcx + 1]
        jmp @tail
    @done:
        ret
    }
    for arm64 {
        x2 := 0
        x3 := 0
        cmp x1, 8
        b.lo @tail
        place {
            fact 0 <= x2
            fact x2 + 8 <= n
            fact 0 <= x3
            fact x3 <= x2 * 255
            fact total(a) == sum_from(a, x2, x3)
            decreases n - x2
        }
    @bulk:
        add x4, x0, x2
        ldrb w5, [x4, 0]
        ldrb w6, [x4, 1]
        ldrb w7, [x4, 2]
        ldrb w8, [x4, 3]
        add x5, x5, x6
        add x7, x7, x8
        add x5, x5, x7
        add x3, x3, x5
        ldrb w5, [x4, 4]
        ldrb w6, [x4, 5]
        ldrb w7, [x4, 6]
        ldrb w8, [x4, 7]
        add x5, x5, x6
        add x7, x7, x8
        add x5, x5, x7
        add x3, x3, x5
        add x2, x2, 8
        add x9, x2, 8
        cmp x9, x1
        b.ls @bulk
        place {
            fact 0 <= x2
            fact x2 <= n
            fact 0 <= x3
            fact x3 <= x2 * 255
            fact total(a) == sum_from(a, x2, x3)
            decreases n - x2
        }
    @tail:
        cmp x2, x1
        b.hs @done
        add x4, x0, x2
        ldrb w5, [x4, 0]
        add x3, x3, x5
        add x2, x2, 1
        b @tail
    @done:
        mov x0, x3
        ret
    }
}
"""
        for target in ("x86_64", "arm64"):
            with tempfile.TemporaryDirectory() as d:
                p = os.path.join(d, "fast_sum.ode")
                with open(p, "w", encoding="utf-8") as f:
                    f.write(src)
                out_o = os.path.join(d, "out.o")
                out_p = os.path.join(d, "out.proof")
                res = ode_audit.pack_verified(p, None, out_o, out_p, fn_name="fast_sum", target=target)
                self.assertEqual(res["verdict"], "shown", res)
                dump = os.path.join(d, "dump.sh")
                st_p = os.path.join(d, "st.txt")
                pf_p = os.path.join(d, "pf.txt")
                with open(dump, "w", encoding="utf-8") as f:
                    f.write(f"#!/bin/sh\ncp \"$2\" {st_p}\ncp \"$3\" {pf_p}\necho shown\n")
                os.chmod(dump, 0o755)
                ode_audit.audit_binary(out_o, out_p, verify_bin=dump)
                tab = os.path.join(ROOT, "arm64", "arm64.tab") if target == "arm64" else os.path.join(ROOT, "core", "x86.tab")
                r1 = subprocess.run([odeverify, tab, st_p, pf_p], capture_output=True, text=True)
                self.assertEqual(r1.returncode, 0, r1.stdout + r1.stderr)
                r2 = subprocess.run([sys.executable, os.path.join(HERE, "verify2.py"), tab, st_p, pf_p],
                                    capture_output=True, text=True)
                self.assertEqual(r2.returncode, 0, r2.stdout + r2.stderr)
                self.assertIn("shown (1 function, verify2)", r2.stdout)

    def test_08_der_valid_nested_ifx_and_tail_calls(self):
        """Nested `ifx` (`&&`/`||`) and verified tail calls (`jmp`/`b`) pass both verifiers on both arches."""
        odeverify = os.path.join(HERE, ".lake", "build", "bin", "odeverify")
        if not os.path.exists(odeverify):
            self.skipTest("odeverify binary not built")
        der_ref = os.path.join(ROOT, "paper", "EXPERIMENTS", "tasks", "der_valid_reference.ode")
        if not os.path.exists(der_ref):
            self.skipTest("der_valid_reference.ode not present")
        for target in ("x86_64", "arm64"):
            with tempfile.TemporaryDirectory() as d:
                out_o = os.path.join(d, "der.o")
                out_p = os.path.join(d, "der.proof")
                res = ode_audit.pack_verified(der_ref, None, out_o, out_p, fn_name="der_valid", target=target)
                self.assertEqual(res["verdict"], "shown", res)
                dump = os.path.join(d, "dump.sh")
                st_p = os.path.join(d, "st.txt")
                pf_p = os.path.join(d, "pf.txt")
                with open(dump, "w", encoding="utf-8") as f:
                    f.write(f"#!/bin/sh\ncp \"$2\" {st_p}\ncp \"$3\" {pf_p}\necho shown\n")
                os.chmod(dump, 0o755)
                ode_audit.audit_binary(out_o, out_p, verify_bin=dump)
                tab = os.path.join(ROOT, "arm64", "arm64.tab") if target == "arm64" else os.path.join(ROOT, "core", "x86.tab")
                r1 = subprocess.run([odeverify, tab, st_p, pf_p], capture_output=True, text=True)
                self.assertEqual(r1.returncode, 0, r1.stdout + r1.stderr)
                r2 = subprocess.run([sys.executable, os.path.join(HERE, "verify2.py"), tab, st_p, pf_p],
                                    capture_output=True, text=True)
                self.assertEqual(r2.returncode, 0, r2.stdout + r2.stderr)
                self.assertIn("shown (8 functions, verify2)", r2.stdout)

    def test_09_cmov_csel_constant_time_and_refusal(self):
        """Constant-time `cmov*` (x86-64) and `csel` (AArch64) pass both verifiers; branching on their result is refused."""
        odeverify = os.path.join(HERE, ".lake", "build", "bin", "odeverify")
        if not os.path.exists(odeverify):
            self.skipTest("odeverify binary not built")
        pos_src = """
def max2(a, b) { if a < b then b else a }

fn ct_max(a: number, b: number)
    requires a < 1000000
    requires b < 1000000
    returns max2(a, b)
    stack 0
{
    for x86_64 {
        mov rax, rdi
        cmp rdi, rsi
        cmovb rax, rsi
        ret
    }
    for arm64 {
        cmp x0, x1
        csel x0, x1, x0, lo
        ret
    }
}
"""
        neg_src = """
def max2(a, b) { if a < b then b else a }

fn bad_branch(a: number, b: number)
    requires a < 1000000
    requires b < 1000000
    returns max2(a, b)
    stack 0
{
    for x86_64 {
        mov rax, rdi
        cmp rdi, rsi
        cmovb rax, rsi
        cmp rax, 0
        je @done
    @done:
        ret
    }
    for arm64 {
        cmp x0, x1
        csel x0, x1, x0, lo
        cmp x0, 0
        b.eq @done
    @done:
        ret
    }
}
"""
        for target in ("x86_64", "arm64"):
            with tempfile.TemporaryDirectory() as d:
                pos_p = os.path.join(d, "ct_max.ode")
                with open(pos_p, "w", encoding="utf-8") as f:
                    f.write(pos_src)
                out_o = os.path.join(d, "ct_max.o")
                out_p = os.path.join(d, "ct_max.proof")
                res = ode_audit.pack_verified(pos_p, None, out_o, out_p, fn_name="ct_max", target=target)
                self.assertEqual(res["verdict"], "shown", res)
                dump = os.path.join(d, "dump.sh")
                st_p = os.path.join(d, "st.txt")
                pf_p = os.path.join(d, "pf.txt")
                with open(dump, "w", encoding="utf-8") as f:
                    f.write(f"#!/bin/sh\ncp \"$2\" {st_p}\ncp \"$3\" {pf_p}\necho shown\n")
                os.chmod(dump, 0o755)
                ode_audit.audit_binary(out_o, out_p, verify_bin=dump)
                tab = os.path.join(ROOT, "arm64", "arm64.tab") if target == "arm64" else os.path.join(ROOT, "core", "x86.tab")
                r1 = subprocess.run([odeverify, tab, st_p, pf_p], capture_output=True, text=True)
                self.assertEqual(r1.returncode, 0, r1.stdout + r1.stderr)
                r2 = subprocess.run([sys.executable, os.path.join(HERE, "verify2.py"), tab, st_p, pf_p],
                                    capture_output=True, text=True)
                self.assertEqual(r2.returncode, 0, r2.stdout + r2.stderr)
                self.assertIn("shown (1 function, verify2)", r2.stdout)

                neg_p = os.path.join(d, "bad.ode")
                with open(neg_p, "w", encoding="utf-8") as f:
                    f.write(neg_src)
                bad_o = os.path.join(d, "bad.o")
                bad_p = os.path.join(d, "bad.proof")
                with self.assertRaises((Exception, SystemExit)) as cm:
                    ode_audit.pack_verified(neg_p, None, bad_o, bad_p, fn_name="bad_branch", target=target)
                self.assertIn("kept out of the trace", str(cm.exception))

    def test_10_ct_base64_decode_out_buffer_dual_verify(self):
        """Output-buffer `ensures out = ...` + `wrote_pre` + `samebyte` + `cmov`/`csel` dual-verify on both arches."""
        odeverify = os.path.join(HERE, ".lake", "build", "bin", "odeverify")
        if not os.path.exists(odeverify):
            self.skipTest("odeverify binary not built")
        src_p = os.path.join(ROOT, "paper", "EXPERIMENTS", "tasks", "ct_base64_decode_reference.ode")
        for target in ("x86_64", "arm64"):
            with tempfile.TemporaryDirectory() as d:
                out_o = os.path.join(d, "ct_b64.o")
                out_p = os.path.join(d, "ct_b64.proof")
                res = ode_audit.pack_verified(src_p, None, out_o, out_p, fn_name="ct_base64_decode", target=target)
                self.assertEqual(res["verdict"], "shown", res)
                dump = os.path.join(d, "dump.sh")
                st_p = os.path.join(d, "st.txt")
                pf_p = os.path.join(d, "pf.txt")
                with open(dump, "w", encoding="utf-8") as f:
                    f.write(f"#!/bin/sh\ncp \"$2\" {st_p}\ncp \"$3\" {pf_p}\necho shown\n")
                os.chmod(dump, 0o755)
                ode_audit.audit_binary(out_o, out_p, verify_bin=dump)
                tab = os.path.join(ROOT, "arm64", "arm64.tab") if target == "arm64" else os.path.join(ROOT, "core", "x86.tab")
                r1 = subprocess.run([odeverify, tab, st_p, pf_p], capture_output=True, text=True)
                self.assertEqual(r1.returncode, 0, r1.stdout + r1.stderr)
                r2 = subprocess.run([sys.executable, os.path.join(HERE, "verify2.py"), tab, st_p, pf_p],
                                    capture_output=True, text=True)
                self.assertEqual(r2.returncode, 0, r2.stdout + r2.stderr)
                self.assertIn("shown (2 functions, verify2)", r2.stdout)
                # Negative control: tamper ensures upper bound 192 -> 191; verify2 must refuse
                with open(st_p, "r", encoding="utf-8") as f:
                    st_txt = f.read()
                bad_st = os.path.join(d, "bad_st.txt")
                with open(bad_st, "w", encoding="utf-8") as f:
                    f.write(st_txt.replace("ensures a0 (num 0) (num 192)", "ensures a0 (num 0) (num 191)", 1))
                r3 = subprocess.run([sys.executable, os.path.join(HERE, "verify2.py"), tab, bad_st, pf_p],
                                    capture_output=True, text=True)
                self.assertNotEqual(r3.returncode, 0, "tampered ensures must be refused by verify2")

    def test_11_cmov_csel_custom_calling_and_stack_spill_wrote(self):
        """`cmov`/`csel` caller invoking a custom-calling helper + stack spill inside a `wrote` loop dual-verifies."""
        odeverify = os.path.join(HERE, ".lake", "build", "bin", "odeverify")
        if not os.path.exists(odeverify):
            self.skipTest("odeverify binary not built")
        src = """
def bump(c) { if c >= 10 then c - 1 else 0 }
def out_list(src) { [bump(src[j]) % 256 for j in 0..8] }

fn helper(c: number)
    requires c < 256
    returns bump(c)
    stack 0
{
    for x86_64 calling {
        in c = rdi
        out = rax
        preserves rbx, rbp, r12, r13, r14, r15, r8, r9
    } {
        rax := 1
        cmp rdi, 10
        cmovae rax, rdi
        sub rax, 1
        ret
    }
    for arm64 calling {
        in c = x0
        out = x0
        preserves x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x2, x3
    } {
        x10 := 1
        cmp x0, 10
        csel x0, x0, x10, hs
        sub x0, x0, 1
        ret
    }
}

fn copy_bump(out: 8 bytes, src: n bytes, n: number)
    requires no_overlap(out, src)
    requires n >= 8
    requires n <= 8
    ensures out = out_list(src)
    returns 1
    trace depends on n
    stack 32
{
    for x86_64 {
        sub rsp, 24
        mov r8, rdi
        mov r9, rsi
        rdx := 0
        place {
            fact 0 <= rdx
            fact rdx <= 8
            keep r8, r9
            wrote out[.. rdx] = out_list(src)
            decreases 8 - rdx
        }
    @lp:
        cmp rdx, 8
        jae @done
        mov qword ptr [rsp + 0], rdx
        mov r10, r9
        add r10, rdx
        movzx edi, byte ptr [r10]
        call helper
        rcx := 0
        cmp rax, 0
        cmove rcx, rax
        mov rdx, qword ptr [rsp + 0]
        mov r11, r8
        add r11, rdx
        mov byte ptr [r11], al
        add rdx, 1
        jmp @lp
    @done:
        rax := 1
        add rsp, 24
        ret
    }
    for arm64 {
        sub sp, sp, 32
        str x30, [sp, 0]
        mov x2, x0
        mov x3, x1
        x1 := 0
        place {
            fact 0 <= x1
            fact x1 <= 8
            keep x2, x3
            wrote out[.. x1] = out_list(src)
            decreases 8 - x1
        }
    @lp:
        cmp x1, 8
        b.hs @done
        str x1, [sp, 8]
        add x9, x3, x1
        ldrb w0, [x9, 0]
        bl helper
        x11 := 0
        cmp x0, 0
        csel x11, x0, x11, eq
        ldr x1, [sp, 8]
        add x10, x2, x1
        strb w0, [x10, 0]
        add x1, x1, 1
        b @lp
    @done:
        x0 := 1
        ldr x30, [sp, 0]
        add sp, sp, 32
        ret
    }
}
"""
        for target in ("x86_64", "arm64"):
            with tempfile.TemporaryDirectory() as d:
                src_p = os.path.join(d, "t.ode")
                with open(src_p, "w", encoding="utf-8") as f:
                    f.write(src)
                out_o = os.path.join(d, "t.o")
                out_p = os.path.join(d, "t.proof")
                res = ode_audit.pack_verified(src_p, None, out_o, out_p, fn_name="copy_bump", target=target)
                self.assertEqual(res["verdict"], "shown", res)
                dump = os.path.join(d, "dump.sh")
                st_p = os.path.join(d, "st.txt")
                pf_p = os.path.join(d, "pf.txt")
                with open(dump, "w", encoding="utf-8") as f:
                    f.write(f"#!/bin/sh\ncp \"$2\" {st_p}\ncp \"$3\" {pf_p}\necho shown\n")
                os.chmod(dump, 0o755)
                ode_audit.audit_binary(out_o, out_p, verify_bin=dump)
                tab = os.path.join(ROOT, "arm64", "arm64.tab") if target == "arm64" else os.path.join(ROOT, "core", "x86.tab")
                r1 = subprocess.run([odeverify, tab, st_p, pf_p], capture_output=True, text=True)
                self.assertEqual(r1.returncode, 0, r1.stdout + r1.stderr)
                r2 = subprocess.run([sys.executable, os.path.join(HERE, "verify2.py"), tab, st_p, pf_p],
                                    capture_output=True, text=True)
                self.assertEqual(r2.returncode, 0, r2.stdout + r2.stderr)
                self.assertIn("shown (2 functions, verify2)", r2.stdout)

    def test_12_signed_disp_lea_and_cmov(self):
        """Negative displacement `lea rdx, [rdi - 65]` wraps via `r_signed` in verify2 (parity with Core.lean)."""
        odeverify = os.path.join(HERE, ".lake", "build", "bin", "odeverify")
        if not os.path.exists(odeverify):
            self.skipTest("odeverify binary not built")
        src = """
def shift_az(c) { if 65 <= c && c <= 90 then c - 65 else 0 }

fn shift_fn(c: number)
    requires c < 256
    returns shift_az(c)
    stack 0
{
    for x86_64 {
        rax := 100
        lea rdx, [rdi + 35]
        cmp rdi, 65
        cmovae rax, rdx
        rcx := 100
        cmp rdi, 90
        cmova rax, rcx
        lea rax, [rax - 100]
        ret
    }
}
"""
        with tempfile.TemporaryDirectory() as d:
            src_p = os.path.join(d, "s.ode")
            with open(src_p, "w", encoding="utf-8") as f:
                f.write(src)
            out_o = os.path.join(d, "s.o")
            out_p = os.path.join(d, "s.proof")
            res = ode_audit.pack_verified(src_p, None, out_o, out_p, fn_name="shift_fn", target="x86_64")
            self.assertEqual(res["verdict"], "shown", res)
            dump = os.path.join(d, "dump.sh")
            st_p = os.path.join(d, "st.txt")
            pf_p = os.path.join(d, "pf.txt")
            with open(dump, "w", encoding="utf-8") as f:
                f.write(f"#!/bin/sh\ncp \"$2\" {st_p}\ncp \"$3\" {pf_p}\necho shown\n")
            os.chmod(dump, 0o755)
            ode_audit.audit_binary(out_o, out_p, verify_bin=dump)
            tab = os.path.join(ROOT, "core", "x86.tab")
            r2 = subprocess.run([sys.executable, os.path.join(HERE, "verify2.py"), tab, st_p, pf_p],
                                capture_output=True, text=True)
            self.assertEqual(r2.returncode, 0, r2.stdout + r2.stderr)
            self.assertIn("shown (1 function, verify2)", r2.stdout)

    def test_13_hoisted_mask_and_contiguous_bitfield(self):
        """Loop-hoisted mask register (`constOf`), symmetric `and64`, and interior bitfield mask `0xF0` dual-verify."""
        odeverify = os.path.join(HERE, ".lake", "build", "bin", "odeverify")
        if not os.path.exists(odeverify):
            self.skipTest("odeverify binary not built")
        # 1. Loop-hoisted mask register on both arm64 (`and x9, x9, x7`) and x86_64 (`and r10, r8`)
        src_loop = """
def sum_low6(src, i, n, acc) {
    if i >= n then acc
    else sum_low6(src, i + 1, n, acc + (src[i] % 64))
}

fn sum_masked(src: n bytes, n: number)
    requires n <= 64
    returns sum_low6(src, 0, n, 0)
    trace depends on n
    stack 0
{
    for x86_64 {
        r8 := 63
        rax := 0
        rcx := 0
        place {
            fact 0 <= rcx
            fact rcx <= n
            fact r8 == 63
            fact rax <= rcx * 63
            fact sum_low6(src, 0, n, 0) == sum_low6(src, rcx, n, rax)
            decreases n - rcx
        }
    @lp:
        cmp rcx, rsi
        jae @done
        mov r9, rdi
        add r9, rcx
        movzx r10d, byte ptr [r9]
        and r10, r8
        add rax, r10
        add rcx, 1
        jmp @lp
    @done:
        ret
    }
    for arm64 {
        x7 := 63
        x2 := 0
        x3 := 0
        place {
            fact 0 <= x3
            fact x3 <= n
            fact x7 == 63
            fact x2 <= x3 * 63
            fact sum_low6(src, 0, n, 0) == sum_low6(src, x3, n, x2)
            decreases n - x3
        }
    @lp:
        cmp x3, x1
        b.hs @done
        add x8, x0, x3
        ldrb w9, [x8, 0]
        and x9, x9, x7
        add x2, x2, x9
        add x3, x3, 1
        b @lp
    @done:
        mov x0, x2
        ret
    }
}
"""
        for target in ("x86_64", "arm64"):
            with tempfile.TemporaryDirectory() as d:
                src_p = os.path.join(d, "m.ode")
                with open(src_p, "w", encoding="utf-8") as f:
                    f.write(src_loop)
                out_o, out_p = os.path.join(d, "m.o"), os.path.join(d, "m.proof")
                res = ode_audit.pack_verified(src_p, None, out_o, out_p, fn_name="sum_masked", target=target)
                self.assertEqual(res["verdict"], "shown", res)
                dump = os.path.join(d, "dump.sh")
                st_p, pf_p = os.path.join(d, "st.txt"), os.path.join(d, "pf.txt")
                with open(dump, "w", encoding="utf-8") as f:
                    f.write(f"#!/bin/sh\ncp \"$2\" {st_p}\ncp \"$3\" {pf_p}\necho shown\n")
                os.chmod(dump, 0o755)
                ode_audit.audit_binary(out_o, out_p, verify_bin=dump)
                tab = os.path.join(ROOT, "arm64", "arm64.tab") if target == "arm64" else os.path.join(ROOT, "core", "x86.tab")
                r2 = subprocess.run([sys.executable, os.path.join(HERE, "verify2.py"), tab, st_p, pf_p],
                                    capture_output=True, text=True)
                self.assertEqual(r2.returncode, 0, r2.stdout + r2.stderr)
                self.assertIn("shown (1 function, verify2)", r2.stdout)

        # 2. Interior contiguous bitmask `0xF0` (240) + commutative mask-first `and mask, val`
        src_bf = """
def hi_nibble_shifted(c) { ((c / 16) % 16) * 16 }

fn hi_nib(c: number)
    requires c < 256
    returns hi_nibble_shifted(c)
    stack 0
{
    for x86_64 {
        rax := 240
        and rax, rdi
        ret
    }
}
"""
        with tempfile.TemporaryDirectory() as d:
            src_p = os.path.join(d, "b.ode")
            with open(src_p, "w", encoding="utf-8") as f:
                f.write(src_bf)
            out_o, out_p = os.path.join(d, "b.o"), os.path.join(d, "b.proof")
            res = ode_audit.pack_verified(src_p, None, out_o, out_p, fn_name="hi_nib", target="x86_64")
            self.assertEqual(res["verdict"], "shown", res)
            dump = os.path.join(d, "dump.sh")
            st_p, pf_p = os.path.join(d, "st.txt"), os.path.join(d, "pf.txt")
            with open(dump, "w", encoding="utf-8") as f:
                f.write(f"#!/bin/sh\ncp \"$2\" {st_p}\ncp \"$3\" {pf_p}\necho shown\n")
            os.chmod(dump, 0o755)
            ode_audit.audit_binary(out_o, out_p, verify_bin=dump)
            tab = os.path.join(ROOT, "core", "x86.tab")
            r2 = subprocess.run([sys.executable, os.path.join(HERE, "verify2.py"), tab, st_p, pf_p],
                                capture_output=True, text=True)
            self.assertEqual(r2.returncode, 0, r2.stdout + r2.stderr)
            self.assertIn("shown (1 function, verify2)", r2.stdout)

    def test_14_multibyte_bytes_load_and_exact_byte_split(self):
        """Multi-byte (32-bit and 64-bit) loads from a `bytes` buffer plus exact `symSplit` byte
        extraction (`& 255`, `>> 8`, `>> 16`, `>> 24`, `>> 56`) dual-verify on both x86-64 and AArch64,
        and trace-excluded multi-byte loads still block branches."""
        odeverify = os.path.join(HERE, ".lake", "build", "bin", "odeverify")
        if not os.path.exists(odeverify):
            self.skipTest("odeverify binary not built here")
        sys.path.insert(0, os.path.join(ROOT, "lang"))
        import ode_audit

        # 1. 32-bit load from `pkt: n bytes` -> sum two big-endian 16-bit words (IPv4 checksum pattern)
        src32 = """
def be16_pair(pkt) { (pkt[0] * 256 + pkt[1]) + (pkt[2] * 256 + pkt[3]) }

fn sum4(pkt: n bytes, n: number)
    requires 4 <= n
    requires n <= 4096
    returns be16_pair(pkt)
    trace depends on pkt, n
    stack 0
{
    for x86_64 {
        mov r8d, dword ptr [rdi]
        mov rax, r8
        and rax, 255
        shl rax, 8
        mov r9, r8
        shr r9, 8
        and r9, 255
        add rax, r9
        mov r10, r8
        shr r10, 16
        and r10, 255
        shl r10, 8
        add rax, r10
        shr r8, 24
        add rax, r8
        ret
    }
    for arm64 {
        ldr w2, [x0, 0]
        x3 := 255
        and x4, x2, x3
        lsl x4, x4, 8
        lsr x5, x2, 8
        and x5, x5, x3
        add x4, x4, x5
        lsr x6, x2, 16
        and x6, x6, x3
        lsl x6, x6, 8
        add x4, x4, x6
        lsr x7, x2, 24
        add x0, x4, x7
        ret
    }
}
"""
        # 2. 64-bit load from `pkt: n bytes` -> sum first byte b[0] and last byte b[7]
        src64 = """
def ends8(pkt) { pkt[0] + pkt[7] }

fn sum_ends(pkt: n bytes, n: number)
    requires 8 <= n
    requires n <= 4096
    returns ends8(pkt)
    trace depends on pkt, n
    stack 0
{
    for x86_64 {
        mov r8, qword ptr [rdi]
        mov rax, r8
        and rax, 255
        shr r8, 56
        add rax, r8
        ret
    }
    for arm64 {
        ldr x2, [x0, 0]
        x3 := 255
        and x4, x2, x3
        lsr x5, x2, 56
        add x0, x4, x5
        ret
    }
}
"""
        for label, src, fn in [("mem32", src32, "sum4"), ("mem64", src64, "sum_ends")]:
            for target in ("x86_64", "arm64"):
                with tempfile.TemporaryDirectory() as d:
                    src_p = os.path.join(d, f"{label}.ode")
                    with open(src_p, "w", encoding="utf-8") as f:
                        f.write(src)
                    out_o, out_p = os.path.join(d, "o.o"), os.path.join(d, "o.proof")
                    res = ode_audit.pack_verified(src_p, None, out_o, out_p, fn_name=fn, target=target)
                    self.assertEqual(res["verdict"], "shown", f"{label}/{target}: {res}")
                    dump = os.path.join(d, "dump.sh")
                    st_p, pf_p = os.path.join(d, "st.txt"), os.path.join(d, "pf.txt")
                    with open(dump, "w", encoding="utf-8") as f:
                        f.write(f"#!/bin/sh\ncp \"$2\" {st_p}\ncp \"$3\" {pf_p}\necho shown\n")
                    os.chmod(dump, 0o755)
                    ode_audit.audit_binary(out_o, out_p, verify_bin=dump)
                    tab = os.path.join(ROOT, "arm64", "arm64.tab") if target == "arm64" else os.path.join(ROOT, "core", "x86.tab")
                    r2 = subprocess.run([sys.executable, os.path.join(HERE, "verify2.py"), tab, st_p, pf_p],
                                        capture_output=True, text=True)
                    self.assertEqual(r2.returncode, 0, f"{label}/{target}: {r2.stdout}{r2.stderr}")
                    self.assertIn("shown (1 function, verify2)", r2.stdout)

        # 3. Negative control: 32-bit load of trace-excluded bytes cannot drive a branch
        src_bad = """
fn bad_branch(pkt: n bytes, n: number)
    requires 4 <= n
    requires n <= 4096
    returns if pkt[0] == 0 then 1 else 0
    trace depends on n
    stack 0
{
    for x86_64 {
        mov r8d, dword ptr [rdi]
        and r8, 255
        cmp r8, 0
        je @z
        mov rax, 0
        ret
    @z:
        mov rax, 1
        ret
    }
}
"""
        with tempfile.TemporaryDirectory() as d:
            src_p = os.path.join(d, "bad.ode")
            with open(src_p, "w", encoding="utf-8") as f:
                f.write(src_bad)
            with self.assertRaises(BaseException) as ctx_err:
                ode_audit.pack_verified(src_p, None, os.path.join(d, "b.o"), os.path.join(d, "b.proof"),
                                        fn_name="bad_branch", target="x86_64")
            self.assertIn("kept out of the trace", str(ctx_err.exception))

    def test_15_or64_wrap_sub64_and_stacklin(self):
        """`or64` (verify2 parity), explicit `wrap` modular `sub64` before `cmov`/`csel` (plus exact refusal),
        and recursive linear `stack C + D * param` all verify end-to-end on both x86_64 and arm64."""
        odeverify = os.path.join(HERE, ".lake", "build", "bin", "odeverify")
        if not os.path.exists(odeverify):
            self.skipTest("odeverify binary not built")

        # 1. `or64` on both arches -> dual-verified by Lean odeverify AND verify2.py
        src_or = """
def hi_zero(a, n) {
    if a[0] < 128 && a[1] < 128 then 1 else 0
}

fn check2(a: n bytes, n: number)
    requires 2 <= n
    requires n <= 4096
    returns hi_zero(a, n)
    trace depends on a, n
    stack 0
{
    for x86_64 {
        movzx r8d, byte ptr [rdi]
        movzx r9d, byte ptr [rdi + 1]
        mov r10, r8
        or r10, r9
        and r10, 128
        cmp r10, 0
        je @ok
        cmp r8, 128
        jae @bad
        cmp r9, 128
        jae @bad
    @ok:
        mov rax, 1
        ret
    @bad:
        mov rax, 0
        ret
    }
    for arm64 {
        ldrb w2, [x0, 0]
        ldrb w3, [x0, 1]
        orr x5, x2, x3
        x4 := 128
        and x5, x5, x4
        cmp x5, 0
        b.eq @ok
        cmp x2, 128
        b.hs @bad
        cmp x3, 128
        b.hs @bad
    @ok:
        mov x0, 1
        ret
    @bad:
        mov x0, 0
        ret
    }
}
"""
        # 2. Wrapping `sub64` (`wrap`) before branchless `cmov`/`csel` on both arches -> dual-verified!
        src_wrap = """
def dec_cap(c) {
    if 65 <= c && c <= 90 then c - 65 else 255
}

fn cap_val(c: number)
    requires 0 <= c
    requires c <= 255
    returns dec_cap(c)
    trace depends on nothing
    stack 0
{
    for x86_64 {
        mov r8, rdi
        wrap
        sub r8, 65
        mov rax, 255
        cmp r8, 25
        cmovbe rax, r8
        ret
    }
    for arm64 {
        wrap
        sub x1, x0, 65
        mov x2, 255
        cmp x1, 25
        csel x0, x1, x2, ls
        ret
    }
}
"""
        # 2b. Negative control: identical `sub` WITHOUT `wrap` must be REFUSED because `c < 65` underflows!
        src_nowrap = src_wrap.replace("        wrap\n", "")

        for label, src, fn in [("or64", src_or, "check2"), ("wrap_sub", src_wrap, "cap_val")]:
            for target in ("x86_64", "arm64"):
                with tempfile.TemporaryDirectory() as d:
                    src_p = os.path.join(d, f"{label}.ode")
                    with open(src_p, "w", encoding="utf-8") as f:
                        f.write(src)
                    out_o, out_p = os.path.join(d, "o.o"), os.path.join(d, "o.proof")
                    res = ode_audit.pack_verified(src_p, None, out_o, out_p, fn_name=fn, target=target)
                    self.assertEqual(res["verdict"], "shown", f"{label}/{target}: {res}")
                    dump = os.path.join(d, "dump.sh")
                    st_p, pf_p = os.path.join(d, "st.txt"), os.path.join(d, "pf.txt")
                    with open(dump, "w", encoding="utf-8") as f:
                        f.write(f"#!/bin/sh\ncp \"$2\" {st_p}\ncp \"$3\" {pf_p}\necho shown\n")
                    os.chmod(dump, 0o755)
                    ode_audit.audit_binary(out_o, out_p, verify_bin=dump)
                    tab = os.path.join(ROOT, "arm64", "arm64.tab") if target == "arm64" else os.path.join(ROOT, "core", "x86.tab")
                    r2 = subprocess.run([sys.executable, os.path.join(HERE, "verify2.py"), tab, st_p, pf_p],
                                        capture_output=True, text=True)
                    self.assertEqual(r2.returncode, 0, f"{label}/{target}: {r2.stdout}{r2.stderr}")
                    self.assertIn("shown (1 function, verify2)", r2.stdout)

        with tempfile.TemporaryDirectory() as d:
            src_p = os.path.join(d, "nowrap.ode")
            with open(src_p, "w", encoding="utf-8") as f:
                f.write(src_nowrap)
            with self.assertRaises(BaseException):
                ode_audit.pack_verified(src_p, None, os.path.join(d, "b.o"), os.path.join(d, "b.proof"),
                                        fn_name="cap_val", target="x86_64")

        # 3. Recursive linear stack bound `stack 32 + 32 * d` verified in Lean on both arches!
        src_rec = """
def all_zero(a, n, d) {
    if d == 0 then 1
    else if a[d - 1] != 0 then 0
    else all_zero(a, n, d - 1)
}

fn rec_zero(a: n bytes, n: number, d: number)
    requires 0 <= d
    requires d <= n
    requires n <= 64
    returns all_zero(a, n, d)
    decreases d
    trace depends on a, n, d
    stack 32 + 32 * d
{
    for x86_64 {
        cmp rdx, 0
        je @base
        mov r8, rdx
        sub r8, 1
        lea r10, [rdi + r8]
        movzx r9d, byte ptr [r10]
        cmp r9, 0
        jne @bad
        push rbx
        mov rdx, r8
        call rec_zero
        pop rbx
        ret
    @base:
        mov rax, 1
        ret
    @bad:
        mov rax, 0
        ret
    }
    for arm64 {
        cmp x2, 0
        b.eq @base
        sub x3, x2, 1
        add x4, x0, x3
        ldrb w5, [x4, 0]
        cmp x5, 0
        b.ne @bad
        sub sp, sp, 32
        str x30, [sp, 0]
        mov x2, x3
        bl rec_zero
        ldr x30, [sp, 0]
        add sp, sp, 32
        ret
    @base:
        mov x0, 1
        ret
    @bad:
        mov x0, 0
        ret
    }
}
"""
        for target in ("x86_64", "arm64"):
            with tempfile.TemporaryDirectory() as d:
                src_p = os.path.join(d, "rec.ode")
                with open(src_p, "w", encoding="utf-8") as f:
                    f.write(src_rec)
                out_o, out_p = os.path.join(d, "rec.o"), os.path.join(d, "rec.proof")
                res = ode_audit.pack_verified(src_p, None, out_o, out_p, fn_name="rec_zero", target=target)
                self.assertEqual(res["verdict"], "shown", f"stacklin/{target}: {res}")


if __name__ == "__main__":
    unittest.main()
