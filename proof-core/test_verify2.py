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


if __name__ == "__main__":
    unittest.main()
