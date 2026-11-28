#!/usr/bin/env pypy3
"""Test the non-generalizing `check` verifier primitive across Core.lean, Reader.lean,
ProveMain.lean, Advice.lean, prove.py, and verify2.py on both x86-64 and AArch64.
"""
import os
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
import prove
import statement
import verify2

ODEVERIFY = os.path.join(HERE, ".lake", "build", "bin", "odeverify")
ODEPROVE = os.path.join(HERE, ".lake", "build", "bin", "odeprove")
HAVE_LEAN = os.path.isfile(ODEVERIFY) and os.path.isfile(ODEPROVE)


def _table(target):
    return os.path.join(ROOT, "core", "x86.tab") if target == "x86_64" else os.path.join(ROOT, "arm64", "arm64.tab")


def _compile_base(src, target, tmp_dir):
    src_p = os.path.join(tmp_dir, f"src_{target}.ode")
    out_o = os.path.join(tmp_dir, f"a_{target}.o")
    out_p = os.path.join(tmp_dir, f"a_{target}.proof")
    with open(src_p, "w", encoding="utf-8") as f:
        f.write(src)
    res = ode_audit.pack_verified(src_p, None, out_o, out_p, target=target)
    assert res["verdict"] == "shown", res
    with open(out_o, "rb") as f:
        elf = ode_audit.parse_elf64(f.read())
    ocl = elf["by_name"][".ode.ocl"][0]["body"].decode("utf-8")
    sym = res["symbol"]
    bound = ocl.replace("contract (", f"contract {sym}(", 1)
    stmt_lines = statement.statement(bound, [(out_o, sym)])
    # Extract existing places text from the compiled proof (between `for sym` and first proof item).
    with open(out_p, "r", encoding="utf-8") as f:
        ptxt = f.read()
    instr_pcs = []
    for ln in stmt_lines:
        if ln.startswith("i "):
            instr_pcs.append(int(ln.split()[1]))
    return bound, out_o, sym, stmt_lines, instr_pcs, ptxt


@unittest.skipUnless(HAVE_LEAN, "requires built proof-core odeverify/odeprove binaries")
class TestCheckPrimitive(unittest.TestCase):
    def test_01_passing_checks_entry_stacked_mid_and_loop_dual_verify(self):
        """Passing checks at pc=0, stacked at the same pc, mid-function preserving registers,
        and sharing a loop place pc must prove and dual-verify (`odeverify` + `verify2.py`)
        on both x86-64 and AArch64."""
        src = """\
def sum_down(n) {
    n
}

fn f_loop(n: number)
    requires n < 100
    returns sum_down(n)
    trace depends on n
    stack 0
{
    var i: u64 := n
    var acc: u64 := 0
    while i > 0
        maintains acc + i == n
        decreases i
    {
        acc += 1
        i -= 1
    }
    return acc
}
"""
        for target in ("x86_64", "arm64"):
            with tempfile.TemporaryDirectory() as td:
                bound, out_o, sym, stmt_lines, instr_pcs, orig_proof = _compile_base(src, target, td)
                # Find the loop place pc from the original proof and reconstruct its place block.
                place_pc = None
                for ln in orig_proof.splitlines():
                    if ln.startswith("place "):
                        place_pc = int(ln.split()[1])
                        break
                self.assertIsNotNone(place_pc, f"expected loop place in {target}")
                arg_reg = "rdi" if target == "x86_64" else "x0"
                # Extract canonical mapped places text for `f_loop` via odec.compile_info + _map_places_text.
                import ode_canon
                import ode_unified
                import odec
                src_p = os.path.join(td, f"src_{target}.ode")
                with open(src_p, "r", encoding="utf-8") as f:
                    src_txt = f.read()
                parsed = ode_unified.parse_unified(src_txt, src=src_p)
                info = odec.compile_info(src_p, "f_loop", target=target)
                spec_text, cname = ode_unified.extract_spec(parsed, target_key=target, fn_name="f_loop", src=src_p)
                canon = ode_canon.canonicalize(spec_text, contract_name=cname)
                base_places = ode_audit._map_places_text(
                    info.get("places", {}).get("f_loop", ""), canon["glossary"], "f_loop", sym, True
                )
                # Attach: (a) two stacked checks at pc=0, (b) a check at the exact same pc as the loop place.
                extra_checks = (
                    f"\ncheck +0x0 {{\n"
                    f"    name a = {arg_reg}\n"
                    f"    fact a <= 99\n"
                    f"}}\n"
                    f"check +0x0 {{\n"
                    f"    name a = {arg_reg}\n"
                    f"    fact a + 1 <= 100\n"
                    f"}}\n"
                    f"check +0x{place_pc:x} {{\n"
                    f"    fact a0 < 100\n"
                    f"}}\n"
                )
                st_p = os.path.join(td, "s.statement")
                pf_p = os.path.join(td, "s.proof")
                prove.prove(bound, [(out_o, sym, base_places + extra_checks)], st_p, pf_p)
                # Verify with Lean odeverify
                r = subprocess.run([ODEVERIFY, _table(target), st_p, pf_p], capture_output=True, text=True)
                self.assertEqual(r.returncode, 0, f"{target} odeverify failed: {r.stdout} {r.stderr}")
                self.assertEqual(r.stdout.strip(), "shown")
                # Verify with independent verify2.py
                n_v2 = verify2.verify_files(_table(target), st_p, pf_p)
                self.assertEqual(n_v2, 1)

    def test_02_failing_check_refused_by_both_verifiers_and_located(self):
        """A violated `check` precondition must be refused by prove.py, odeverify, and verify2.py
        even when the downstream instructions are sound, and `--locate` must report `at +PC`."""
        src = """\
def add1(n) {
    n + 1
}

fn f_add1(n: number)
    requires n < 100
    returns add1(n)
    trace depends on n
    stack 0
{
    return n + 1
}
"""
        for target in ("x86_64", "arm64"):
            with tempfile.TemporaryDirectory() as td:
                bound, out_o, sym, stmt_lines, instr_pcs, orig_proof = _compile_base(src, target, td)
                arg_reg = "rdi" if target == "x86_64" else "x0"
                # `n < 100` does NOT imply `n <= 50`!
                bad_check = (
                    f"check +0x0 {{\n"
                    f"    name a = {arg_reg}\n"
                    f"    fact a <= 50\n"
                    f"}}\n"
                )
                st_p = os.path.join(td, "bad.statement")
                pf_p = os.path.join(td, "bad.proof")
                with self.assertRaises(SystemExit):
                    prove.prove(bound, [(out_o, sym, bad_check)], st_p, pf_p)
                # Also craft a raw proof file containing the violated check and confirm both verifiers refuse it.
                with open(st_p, "w", encoding="utf-8") as f:
                    f.write("\n".join(stmt_lines) + "\n")
                with open(pf_p, "w", encoding="utf-8") as f:
                    f.write(f"for {sym}\ncheck 0\nname a {arg_reg}\nfact (bin <= (name a) (num 50))\n")
                r = subprocess.run([ODEVERIFY, _table(target), st_p, pf_p], capture_output=True, text=True)
                self.assertNotEqual(r.returncode, 0, f"{target} odeverify MUST refuse violated check")
                with self.assertRaises(verify2.Refuse):
                    verify2.verify_files(_table(target), st_p, pf_p)
                # Locate must report `at +0`.
                loc = subprocess.run([ODEPROVE, "--locate", _table(target), st_p, pf_p], capture_output=True, text=True)
                self.assertNotEqual(loc.returncode, 0)
                self.assertIn("at +0", loc.stdout)


if __name__ == "__main__":
    unittest.main()
