#!/usr/bin/env pypy3
"""Verify `b3l_wide128` (128 KiB subtree, 670 instructions, 15 wide-kernel calls) from ../kcheck/b3hashr.o.

    pypy3 test_wide128.py        (skipped where Lean's `lake` is not installed)

`b3l_wide128` hashes 128 whole chunks (131,072 bytes) by calling `blake3_servil_avx512_k32` four times
and `blake3_servil_avx512_p16` eleven times (levels of 64, 32, 16, 8, 4, 2, and 1 parent nodes), then
copies the 32-byte root chaining value from its stack frame to `out`. Its contract is read verbatim from
../kcheck/proofs/inner.spec, alongside ../kcheck/blake3.spec."""
import os, re, subprocess, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
KCHECK = os.path.join(HERE, "..", "kcheck")
sys.path.insert(0, HERE)
sys.path.insert(0, KCHECK)
import built, lean_verify, statement

OBJ = os.path.join(KCHECK, "b3hashr.o")
K32 = "blake3_servil_avx512_k32"
P16 = "blake3_servil_avx512_p16"
NAME = "b3l_wide128"
FUNCTIONS = [(OBJ, K32), (OBJ, P16), (OBJ, NAME)]
LAYOUT_KEYED = "layout keyed 40 { key: cv at 0, flags: byte at 32 }\n"

FOLLOW = "refused: the specification's words are not followed on the terms the function made"
STACK = "refused: a call needs more stack than this function's contract allows"


def contract_of(inner, name):
    (found,) = re.findall(rf"^contract {name}\(.*?^\}}\n", inner, re.S | re.M)
    return found


def spec_text(change=lambda t: t):
    with open(os.path.join(KCHECK, "blake3.spec")) as f:
        spec = f.read()
    with open(os.path.join(KCHECK, "proofs", "inner.spec")) as f:
        inner = f.read()
    return change(spec + "\n" + LAYOUT_KEYED + "\n" +
                  contract_of(inner, K32) + "\n" +
                  contract_of(inner, P16) + "\n" +
                  contract_of(inner, NAME))


def combined_proof():
    parts = []
    for _, sym in FUNCTIONS:
        with open(os.path.join(HERE, "proofs", sym + ".proof")) as f:
            parts.append(f.read())
    return "".join(parts)


def verify_with(spec):
    with tempfile.TemporaryDirectory() as d:
        st = os.path.join(d, "s")
        pf = os.path.join(d, "p")
        lines = statement.statement(spec, FUNCTIONS)
        with open(st, "w") as f:
            f.write("\n".join(lines) + "\n")
        with open(pf, "w") as f:
            f.write(combined_proof())
        r = subprocess.run([os.path.join(HERE, ".lake", "build", "bin", "odeverify"),
                            os.path.join(HERE, "..", "core", "x86.tab"), st, pf],
                           capture_output=True, text=True)
        return r.returncode == 0, (r.stdout + r.stderr).strip()


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Wide128(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")

    def test_shipped_b3l_wide128_is_shown_without_trace_depends_on_t(self):
        """`b3l_wide128` verifies with `trace depends on t` dropped (trace depends on nothing), which also
        implies the weaker `inner.spec` contract with `trace depends on t`."""
        def drop_trace(s):
            old = "    ensures out = subtree(kf.key, kf.flags, t, input)\n    trace depends on t\n"
            self.assertEqual(s.count(old), 1)
            return s.replace(old, "    ensures out = subtree(kf.key, kf.flags, t, input)\n")
        ok, out = verify_with(spec_text(drop_trace))
        self.assertTrue(ok, out)
        self.assertEqual(out, "shown")

    def test_false_contracts_are_refused(self):
        base = spec_text()
        # Fast refusal: stack budget too small for own frame (8,536 bytes) -> caught at `sub rsp, 8488`.
        old_s = "    ensures out = subtree(kf.key, kf.flags, t, input)\n    trace depends on t\n    stack 16384"
        new_s0 = "    ensures out = subtree(kf.key, kf.flags, t, input)\n    trace depends on t\n    stack 8192"
        self.assertEqual(base.count(old_s), 1)
        ok, out = verify_with(base.replace(old_s, new_s0, 1))
        self.assertFalse(ok, out)
        self.assertIn("need entail", out)

        # Fast refusal: stack budget fits own frame (8,536 bytes) but not the kernel call (+4,104 bytes).
        new_s = "    ensures out = subtree(kf.key, kf.flags, t, input)\n    trace depends on t\n    stack 12000"
        ok, out = verify_with(base.replace(old_s, new_s, 1))
        self.assertFalse(ok, out)
        self.assertIn(STACK, out)

        # Functional refusal: counter shifted by 1.
        old_t = "ensures out = subtree(kf.key, kf.flags, t, input)"
        new_t = "ensures out = subtree(kf.key, kf.flags, t + 1, input)"
        self.assertEqual(base.count(old_t), 1)
        ok, out = verify_with(base.replace(old_t, new_t, 1))
        self.assertFalse(ok, out)
        self.assertIn(FOLLOW, out)


if __name__ == "__main__":
    unittest.main()
