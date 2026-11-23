#!/usr/bin/env pypy3
"""Verify `b3l_wide32` (32 KiB subtree, 259 instructions, 6 wide-kernel calls) from ../kcheck/b3hashr.o.

    pypy3 test_wide32.py        (skipped where Lean's `lake` is not installed)

`b3l_wide32` hashes 32 whole chunks (32,768 bytes) by calling `blake3_servil_avx512_k32` once (32 lanes
of 16 blocks each) and `blake3_servil_avx512_p16` five times (16, 8, 4, 2, and 1 parent nodes), then
copies the 32-byte root chaining value from its stack frame to `out` with two `movups` loads/stores.
Its contract is read verbatim from ../kcheck/proofs/inner.spec, alongside ../kcheck/blake3.spec.

Also verified: the stronger contract with `trace depends on t` removed (its trace depends on nothing at
all, not even the chunk counter `t`). Every false mutation of the contract or source is refused."""
import os, re, shutil, subprocess, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
KCHECK = os.path.join(HERE, "..", "kcheck")
sys.path.insert(0, HERE)
sys.path.insert(0, KCHECK)
sys.path.insert(0, os.path.join(HERE, "..", "lang"))
import built, lean_verify, odec, prove, statement

OBJ = os.path.join(KCHECK, "b3hashr.o")
K32 = "blake3_servil_avx512_k32"
P16 = "blake3_servil_avx512_p16"
NAME = "b3l_wide32"
FUNCTIONS = [(OBJ, K32), (OBJ, P16), (OBJ, NAME)]
LAYOUT_KEYED = "layout keyed 40 { key: cv at 0, flags: byte at 32 }\n"

FOLLOW = "refused: the specification's words are not followed on the terms the function made"
WORD = "refused: a word of the run is not known to hold what the specification says"
STACK = "refused: a call needs more stack than this function's contract allows"
NEEDS = "refused: a called function needs of the processor what this function's contract does not say it needs"
FRAME = "refused: a called function's table of addresses, or the run it writes, is no part of this function's frame, or the two overlap"
LANE = "refused: a lane of a called function's table is not blocks this function may read, every word of them known"


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


def verify_with(spec, fns=FUNCTIONS, proof_text=None):
    with tempfile.TemporaryDirectory() as d:
        st = os.path.join(d, "s")
        pf = os.path.join(d, "p")
        lines = statement.statement(spec, fns)
        with open(st, "w") as f:
            f.write("\n".join(lines) + "\n")
        with open(pf, "w") as f:
            f.write(combined_proof() if proof_text is None else proof_text)
        r = subprocess.run([os.path.join(HERE, ".lake", "build", "bin", "odeverify"),
                            os.path.join(HERE, "..", "core", "x86.tab"), st, pf],
                           capture_output=True, text=True)
        return r.returncode == 0, (r.stdout + r.stderr).strip()


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Wide32(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.dir = tempfile.mkdtemp(prefix="odewide32-")
        with open(os.path.join(KCHECK, "hash.ode")) as f:
            cls.source = f.read()

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.dir)

    def test_shipped_b3l_wide32_is_shown(self):
        ok, out = verify_with(spec_text())
        self.assertTrue(ok, out)
        self.assertEqual(out, "shown")

    def test_stronger_contract_without_trace_depends_on_t_is_shown(self):
        """`b3l_wide32` never branches on `t` or computes addresses from `t`: its trace depends on nothing."""
        def drop_trace(s):
            old = "    ensures out = subtree(kf.key, kf.flags, t, input)\n    trace depends on t\n"
            self.assertEqual(s.count(old), 1)
            return s.replace(old, "    ensures out = subtree(kf.key, kf.flags, t, input)\n")
        ok, out = verify_with(spec_text(drop_trace))
        self.assertTrue(ok, out)
        self.assertEqual(out, "shown")

    def test_false_contracts_are_refused(self):
        cases = [
            ("chunk counter shifted by one",
             "ensures out = subtree(kf.key, kf.flags, t, input)",
             "ensures out = subtree(kf.key, kf.flags, t + 1, input)",
             FOLLOW),
            ("stack budget too small for calls",
             "    ensures out = subtree(kf.key, kf.flags, t, input)\n    trace depends on t\n    stack 8192",
             "    ensures out = subtree(kf.key, kf.flags, t, input)\n    trace depends on t\n    stack 4096",
             STACK),
            ("missing needs avx512",
             "    ensures out = subtree(kf.key, kf.flags, t, input)\n    trace depends on t\n    stack 8192\n    needs avx512\n",
             "    ensures out = subtree(kf.key, kf.flags, t, input)\n    trace depends on t\n    stack 8192\n",
             NEEDS),
            ("left_chunks changed to least power of two",
             "def left_chunks(bytes) { the greatest power of two k with 1024 * k < len(bytes) }",
             "def left_chunks(bytes) { the least power of two k with 1024 * k < len(bytes) }",
             FOLLOW),
        ]
        for what, old, new, why in cases:
            with self.subTest(what=what):
                base = spec_text()
                self.assertEqual(base.count(old), 1, what)
                ok, out = verify_with(base.replace(old, new, 1))
                self.assertFalse(ok, (what, out))
                self.assertIn(why, out, what)

    def test_false_sources_are_refused(self):
        cases = [
            ("final copy reads wrong frame offset",
             "  // copy 32 bytes: out <- a\n  lea rax, [rsp + 1280]\n",
             "  // copy 32 bytes: out <- a\n  lea rax, [rsp + 1312]\n",
             WORD),
            ("first parent call overwrites pointer table",
             "  lea r9, [rsp + 1280]\n  call blake3_servil_avx512_p16\n",
             "  lea r9, [rsp + 64]\n  call blake3_servil_avx512_p16\n",
             FRAME),
            ("first parent call overlaps its own input lanes",
             "  lea r9, [rsp + 1280]\n  call blake3_servil_avx512_p16\n",
             "  lea r9, [rsp + 128]\n  call blake3_servil_avx512_p16\n",
             LANE),
        ]
        for k, (what, old, new, why) in enumerate(cases):
            with self.subTest(what=what):
                self.assertGreaterEqual(self.source.count(old), 1, what)
                src = os.path.join(self.dir, f"bad{k}.ode")
                obj = os.path.join(self.dir, f"bad{k}.o")
                with open(src, "w") as f:
                    f.write(self.source.replace(old, new, 1))
                odec.build(src, "wide32", obj)
                ok, out = verify_with(spec_text(), [(OBJ, K32), (OBJ, P16), (obj, NAME)])
                self.assertFalse(ok, (what, out))
                self.assertIn(why, out, what)


if __name__ == "__main__":
    unittest.main()
