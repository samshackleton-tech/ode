#!/usr/bin/env pypy3
"""Verify P16's 16-lane transpose, seven compression rounds, aligned stack spills, and output packing.

    pypy3 test_p16_one.py        (skipped where Lean's `lake` is not installed)

This fixture takes P16's prologue, key broadcasts, 64-instruction input transpose, round loop with four
64-byte aligned stack spills and reloads, feed-forward XORs, output transpose, stores, and epilogue from
../wide/p16.ode, substituting 16 contiguous block loads and one fixed block per lane for the pointer array
and outer block loop. The contract requires `out` to hold the sixteen 8-word outputs of `compress` from
../kcheck/blake3.spec.
"""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
for folder in ("proof-core", "lang", "kcheck"):
    sys.path.insert(0, str(ROOT / folder))

import built
import kdecode
import lean_verify
import odec
import prove
import statement

NAME = "p16_one"
FOLLOW = "refused: the specification's words are not followed on the terms the function made"
HOLD = "refused: a word of the run is not known to hold what the specification says"


def part(text, start, stop):
    a, b = text.index(start), text.index(stop)
    assert a < b, (start, stop)
    return text[a:b]


def make_source():
    with (ROOT / "wide/p16.ode").open() as f:
        p16 = f.read()
    prefix = p16[:p16.index("  mov r12, rdi\n")].replace('fn p16 as "blake3_servil_avx512_p16"', f'fn {NAME} as "{NAME}"')
    key = part(p16, "  vpbroadcastd zmm0, DWORD PTR [r14 + 0]\n", "  xor r14d, r14d\n")
    transpose = part(p16, "  vpunpckldq zmm8, zmm16, zmm17\n", "  mov eax, r10d\n")
    iv = part(p16, "  vpbroadcastd zmm9, DWORD PTR [rip + #p16_iv + 0]\n", "  vpbroadcastd zmm13, r9d\n")
    rounds = part(p16, "  mov r11d, 7\n", "  mov r10d, r8d\n")
    tail = p16[p16.index("  vpunpckldq zmm16, zmm0, zmm1\n"):]
    loads = "".join(f"  vmovdqu32 zmm{i + 16}, zmmword ptr [rsi + {64 * i}]\n" for i in range(16))
    words = (
        "  vpxord zmm13, zmm13, zmm13\n"
        "  vpxord zmm14, zmm14, zmm14\n"
        "  mov edx, 64\n"
        "  vpbroadcastd zmm15, edx\n"
        "  mov eax, 4\n"
        "  vpbroadcastd zmm24, eax\n"
    )
    return prefix + "  mov r14, rdx\n  mov r15, rdi\n" + key + loads + transpose + iv + words + rounds + tail


def make_statement(rows, stack=367):
    lanes = [
        f"(call compress (call words (name key)) (call words (slice (name input) (num {64 * i}) (num {64 * (i + 1)}))) "
        f"(call counter (num 0)) (num 64) (num 4))"
        for i in range(16)
    ]
    expr = lanes[-1]
    for lane in reversed(lanes[:-1]):
        expr = f"(bin ++ {lane} {expr})"
    header = [
        f"fn {NAME}",
        "arg out out 512",
        "arg input fixed 1024",
        "arg key fixed 32",
        f"stack {stack}",
        "needs avx512",
        f"ensuresw out (call bytes_of {expr})",
    ]
    with (ROOT / "kcheck/blake3.spec").open() as f:
        defs = statement.definitions(f.read())
    return "\n".join(header + [f"i {a} {b} {text}" for a, b, text in rows] + defs) + "\n"


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class P16OneBlock(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.dir = Path(tempfile.mkdtemp(prefix="ode-p16-one-"))
        cls.source = make_source()
        cls.rows = cls.assemble(cls.source, "good")
        cls.statement = cls.dir / "good.statement"
        cls.proof = cls.dir / "good.proof"
        with cls.statement.open("w") as f:
            f.write(make_statement(cls.rows))
        prover = prove.Prover(str(cls.statement), [f"for {NAME}"], str(cls.proof))
        prover.last = ""
        try:
            items = prover.solve([])
            assert items is not None, prover.last
            cls.rounds = prover.runs
            cls.proof_lines = prover.lines + items
        finally:
            prover.close()
        with cls.proof.open("w") as f:
            f.write("\n".join(cls.proof_lines) + "\n")

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.dir)

    @classmethod
    def assemble(cls, text, tag):
        src = cls.dir / f"{tag}.ode"
        obj = cls.dir / f"{tag}.o"
        with src.open("w") as f:
            f.write(text)
        odec.build(str(src), NAME, str(obj))
        rows, _ = kdecode.read(str(obj), NAME, 0, 0)
        return rows

    def verify_files(self, st_path, pf_path):
        r = subprocess.run([lean_verify.EXE, lean_verify.TABLE, str(st_path), str(pf_path)], capture_output=True, text=True)
        self.assertEqual(r.returncode == 0, r.stdout == "shown\n", r.stdout[:200])
        return r.stdout

    def prove_rows(self, rows, tag, stack=367):
        st = self.dir / f"{tag}.statement"
        pf = self.dir / f"{tag}.proof"
        with st.open("w") as f:
            f.write(make_statement(rows, stack=stack))
        prover = prove.Prover(str(st), [f"for {NAME}"], str(pf))
        prover.last = ""
        try:
            got = prover.solve([])
            return got, prover.last
        finally:
            prover.close()

    def test_sixteen_lanes_shown_at_exact_stack_bound(self):
        # Six pushes (48 bytes), up to 63 bytes of 64-byte alignment, and 256 bytes of spill frame = 367 bytes.
        self.assertEqual(len(self.rows), 418)
        self.assertEqual(self.verify_files(self.statement, self.proof), "shown\n")
        self.assertLess(self.proof.stat().st_size, 1024)
        got, last = self.prove_rows(self.rows, "short_stack", stack=366)
        self.assertIsNone(got)
        self.assertIn("need entail", last.splitlines()[0])

    def test_wrong_code_is_refused(self):
        cases = [
            ("rotation count", "  vprord d0, d0, 16\n", "  vprord d0, d0, 15\n", FOLLOW),
            ("input transpose", "  vshufi32x4 zmm30, zmm31, zmm18, 0x88\n", "  vshufi32x4 zmm30, zmm31, zmm18, 0xdd\n", FOLLOW),
            ("spill reload slot", "  vmovdqa32 zmm16, ZMMWORD PTR [rsp + 64]\n", "  vmovdqa32 zmm16, ZMMWORD PTR [rsp + 0]\n", FOLLOW),     # (the other slot is known too: it holds another vector)
            ("output store offset", "  vmovdqu32 ZMMWORD PTR [r15 + 448], zmm4\n", "  vmovdqu32 ZMMWORD PTR [r15 + 384], zmm4\n", HOLD),
        ]
        for what, old, new, expected in cases:
            with self.subTest(what=what):
                self.assertEqual(self.source.count(old), 1)
                rows = self.assemble(self.source.replace(old, new), what.replace(" ", "_"))
                st = self.dir / f"{what.replace(' ', '_')}.statement"
                with st.open("w") as f:
                    f.write(make_statement(rows))
                self.assertNotEqual(self.verify_files(st, self.proof), "shown\n")
                got, last = self.prove_rows(rows, what.replace(" ", "_") + "_prove")
                self.assertIsNone(got, what)
                self.assertIn(expected, last.splitlines()[0])


if __name__ == "__main__":
    unittest.main()
