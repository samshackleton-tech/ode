#!/usr/bin/env pypy3
"""Verify P16's sixteen block loads through its table of input addresses.

    pypy3 test_p16_table.py        (skipped where Lean's `lake` is not installed)

P16 is given the address of a table of sixteen addresses. Each address points to one lane's blocks. This
fixture takes P16's instructions from ../wide/p16.ode as test_p16_one.py does, and also keeps P16's sixteen
pairs `mov rax, [r12 + 8 * i]` and `vmovdqu32 zmm, [rax + r14]`. It leaves out the loop over blocks: every
lane's block is read at offset 0. The contract says that the table holds sixteen addresses of `n` blocks
each, that `n` is at least 1, and that `out` holds `compress` of each lane's first block.

The controls change the contract or the source one thing at a time. Each must be refused.
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
from test_p16_one import part

NAME = "p16_table"
FOLLOW = "refused: the specification's words are not followed on the terms the function made"


def make_source():
    with (ROOT / "wide/p16.ode").open() as f:
        p16 = f.read()
    prefix = p16[:p16.index("  mov r12, rdi\n")].replace('fn p16 as "blake3_servil_avx512_p16"', f'fn {NAME} as "{NAME}"')
    key = part(p16, "  vpbroadcastd zmm0, DWORD PTR [r14 + 0]\n", "  xor r14d, r14d\n")
    loads = part(p16, "  mov rax, QWORD PTR [r12 + 0]\n", "  vpunpckldq zmm8, zmm16, zmm17\n")
    transpose = part(p16, "  vpunpckldq zmm8, zmm16, zmm17\n", "  mov eax, r10d\n")
    iv = part(p16, "  vpbroadcastd zmm9, DWORD PTR [rip + #p16_iv + 0]\n", "  vpbroadcastd zmm13, r9d\n")
    rounds = part(p16, "  mov r11d, 7\n", "  mov r10d, r8d\n")
    tail = p16[p16.index("  vpunpckldq zmm16, zmm0, zmm1\n"):]
    words = (
        "  vpxord zmm13, zmm13, zmm13\n"
        "  vpxord zmm14, zmm14, zmm14\n"
        "  mov edx, 64\n"
        "  vpbroadcastd zmm15, edx\n"
        "  mov eax, 4\n"
        "  vpbroadcastd zmm24, eax\n"
    )
    # out in rdi, the table in rsi, the key in rdx, the count of blocks in rcx
    moves = "  mov r14, rdx\n  mov r15, rdi\n  mov r12, rsi\n"
    return prefix + moves + key + "  xor r14d, r14d\n" + loads + transpose + iv + words + rounds + tail


def make_statement(rows, stack=367, block=0, at_least=1, table="arg inputs fixed 128", lanes="lanes inputs n"):
    each = [
        f"(call compress (call words (name key)) (index (index (name inputs) (num {i})) (num {block})) "
        f"(call counter (num 0)) (num 64) (num 4))"
        for i in range(16)
    ]
    expr = each[-1]
    for lane in reversed(each[:-1]):
        expr = f"(bin ++ {lane} {expr})"
    header = [f"fn {NAME}", "arg out out 512", table, "arg key fixed 32", "arg n number"]
    header += [lanes] if lanes else []
    header += [f"atleast n {at_least}"] if at_least else []
    header += [f"stack {stack}", "needs avx512", f"ensuresw out (call bytes_of {expr})"]
    with (ROOT / "kcheck/blake3.spec").open() as f:
        defs = statement.definitions(f.read())
    return "\n".join(header + [f"i {a} {b} {text}" for a, b, text in rows] + defs) + "\n"


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class P16Table(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.dir = Path(tempfile.mkdtemp(prefix="ode-p16-table-"))
        cls.source = make_source()
        cls.rows = cls.assemble(cls.source, "good")
        cls.statement = cls.dir / "good.statement"
        cls.proof = cls.dir / "good.proof"
        with cls.statement.open("w") as f:
            f.write(make_statement(cls.rows))
        got, last = cls.prove_file(cls.statement, cls.proof)
        assert got, last

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

    @classmethod
    def prove_file(cls, st, pf):
        """(a proof was found and written to `pf`, the verifier's last word where none was)."""
        prover = prove.Prover(str(st), [f"for {NAME}"], str(pf))
        prover.last = ""
        try:
            items = prover.solve([])
            if items is None:
                return False, prover.last
            with pf.open("w") as f:
                f.write("\n".join(prover.lines + items) + "\n")
            return True, ""
        finally:
            prover.close()

    def verify_files(self, st, pf):
        r = subprocess.run([lean_verify.EXE, lean_verify.TABLE, str(st), str(pf)], capture_output=True, text=True)
        self.assertEqual(r.returncode == 0, r.stdout == "shown\n", r.stdout[:200])
        return r.stdout

    def refused(self, tag, text, expected):
        """The statement is not shown with the good proof, the prover finds no proof of it, and it says why."""
        st = self.dir / f"{tag}.statement"
        with st.open("w") as f:
            f.write(text)
        self.assertNotEqual(self.verify_files(st, self.proof), "shown\n", tag)
        got, last = self.prove_file(st, self.dir / f"{tag}.proof")
        self.assertFalse(got, tag)
        self.assertIn(expected, last.splitlines()[0], tag)

    def changed(self, old, new):
        self.assertEqual(self.source.count(old), 1, old)
        return self.source.replace(old, new)

    def test_sixteen_lanes_read_through_the_table(self):
        self.assertEqual(len(self.rows), 437)
        self.assertEqual(self.verify_files(self.statement, self.proof), "shown\n")
        self.assertLess(self.proof.stat().st_size, 4096)

    def test_a_changed_contract_is_refused(self):
        rows = self.rows
        # With no lower bound, a lane may have no block: the read at offset 0 is not shown to lie within it.
        self.refused("no_lower_bound", make_statement(rows, at_least=0), "need entail")
        # The function read each lane's block 0; the contract speaks of block 1.
        self.refused("block_1", make_statement(rows, block=1), FOLLOW)
        # The run is not said to be a table: nothing is known of where its addresses point.
        self.refused("no_table", make_statement(rows, lanes=""), "sixty-four bytes that are of no run of words given to read")
        # A table of fifteen addresses: the sixteenth is outside it.
        self.refused("short_table", make_statement(rows, table="arg inputs fixed 120"), "not eight bytes within it")

    def test_changed_code_is_refused(self):
        # Lane 1 reads lane 0's block.
        rows = self.assemble(self.changed("  mov rax, QWORD PTR [r12 + 8]\n", "  mov rax, QWORD PTR [r12 + 0]\n"), "lane")
        self.refused("lane", make_statement(rows), FOLLOW)
        # An address taken from the middle of two of the table's addresses.
        rows = self.assemble(self.changed("  mov rax, QWORD PTR [r12 + 8]\n", "  mov rax, QWORD PTR [r12 + 4]\n"), "place")
        self.refused("place", make_statement(rows), "a read through an address that is not one of a table's")
        # A read 64 bytes before a lane's blocks.
        rows = self.assemble(self.changed("  xor r14d, r14d\n", "  mov r14, -64\n"), "before")
        self.refused("before", make_statement(rows), "need entail")

    def test_the_second_block_needs_two_blocks(self):
        rows = self.assemble(self.changed("  xor r14d, r14d\n", "  mov r14d, 64\n"), "second")
        # With one block a lane, the read at offset 64 is outside the lane.
        self.refused("second_of_one", make_statement(rows), "need entail")
        # With two blocks a lane it is block 1, and no other.
        self.refused("second_as_first", make_statement(rows, at_least=2), FOLLOW)
        st = self.dir / "second.statement"
        pf = self.dir / "second.proof"
        with st.open("w") as f:
            f.write(make_statement(rows, at_least=2, block=1))
        got, last = self.prove_file(st, pf)
        self.assertTrue(got, last)
        self.assertEqual(self.verify_files(st, pf), "shown\n")


if __name__ == "__main__":
    unittest.main()
