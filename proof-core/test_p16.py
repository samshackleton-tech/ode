#!/usr/bin/env pypy3
"""Verify the shipped 16-way kernel, for chunks of one block and of two.

    pypy3 test_p16.py        (skipped where Lean's `lake` is not installed)

The function is `blake3_servil_avx512_p16` as it lies in ../kcheck/b3hashr.o: 460 instructions. Its bytes
are not changed here. Its contract is examples/kernel/p16.contract, which is the contract of
../kcheck/proofs/inner.spec but for the `trace` line: sixteen lanes, each a chunk of `n` blocks read through
a table of addresses, the same counter in every lane, and four bytes of one register that give the flags,
the flags of the first and of the last block, and the last block's length.

The kernel loops over the blocks. The verifier does not have a loop invariant for vector registers yet. So
the contract is narrowed here by one line, `requires n < 2` (one block a lane) or `requires n < 3` (one or
two). The verifier then follows each count of blocks as a path of its own. With one block the jump back to
the loop's head is never taken; with two it is taken once. The contract for every `n` is refused for now,
and a test records that.

What the one-block case exercises beyond test_p16_table.py: the kinds `16 inputs`, `bytes a b c d` and
`16 cvs` of the contract language, the four bytes taken out of the register by shifts and masks, the two
ORs that make the first and last block's flags, the counter's two halves, the block length, and the choice
between a last block and any other. With two blocks it also exercises the chaining value carried from the
first block to the second, and the read of each lane's second block.

The controls change the contract or one instruction. Each must be refused.
"""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
import unittest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
for folder in ("proof-core", "kcheck"):
    sys.path.insert(0, str(ROOT / folder))

import built
import lean_verify
import prove
import statement

NAME = "blake3_servil_avx512_p16"
OBJ = str(ROOT / "kcheck/b3hashr.o")
FOLLOW = "refused: the specification's words are not followed on the terms the function made"
OTHER_WORD = "refused: a word of the run is not known to hold what the specification says"
AT_LEAST = "    requires n >= 1\n"
CALL = "chunk(key, t, flags, start, end, length, n, inputs[i])"
# The contract's lines as statement.py writes them, but for the `ensuresw` line.
LINES = [
    f"fn {NAME}",
    "arg inputs fixed 128",
    "lanes inputs n",
    "arg n number",
    "arg key fixed 32",
    "arg t number",
    "arg packed number",
    "arg out out 512",
    "needs avx512",
    "atleast n 1",
    "below n 2",
    "stack 4096",
]


def spec_text(change=lambda t: t):
    with (ROOT / "kcheck/blake3.spec").open() as f:
        spec = f.read()
    with (HERE / "examples/kernel/p16.contract").open() as f:
        text = f.read()
    return change(spec + "\n" + text)


def once(old, new):
    def change(text):
        assert text.count(old) == 1, (old, text.count(old))
        return text.replace(old, new)
    return change


def both(*changes):
    def change(text):
        for c in changes:
            text = c(text)
        return text
    return change


def below(k):
    """The contract narrowed: fewer than `k` blocks a lane."""
    return once(AT_LEAST, AT_LEAST + f"    requires n < {k}\n")


def lines_of(change):
    return statement.statement(spec_text(change), [(OBJ, NAME)])


class Statement(unittest.TestCase):
    """The contract as statement.py writes it for the verifier in Lean."""

    def test_the_contract_in_the_accounts_terms(self):
        lines = lines_of(below(2))
        self.assertEqual([l for l in lines if l.split()[0] not in ("i", "def", "ensuresw")], LINES)
        self.assertEqual(sum(l.startswith("i ") for l in lines), 460)
        (ensures,) = [l for l in lines if l.startswith("ensuresw ")]
        low = "(bin % (name packed) (num 4294967296))"
        lane = lambda i: (
            "(call chunk (call words (name key)) (call counter (name t)) "
            "(bin % (name packed) (num 256)) "
            f"(bin % (bin / {low} (num 256)) (num 256)) "
            f"(bin % (bin / {low} (num 65536)) (num 256)) "
            f"(bin / {low} (num 16777216)) "
            f"(name n) (index (name inputs) (num {i})))"
        )
        expr = lane(15)
        for i in reversed(range(15)):
            expr = f"(bin ++ {lane(i)} {expr})"
        self.assertEqual(ensures, f"ensuresw out (call bytes_of {expr})")

    def test_what_is_not_read_is_refused(self):
        cases = [
            ("three bytes named", once("bytes flags start end length", "bytes flags start end"), "names its bytes twice, or not four of them"),
            ("a byte's name is an argument's", once("bytes flags start end length", "bytes flags start end key"), "gives the name key twice"),
            ("the register's whole number", once(CALL, "chunk(key, t, packed, start, end, length, n, inputs[i])"), "only four bytes are named"),
            ("the count of blocks is no number", once("16 inputs, n: number", "16 inputs, n: counter"), "no number n of their blocks"),
            ("some of the values", once("inputs[i]) for i in 0..16", "inputs[i]) for i in 0..8"), "not of all of them"),
            ("the values from 1 on", once("inputs[i]) for i in 0..16", "inputs[i]) for i in 1..16"), "not of all of them"),
            ("a bound that is no number", once(AT_LEAST, "    requires n >= t\n"), "has a `requires` the verifier in Lean does not read yet"),
            ("a bound of a run", once(AT_LEAST, "    requires key >= 1\n"), "has a `requires` the verifier in Lean does not read yet"),
            ("the trace depends on no byte of the blocks", once("trace depends on inputs, key", "trace depends on key"), "the trace does not depend on the bytes of inputs"),
            ("no line of what overlaps", once("    requires no_overlap(inputs, key, out)\n", ""), "does not say `requires no_overlap(inputs, key, out)`"),
        ]
        for what, change, why in cases:
            with self.subTest(what=what):
                with self.assertRaises(SystemExit) as e:
                    lines_of(change)
                self.assertIn(why, str(e.exception))


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class P16(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.dir = Path(tempfile.mkdtemp(prefix="ode-p16-"))
        cls.lines = lines_of(below(2))
        cls.statement = cls.write("one", cls.lines)
        cls.proof = cls.dir / "one.proof"
        got, last = cls.prove_file(cls.statement, cls.proof)
        assert got, last

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.dir)

    @classmethod
    def write(cls, tag, lines):
        st = cls.dir / f"{tag}.statement"
        with st.open("w") as f:
            f.write("\n".join(lines) + "\n")
        return st

    @classmethod
    def prove_file(cls, st, pf, seconds=None):
        """(a proof was found and written to `pf`, the verifier's last word where none was). With `seconds`,
        the search gives up after that time."""
        prover = prove.Prover(str(st), [f"for {NAME}"], str(pf), until=None if seconds is None else time.time() + seconds)
        prover.last = ""
        try:
            try:
                items = prover.solve([])
            except prove.GaveUp:
                return False, "gave up"
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

    def refused(self, tag, lines, expected, proof=None):
        """The statement is not shown with the good proof, the prover finds no proof of it, and it says why."""
        st = self.write(tag, lines)
        self.assertNotEqual(self.verify_files(st, proof or self.proof), "shown\n", tag)
        got, last = self.prove_file(st, self.dir / f"{tag}.proof")
        self.assertFalse(got, tag)
        self.assertIn(expected, last.splitlines()[0], tag)

    def changed(self, old, new):
        """The good statement with one of its lines changed."""
        self.assertEqual(self.lines.count(old), 1, old)
        return [new if l == old else l for l in self.lines]

    def test_one_block_a_lane_is_shown(self):
        self.assertEqual(self.verify_files(self.statement, self.proof), "shown\n")
        self.assertLess(self.proof.stat().st_size, 2048)
        # The same proof shows it with the least stack the kernel can do with: 48 bytes of saved registers,
        # up to 63 to reach a 64-byte boundary, and 256 below that.
        st = self.write("stack_367", self.changed("stack 4096", "stack 367"))
        self.assertEqual(self.verify_files(st, self.proof), "shown\n")

    def test_two_blocks_a_lane_are_shown(self):
        st, pf = self.write("two", lines_of(below(3))), self.dir / "two.proof"
        got, last = self.prove_file(st, pf)
        self.assertTrue(got, last)
        self.assertEqual(self.verify_files(st, pf), "shown\n")
        self.assertLess(pf.stat().st_size, 4096)
        # The proof for one block does not show it: it says that no input takes the jump back.
        self.assertIn("refused: a proof of arithmetic does not show", self.verify_files(st, self.proof))
        # With exactly two blocks the first block's flags and the last block's go to different blocks:
        # exchanged in the contract, they are refused.
        two = once(AT_LEAST, "    requires n >= 2\n    requires n < 3\n")
        self.refused("two_first_last", lines_of(both(two, once(CALL, "chunk(key, t, flags, end, start, length, n, inputs[i])"))), FOLLOW, proof=pf)

    def test_every_count_of_blocks_is_not_shown_yet(self):
        # The contract as it is, for every n: the path goes round the loop without end. (This is to change
        # when the verifier has a loop invariant for vector registers.)
        st = self.write("every", lines_of(lambda t: t))
        self.assertNotEqual(self.verify_files(st, self.proof), "shown\n")
        got, last = self.prove_file(st, self.dir / "every.proof", seconds=12)
        self.assertFalse(got)

    def test_a_changed_contract_is_refused(self):
        one = below(2)
        cases = [
            # the last block's flags and its length, exchanged where the contract uses them
            ("end_length", both(one, once(CALL, "chunk(key, t, flags, start, length, end, n, inputs[i])")), FOLLOW),
            # and where the register's bytes are named
            ("bytes_named", both(one, once("bytes flags start end length", "bytes flags start length end")), FOLLOW),
            # the last block's flags left out
            ("no_end", both(one, once(CALL, "chunk(key, t, flags, start, 0, length, n, inputs[i])")), FOLLOW),
            ("length_64", both(one, once(CALL, "chunk(key, t, flags, start, end, 64, n, inputs[i])")), FOLLOW),
            ("next_counter", both(one, once(CALL, "chunk(key, t + 1, flags, start, end, length, n, inputs[i])")), FOLLOW),
            ("two_blocks", both(one, once(CALL, "chunk(key, t, flags, start, end, length, 2, inputs[i])")), FOLLOW),
            ("lanes_reversed", both(one, once(CALL, "chunk(key, t, flags, start, end, length, n, inputs[15 - i])")), OTHER_WORD),
            # with no lower bound a lane may have no block: the read at offset 0 is not shown to lie within it
            ("no_lower_bound", once(AT_LEAST, "    requires n < 2\n"), "need entail"),
        ]
        for tag, change, why in cases:
            with self.subTest(what=tag):
                self.refused(tag, lines_of(change), why)
        with self.subTest(what="stack_366"):
            self.refused("stack_366", self.changed("stack 4096", "stack 366"), "need entail")

    def test_a_changed_instruction_is_refused(self):
        cases = [
            # the first block's flags taken from the wrong bits of the register
            ("start_shift", "i 115 119 .shr32 .r10 8", "i 115 119 .shr32 .r10 9", FOLLOW),
            # the last block's flags left out
            ("no_end", "i 766 768 .or 32 (.reg .rax) (.reg .rdi)", "i 766 768 .nop", FOLLOW),
            # the counter's high half
            ("counter_high", "i 819 823 .shr64 .rcx 32", "i 819 823 .shr64 .rcx 31", FOLLOW),
            # the last block's length
            ("length_shift", "i 142 145 .shr32 .rsi 24", "i 142 145 .shr32 .rsi 16", FOLLOW),
        ]
        for tag, old, new, why in cases:
            with self.subTest(what=tag):
                self.refused(tag, self.changed(old, new), why)


if __name__ == "__main__":
    unittest.main()
