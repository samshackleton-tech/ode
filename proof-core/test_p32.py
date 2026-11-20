#!/usr/bin/env pypy3
"""Verify the shipped 32-way kernel for chunks of one block and of two.

    pypy3 test_p32.py        (skipped where Lean's `lake` is not installed)

The function is `blake3_servil_avx512_p32` as it lies in ../kcheck/b3hashr.o: 699 instructions. Its bytes are
not changed here. Its contract is examples/kernel/p32.contract, which is the contract of
../kcheck/proofs/inner.spec: thirty-two lanes, each a chunk of `n` blocks read through a table of addresses,
the same counter in every lane. (The hash calls the same code through its other entry,
`blake3_servil_avx512_k32`, which gives lane i the counter t + i: that entry runs six instructions on mask
registers, which the account of the machine does not have yet.)

The class `P32` narrows the contract by one line, `requires n < 2` (one block a lane) or `requires n < 3`
(one or two), and gives no place: the verifier follows each count of blocks as a path of its own. The
contract as it is, for every `n`, needs a place for the loop over the blocks; that is not here yet, and a
test says so.

What this kernel has that the 16-way kernel has not:

- It finds the order of the message words for each round in a table in its file's read-only data
  (`lea rdi, [rip + schedule]`, then four-byte loads). The statement gives the file's data, and the verifier
  takes each load as the number the file's bytes make (test_table.py has small functions that do this).
- It keeps the sixteen message words of each half as sixty-four-byte cells of its frame, and adds one of
  them to a register by `vpaddd zmm, zmm, [rsi + rax]`: an operation whose second operand is read from
  memory, at the frame's address plus the number read from the table. The account of the machine gives
  that form its meaning (Machine.lean, `lanesOf512`; test_machine.py compares it with conc.py), and the
  verifier takes the cell's words where the address is that of a cell a vector was stored to.

The controls change the contract, one instruction, or the file's data. Each is a statement that is false.
Each must be refused.
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

NAME = "blake3_servil_avx512_p32"
OBJ = str(ROOT / "kcheck/b3hashr.o")
FOLLOW = "refused: the specification's words are not followed on the terms the function made"
OTHER_WORD = "refused: a word of the run is not known to hold what the specification says"
NO_CELL = "refused: sixty-four bytes that are of no run of words given to read"
NOT_IN_DATA = "refused: the address of a place that is not in the file's read-only data"
PAST_DATA = "refused: a read of the file's read-only data that is not one, four or eight bytes within it"
AT_LEAST = "    requires n >= 1\n"
CALL = "chunk(key, t, flags, start, end, length, n, inputs[i])"
SCHEDULE = 0x4380                         # where the order of the message words lies in the file's data
# The contract's lines as statement.py writes them, but for the `data` and the `ensuresw` line.
LINES = [
    f"fn {NAME}",
    "arg inputs fixed 256",
    "lanes inputs n",
    "arg n number",
    "arg key fixed 32",
    "arg t number",
    "arg packed number",
    "arg out out 1024",
    "needs avx512",
    "atleast n 1",
    "below n 2",
    "hidden key",
    "stack 4096",
]


def spec_text(change=lambda t: t):
    with (ROOT / "kcheck/blake3.spec").open() as f:
        spec = f.read()
    with (HERE / "examples/kernel/p32.contract").open() as f:
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
        self.assertEqual([l for l in lines if l.split()[0] not in ("i", "def", "ensuresw", "data")], LINES)
        self.assertEqual(sum(l.startswith("i ") for l in lines), 699)
        self.assertEqual(sum(l.startswith("i ") and " .zpadddm " in l for l in lines), 32)
        self.assertEqual(sum(l.startswith("i ") and " .lea_data " in l for l in lines), 1)
        # the file's data: in this file one section holds the code and the constants, and the data is all of it
        (data,) = [l for l in lines if l.startswith("data ")]
        with open(OBJ, "rb") as f:
            whole = f.read()
        image = bytes.fromhex(data[5:])
        self.assertEqual(len(image), 17856)
        self.assertIn(image, whole)
        # the order of the message words for the seven rounds: places in the frame, 64 bytes a word
        schedule = [int.from_bytes(image[SCHEDULE + 4 * k:SCHEDULE + 4 * k + 4], "little") for k in range(16 * 7)]
        self.assertEqual(schedule[:16], [64 * k for k in range(16)])
        self.assertEqual(schedule[16:32], [64 * k for k in (2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8)])
        self.assertTrue(all(sorted(schedule[16 * r:16 * r + 16]) == [64 * k for k in range(16)] for r in range(7)))
        (ensures,) = [l for l in lines if l.startswith("ensuresw ")]
        self.assertEqual(ensures.count("(call chunk "), 32)
        self.assertIn("(index (name inputs) (num 31))", ensures)


class Files:
    """Statements and proofs in a folder of the test's own (`cls.dir`), the prover and the verifier on them."""

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

    def changed(self, old, new):
        """The good statement with one of its lines changed."""
        self.assertEqual(self.lines.count(old), 1, old)
        return [new if l == old else l for l in self.lines]


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class P32(Files, unittest.TestCase):
    """The contract narrowed to one block a lane, or to one or two: no place."""

    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.dir = Path(tempfile.mkdtemp(prefix="ode-p32-"))
        cls.lines = lines_of(below(2))
        cls.statement = cls.write("one", cls.lines)
        cls.proof = cls.dir / "one.proof"
        got, last = cls.prove_file(cls.statement, cls.proof)
        assert got, last

    def refused(self, tag, lines, expected, proof=None):
        """The statement is not shown with the good proof, the prover finds no proof of it, and it says why."""
        st = self.write(tag, lines)
        self.assertNotEqual(self.verify_files(st, proof or self.proof), "shown\n", tag)
        got, last = self.prove_file(st, self.dir / f"{tag}.proof", seconds=60)
        self.assertFalse(got, tag)
        self.assertIn(expected, last.splitlines()[0], tag)

    def test_one_block_a_lane_is_shown(self):
        self.assertEqual(self.verify_files(self.statement, self.proof), "shown\n")
        self.assertLess(self.proof.stat().st_size, 2048)
        # The same proof shows it with the least stack the kernel can do with: 48 bytes of saved registers,
        # up to 63 to reach a 64-byte boundary, and 2,368 below that.
        st = self.write("stack_2479", self.changed("stack 4096", "stack 2479"))
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

    def test_every_count_of_blocks_is_not_shown_without_a_place(self):
        # The contract as it is, for every n, and no place: the path goes round the loop without end.
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
            # what the other entry does: lane i with the counter t + i
            ("lane_counters", both(one, once(CALL, "chunk(key, t + i, flags, start, end, length, n, inputs[i])")), FOLLOW),
            ("two_blocks", both(one, once(CALL, "chunk(key, t, flags, start, end, length, 2, inputs[i])")), FOLLOW),
            # each lane with another lane's blocks: the lanes the other way round, and the two halves exchanged
            ("lanes_reversed", both(one, once(CALL, "chunk(key, t, flags, start, end, length, n, inputs[31 - i])")), OTHER_WORD),
            ("halves_exchanged", both(one, once(CALL, "chunk(key, t, flags, start, end, length, n, inputs[(i + 16) % 32])")), OTHER_WORD),
            # with no lower bound a lane may have no block: the read at offset 0 is not shown to lie within it
            ("no_lower_bound", once(AT_LEAST, "    requires n < 2\n"), "need entail"),
        ]
        for tag, change, why in cases:
            with self.subTest(what=tag):
                self.refused(tag, lines_of(change), why)
        with self.subTest(what="stack_2478"):
            self.refused("stack_2478", self.changed("stack 4096", "stack 2478"), "need entail")

    def test_a_changed_instruction_is_refused(self):
        add = "i 2304 2311 .zpadddm 0 0 .rsi .rax 0x0"         # the first message word added in a round: zmm0 += [rsi + rax]
        table = "i 2271 2278 .lea_data .rdi 0x4380"            # the address of the order of the message words
        cases = [
            # the first block's flags taken from the wrong bits of the register
            ("start_shift", "i 2095 2098 .shr32 .rdx 8", "i 2095 2098 .shr32 .rdx 9", FOLLOW),
            # the last block's flags left out
            ("no_end", "i 2128 2130 .or 32 (.reg .rax) (.reg .rcx)", "i 2128 2130 .nop", FOLLOW),
            # the counter's high half
            ("counter_high", "i 56 60 .shr64 .rcx 32", "i 56 60 .shr64 .rcx 31", FOLLOW),
            # the last block's length
            ("length_shift", "i 2132 2135 .shr32 .rdx 24", "i 2132 2135 .shr32 .rdx 16", FOLLOW),
            # the operand read from the frame: another message word (by the register with another number of
            # the table, and by the next cell); and sixty-four bytes that are half of one cell and half of the next
            ("another_word", add, "i 2304 2311 .zpadddm 0 0 .rsi .rcx 0x0", FOLLOW),
            ("next_cell", add, "i 2304 2311 .zpadddm 0 0 .rsi .rax 0x40", FOLLOW),
            ("half_a_cell", add, "i 2304 2311 .zpadddm 0 0 .rsi .rax 0x20", NO_CELL),
            # the table: read four bytes on (the next number of it); taken four bytes on (the last round then
            # reads a number past the table, which is no place of a cell); taken at the end of the file's data,
            # and so near the end that a load ends past it
            ("table_read_4_on", "i 2292 2294 .mov 32 (.reg .rax) (.mem .rdi 0x0)", "i 2292 2294 .mov 32 (.reg .rax) (.mem .rdi 0x4)", FOLLOW),
            ("table_4_on", table, "i 2271 2278 .lea_data .rdi 0x4384", NO_CELL),
            ("table_at_the_end", table, "i 2271 2278 .lea_data .rdi 0x45C0", NOT_IN_DATA),
            ("table_near_the_end", table, "i 2271 2278 .lea_data .rdi 0x45A0", PAST_DATA),
        ]
        for tag, old, new, why in cases:
            with self.subTest(what=tag):
                self.refused(tag, self.changed(old, new), why)

    def test_changed_data_is_refused(self):
        """The statement's `data` line is the file's. With the first number of the table changed (the first
        message word of the first round taken from the next cell) the function computes another hash; and
        without the line the table's address is refused."""
        k = next(i for i, l in enumerate(self.lines) if l.startswith("data "))
        at = 5 + 2 * SCHEDULE
        self.assertEqual(self.lines[k][at:at + 8], "00000000")
        other = self.lines[k][:at] + "40" + self.lines[k][at + 2:]
        self.refused("data_changed", self.lines[:k] + [other] + self.lines[k + 1:], FOLLOW)
        self.refused("no_data", self.lines[:k] + self.lines[k + 1:], NOT_IN_DATA)


if __name__ == "__main__":
    unittest.main()
