#!/usr/bin/env pypy3
"""Verify the shipped 32-way kernel: for chunks of one block and of two, and for every count of blocks.

    pypy3 test_p32.py        (skipped where Lean's `lake` is not installed)

The function is `blake3_servil_avx512_p32` as it lies in ../kcheck/b3hashr.o: 699 instructions. Its bytes are
not changed here. Its contract is examples/kernel/p32.contract, which is the contract of
../kcheck/proofs/inner.spec: thirty-two lanes, each a chunk of `n` blocks read through a table of addresses,
the same counter in every lane. (The hash calls the same code through its other entry,
`blake3_servil_avx512_k32`, which gives lane i the counter t + i: test_k32.py.)

The class `P32` narrows the contract by one line, `requires n < 2` (one block a lane) or `requires n < 3`
(one or two), and gives no place: the verifier follows each count of blocks as a path of its own.

The class `Loop` takes the contract as it is, for every `n`, with a place (a loop invariant) for the loop
over the blocks: examples/kernel/p32.places. The place says what the vector registers hold after the blocks
done, as the 16-way kernel's place does, for both halves of the lanes. And it says two things that kernel's
place has no need of:

- What four cells of the frame hold. This kernel stores the counter's low and high words there before the
  loop and reads them back in every turn. A line `cell [rsp + 2048]: word i = lo(t)` says what each of the
  sixteen words of such a cell is; the verifier shows it of the state that comes to the place and takes it
  as known of every later turn.
- Two facts that name the last block's flags and its length (`fact end <= 255`). This kernel works both out
  only where the block is the last; what the lanes are said to hold names them on every path. The verifier
  works a number out where a fact names it. Without the two facts the place is still true and is refused: a
  limit of the verifier, kept as a test.

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
AT_PLACE = "refused: at the place 3908 the vector registers are not shown to hold what the place says"
AT_CELL = "refused: at the place 3908 a cell of the frame is not shown to hold what the place says"
NO_LANES = "refused: a 512-bit register whose lanes are not all known"
NO_SAVED = "refused: the aligned load does not match a saved stack vector"
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
    """Statements and proofs in a folder of the test's own (`cls.dir`), the prover and the verifier on them.
    `name`: the function they are of."""
    name = NAME

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
    def prove_file(cls, st, pf, seconds=None, place=()):
        """(a proof was found and written to `pf`, the verifier's last word where none was). With `seconds`,
        the search gives up after that time. `place`: the lines of the function's places."""
        prover = prove.Prover(str(st), [f"for {cls.name}"] + list(place), str(pf), until=None if seconds is None else time.time() + seconds)
        prover.last = ""
        try:
            try:
                items = prover.solve([])
            except prove.GaveUp:
                return False, "gave up"
            except prove.Unkept as e:
                return False, f"a kept register does not hold what it held: {e.args}"
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


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Loop(Files, unittest.TestCase):
    """The contract as it is: every count of blocks, by the place at the loop's bottom."""

    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.dir = Path(tempfile.mkdtemp(prefix="ode-p32-loop-"))
        with (HERE / "examples/kernel/p32.places").open() as f:
            cls.places = f.read()
        cls.statement, cls.proof = cls.dir / "every.statement", cls.dir / "every.proof"
        cls.runs, cls.found = prove.prove(spec_text(), [(OBJ, NAME, cls.places)], str(cls.statement), str(cls.proof))[NAME]
        with cls.statement.open() as f:
            cls.lines = f.read().split("\n")[:-1]
        with cls.proof.open() as f:
            proof = f.read().split("\n")[:-1]
        # the place as the verifier reads it (with the registers the prover found it keeps), then what was found
        cls.place = [l for l in proof if l.split()[0] in ("place", "name", "fact", "keep", "decreases", "lane", "cell")]
        cls.items = [l for l in proof if l.split()[0] in ("t", "p", "s", "q")]
        assert proof == [f"for {NAME}"] + cls.place + cls.items, "the proof's lines are not: for, the place, what was found"

    def refused(self, tag, lines, expected, place=None):
        """With these lines for the statement and these for the place: what was found for the good ones does
        not show it, the prover finds no proof of it, and it says why."""
        place = self.place if place is None else place
        st = self.write(tag, lines)
        with (self.dir / f"{tag}.good.proof").open("w") as f:
            f.write("\n".join([f"for {NAME}"] + place + self.items) + "\n")
        self.assertNotEqual(self.verify_files(st, self.dir / f"{tag}.good.proof"), "shown\n", tag)
        got, last = self.prove_file(st, self.dir / f"{tag}.proof", seconds=60, place=place)
        self.assertFalse(got, tag)
        self.assertIn(expected, last.splitlines()[0], tag)

    def with_place(self, old, new):
        out = [l.replace(old, new) for l in self.place]
        self.assertNotEqual(out, self.place, old)
        return out

    def without(self, start):
        out = [l for l in self.place if not l.startswith(start)]
        self.assertEqual(len(out), len(self.place) - 1, start)
        return out

    def test_every_count_of_blocks_is_shown(self):
        self.assertEqual(self.verify_files(self.statement, self.proof), "shown\n")
        # the kept proof is what the prover finds, and shows it from the files
        kept = HERE / "proofs" / f"{NAME}.proof"
        self.assertEqual(lean_verify.verify(spec_text(), [(OBJ, NAME)], str(kept)), (True, "shown"))
        with kept.open() as f, self.proof.open() as g:
            self.assertEqual(f.read(), g.read())
        self.assertEqual(sum(l.startswith("i ") for l in self.lines), 699)
        self.assertEqual([l for l in self.lines if l.split()[0] in ("atleast", "below")], ["atleast n 1"])
        self.assertLess(self.proof.stat().st_size, 8192)
        # the place as the prover writes it for the verifier
        low = "(bin % (name packed) (num 4294967296))"
        end = f"(bin % (bin / {low} (num 65536)) (num 256))"
        length = f"(bin / {low} (num 16777216))"
        self.assertEqual(self.place[:10], [
            "place 3908", "name left r13", "name off r14",
            "fact (bin >= (name left) (num 1))", "fact (bin <= (name left) (name n))",
            "fact (bin == (name off) (bin * (num 64) (bin - (name n) (name left))))",
            f"fact (bin <= {end} (num 255))", f"fact (bin <= {length} (num 255))",
            "keep rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r15",
            "decreases (name left)"])
        chunk = ("(call chunk.h (call words (name key)) (call counter (name t)) (bin % (name packed) (num 256)) "
                 f"(bin % (bin / {low} (num 256)) (num 256)) {end} {length} (name n) ")
        done = "(bin + (bin - (name n) (name left)) (num 1)))"
        self.assertEqual(self.place[10:], [
            f"lane i zmm0 zmm1 zmm2 zmm3 zmm4 zmm5 zmm6 zmm7 = {chunk}(index (name inputs) (name i)) {done}",
            f"lane i zmm8 zmm9 zmm10 zmm11 zmm12 zmm13 zmm14 zmm15 = {chunk}(index (name inputs) (bin + (name i) (num 16))) {done}",
            "cell 2048 i (call lo (call counter (name t)))", "cell 2112 i (call hi (call counter (name t)))",
            "cell 2176 i (call lo (call counter (name t)))", "cell 2240 i (call hi (call counter (name t)))"])
        # The same proof shows it with the least stack the kernel can do with.
        st = self.write("stack_2479", self.changed("stack 4096", "stack 2479"))
        self.assertEqual(self.verify_files(st, self.proof), "shown\n")

    def test_the_trace(self):
        """The key's bytes are marked (`hidden key`): shown, since the kernel only loads them into vector
        registers. With the table of addresses marked too it is refused: the addresses the blocks are read at
        would depend on something marked."""
        self.assertIn("hidden key", self.lines)
        self.assertNotIn("hidden inputs", self.lines)
        k = self.lines.index("hidden key")
        self.refused("hidden-table", self.lines[:k] + ["hidden inputs"] + self.lines[k:], "refused: an address is made of something that may depend on a secret")

    def test_a_changed_contract_is_refused(self):
        cases = [
            # the first block's flags and the last block's, exchanged (false where there are two blocks or more)
            ("first_last", once(CALL, "chunk(key, t, flags, end, start, length, n, inputs[i])"), FOLLOW),
            ("end_length", once(CALL, "chunk(key, t, flags, start, length, end, n, inputs[i])"), FOLLOW),
            ("no_end", once(CALL, "chunk(key, t, flags, start, 0, length, n, inputs[i])"), FOLLOW),
            ("length_64", once(CALL, "chunk(key, t, flags, start, end, 64, n, inputs[i])"), FOLLOW),
            ("next_counter", once(CALL, "chunk(key, t + 1, flags, start, end, length, n, inputs[i])"), FOLLOW),
            # what the other entry does: lane i with the counter t + i
            ("lane_counters", once(CALL, "chunk(key, t + i, flags, start, end, length, n, inputs[i])"), FOLLOW),
            # one block fewer than the function compresses, and two blocks whatever n is
            ("one_block_fewer", once(CALL, "chunk(key, t, flags, start, end, length, n - 1, inputs[i])"), OTHER_WORD),
            ("two_blocks", once(CALL, "chunk(key, t, flags, start, end, length, 2, inputs[i])"), FOLLOW),
            # each lane with another lane's blocks: the lanes the other way round, and the two halves exchanged
            ("lanes_reversed", once(CALL, "chunk(key, t, flags, start, end, length, n, inputs[31 - i])"), OTHER_WORD),
            ("halves_exchanged", once(CALL, "chunk(key, t, flags, start, end, length, n, inputs[(i + 16) % 32])"), OTHER_WORD),
            # with no lower bound a lane may have no block: the read at offset 0 is not shown to lie within it
            ("no_lower_bound", once(AT_LEAST, ""), "need entail"),
        ]
        for tag, change, why in cases:
            with self.subTest(what=tag):
                self.refused(tag, lines_of(change), why)
        with self.subTest(what="stack_2478"):
            self.refused("stack_2478", self.changed("stack 4096", "stack 2478"), "need entail")

    def test_a_changed_instruction_is_refused(self):
        cases = [
            # the next block is read two blocks on
            ("two_blocks_on", "i 3908 3912 .add 64 (.reg .r14) (.imm 0x40)", "i 3908 3912 .add 64 (.reg .r14) (.imm 0x80)", "need entail"),
            # the last block's flags left out; its length and the first block's flags from the wrong bits
            ("no_end", "i 2128 2130 .or 32 (.reg .rax) (.reg .rcx)", "i 2128 2130 .nop", AT_PLACE),
            ("length_shift", "i 2132 2135 .shr32 .rdx 24", "i 2132 2135 .shr32 .rdx 16", AT_PLACE),
            ("start_shift", "i 2095 2098 .shr32 .rdx 8", "i 2095 2098 .shr32 .rdx 9", AT_PLACE),
            # the counter's high half, which goes to two cells of the frame before the loop
            ("counter_high", "i 56 60 .shr64 .rcx 32", "i 56 60 .shr64 .rcx 31", AT_PLACE),
            # in the loop: the counter's low words read from the cell of its high words
            ("cell_of_the_high_words", "i 2175 2183 .zload true 20 .rsp 0x800", "i 2175 2183 .zload true 20 .rsp 0x840", AT_PLACE),
            # in the loop: a message word stored over the cell of the counter's low words
            ("cell_written_over", "i 2042 2049 .zstore true .rsi 0x6C0 19", "i 2042 2049 .zstore true .rsi 0x800 19", NO_CELL),
        ]
        for tag, old, new, why in cases:
            with self.subTest(what=tag):
                self.refused(tag, self.changed(old, new), why)

    def test_a_changed_place_is_refused(self):
        done = "(bin + (bin - (name n) (name left)) (num 1)))"
        low_half, high_half = "(index (name inputs) (name i))", "(index (name inputs) (bin + (name i) (num 16)))"
        exchanged = [l.replace(low_half, "@").replace(high_half, low_half).replace("@", high_half) for l in self.place]
        self.assertNotEqual(exchanged, self.place)
        cases = [
            # a cell said to hold the counter's low words where it holds the high ones; a cell four bytes on
            ("cell_low_for_high", self.with_place("cell 2112 i (call hi ", "cell 2112 i (call lo "), AT_CELL),
            ("cell_four_bytes_on", self.with_place("cell 2048 i ", "cell 2052 i "), AT_CELL),
            # a cell said to hold in word i the low word of the counter t + i (what the other entry stores there)
            ("cell_lane_counters", self.with_place("cell 2048 i (call lo (call counter (name t)))", "cell 2048 i (call lo (call counter (bin + (name t) (name i))))"), AT_CELL),
            # the chaining value after one block fewer, or one more, than are done
            ("one_block_behind", self.with_place(done, "(bin - (name n) (name left)))"), AT_PLACE),
            ("one_block_ahead", self.with_place(done, "(bin + (bin - (name n) (name left)) (num 2)))"), AT_PLACE),
            # the two halves of the lanes exchanged; two registers exchanged
            ("halves_exchanged", exchanged, AT_PLACE),
            ("registers_exchanged", self.with_place("zmm8 zmm9 ", "zmm9 zmm8 "), AT_PLACE),
            # something false of how far the code has read; a number that does not decrease
            ("offset_ahead", self.with_place("(bin * (num 64) (bin - (name n) (name left)))", "(bin * (num 64) (bin + (bin - (name n) (name left)) (num 1)))"), "need entail"),
            ("does_not_decrease", self.with_place("decreases (name left)", "decreases (bin - (name n) (name left))"), "need entail"),
            # a register kept that the loop changes
            ("keeps_r13", self.with_place("keep rax", "keep r13 rax"), "a kept register does not hold what it held"),
        ]
        for tag, place, why in cases:
            with self.subTest(what=tag):
                self.refused(tag, self.lines, why, place=place)

    def test_a_place_that_says_too_little_is_refused(self):
        """Each of these places is true of the function, and none is kept by the loop as the verifier follows
        it: with nothing said of a cell, or of half the lanes, the next turn reads what nothing is known of."""
        cases = [
            ("no_cell", self.without("cell 2048 "), NO_SAVED),
            ("no_high_lanes", self.without("lane i zmm8 "), NO_LANES),
            ("no_upper_bound", self.without("fact (bin <= (name left) (name n))"), "need entail"),
            ("no_offset", self.without("fact (bin == (name off)"), "need entail"),
        ]
        for tag, place, why in cases:
            with self.subTest(what=tag):
                self.refused(tag, self.lines, why, place=place)

    def test_a_number_no_fact_names_is_not_followed(self):
        """A limit of the verifier, kept as a test. Without the two facts that name the last block's flags
        and its length the place is true, and is what the loop keeps. It is refused: on a path where the
        block is not the last the kernel has not worked the two numbers out, and the verifier, which follows
        what the lanes are said to hold on the terms the function made, has no term for them."""
        place = [l for l in self.place if not (l.startswith("fact (bin <= (bin ") and l.endswith("(num 255))"))]
        self.assertEqual(len(place), len(self.place) - 2)
        self.refused("no_facts_of_the_bytes", self.lines, AT_PLACE, place=place)

    def test_a_place_that_is_not_read_is_refused(self):
        # the readable form of a place's cells (prove.places): what it does not read
        spec = prove.ode.Spec(spec_text())
        kinds = statement.kinds_of(spec.contracts[NAME], NAME, spec.layouts)
        counted = {name: m["state"] for name, m in prove.ode.Parser(spec_text()).file()[2].items()}
        cases = [
            ("the word counted by a name of the contract", once("cell [rsp + 2048]: word i = lo(t)", "cell [rsp + 2048]: word flags = lo(t)"), "counts its words by a name the contract gives"),
            ("a cell from another register", once("cell [rsp + 2048]: word i", "cell [rbp + 2048]: word i"), "does not read yet"),
            ("a cell below the stack pointer", once("cell [rsp + 2048]: word i", "cell [rsp - 64]: word i"), "does not read yet"),
        ]
        for what, change, why in cases:
            with self.subTest(what=what):
                with self.assertRaises(SystemExit) as e:
                    prove.places(change(self.places), {}, statement.sequences(spec), kinds, counted, NAME)
                self.assertIn(why, str(e.exception))
        # and the verifier's own reading of the line: the cell lies a number of bytes above the stack pointer
        bad = self.dir / "bad_cell.proof"
        with bad.open("w") as f:
            f.write("\n".join([f"for {NAME}"] + self.with_place("cell 2048 i ", "cell -64 i ") + self.items) + "\n")
        self.assertIn("a place's cell lies a number of bytes above the stack pointer", self.verify_files(self.statement, bad))


if __name__ == "__main__":
    unittest.main()
