#!/usr/bin/env pypy3
"""Verify the entry of the shipped 32-way kernel that the hash calls: lane i has the counter t + i.

    pypy3 test_k32.py        (skipped where Lean's `lake` is not installed)

The function is `blake3_servil_avx512_k32` as it lies in ../kcheck/b3hashr.o: 702 instructions. Its bytes are
not changed here. All but three of them are the kernel that test_p32.py verifies
(`blake3_servil_avx512_p32`, the same code entered twelve bytes later, where every lane gets the same
counter). The contract is examples/kernel/k32.contract, which is the contract of
../kcheck/proofs/inner.spec: `out[i] = chunk(key, t + i, ..., inputs[i])` for the thirty-two lanes.

Entered here, the kernel runs six instructions that the other entry jumps over. They make the thirty-two
counters from the one given:

- `vpaddd zmm2, zmm0, [rip + ...]`, twice: the counter's low word and the numbers 0 to 15, then 16 to 31. The
  sixteen numbers are a constant in the file's read-only data, which the decoder puts into the instruction.
- `vpcmpud k1, zmm2, zmm0, 1`, twice: into a mask register, lane by lane, whether the sum is below the low
  word it was made from. That is so exactly where the sum wrapped at 2^32.
- `vpaddd zmm5{k1}, zmm1, zmm4`, twice: the high word and one, in the lanes the mask names; the other lanes
  keep the high word.

The account of the machine has the mask registers k1 to k7 for these (Machine.lean; test_machine.py compares
the three rows of the table with conc.py). The verifier holds a lane of a mask as a term "is this word below
that one", and a lane set under a mask as a term "this word where the mask's lane is set, else that one". On
the specification's side `t + i` is a counter and a number of the text more. Its low word is the word of the
sum. Its high word is found as the code works it out: the high word of `t`, or that and one, by whether the
low word of the sum is below the low word of `t` (Core.lean, `hiPlus`; that this is the high word of the
counter is `hiPlus_sound`).

The class `K32` narrows the contract by one line, `requires n < 2` or `requires n < 3`, and gives no place.
The class `Loop` takes the contract as it is, for every `n`, with the place of examples/kernel/k32.places:
the place of the other entry, with the counters t + i and t + i + 16 in the lanes and in the four cells of
the frame that hold the counters' words.

The controls change the contract, one instruction, or the place. Each is a statement that is false. Each
must be refused.
"""
from pathlib import Path
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
for folder in ("proof-core", "kcheck"):
    sys.path.insert(0, str(ROOT / folder))

import built
import lean_verify
import prove
import statement
from test_p32 import Files, once, both, OBJ, FOLLOW, AT_LEAST         # (the same file, and the same words of refusal)

NAME = "blake3_servil_avx512_k32"
AT_PLACE = "refused: at the place 3920 the vector registers are not shown to hold what the place says"
AT_CELL = "refused: at the place 3920 a cell of the frame is not shown to hold what the place says"
NO_MASK = "refused: a 512-bit register or a mask register whose lanes are not all known"
NO_PLACE = "refused: a row that sets what is no 512-bit register"
CALL = "chunk(key, t + i, flags, start, end, length, n, inputs[i])"
# The instructions that only this entry runs: the numbers 0 to 15 and 16 to 31 added to the low word, the
# two compares, and the two adds under a mask.
ENTRY = "i 4 10 .mov 32 (.reg .r10) (.imm 0x1)"
LOW_0 = "i 107 117 .zpadddc 2 0 0x" + "".join(f"{k:08X}" for k in reversed(range(16))) + "#512"
LOW_16 = "i 117 127 .zpadddc 3 0 0x" + "".join(f"{k:08X}" for k in reversed(range(16, 32))) + "#512"
BELOW_0, BELOW_16 = "i 127 134 .zpcmpud 1 2 0 1", "i 134 141 .zpcmpud 2 3 0 1"
HIGH_0, HIGH_16 = "i 147 153 .zpaddd_k 5 1 1 4", "i 153 159 .zpaddd_k 6 2 1 4"
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
    with (HERE / "examples/kernel/k32.contract").open() as f:
        text = f.read()
    return change(spec + "\n" + text)


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
        self.assertEqual(sum(l.startswith("i ") for l in lines), 702)
        for line in (ENTRY, LOW_0, LOW_16, BELOW_0, BELOW_16, HIGH_0, HIGH_16):
            self.assertEqual(lines.count(line), 1, line)
        # one line a lane: the 32 bytes of the lane's value, from byte 32 * i of the run on
        ensures = [l for l in lines if l.startswith("ensuresw ")]
        self.assertEqual(len(ensures), 32)
        for i, line in enumerate(ensures):
            self.assertTrue(line.startswith(f"ensuresw out {32 * i} 32 (call bytes_of (call chunk "), line[:80])
            self.assertEqual(line.count("(call chunk "), 1)
            # lane i has the counter t + i, and the blocks its address in the table points to
            self.assertIn(f"(bin + (call counter (name t)) (num {i})) ", line)
            self.assertIn(f"(index (name inputs) (num {i}))", line)


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class K32(Files, unittest.TestCase):
    """The contract narrowed to one block a lane, or to one or two: no place."""
    name = NAME

    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.dir = Path(tempfile.mkdtemp(prefix="ode-k32-"))
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

    def test_two_blocks_a_lane_are_shown(self):
        st, pf = self.write("two", lines_of(below(3))), self.dir / "two.proof"
        got, last = self.prove_file(st, pf)
        self.assertTrue(got, last)
        self.assertEqual(self.verify_files(st, pf), "shown\n")
        self.assertLess(pf.stat().st_size, 4096)

    def test_a_changed_contract_is_refused(self):
        one = below(2)
        cases = [
            # what the other entry does: every lane with the counter t
            ("same_counter", both(one, once(CALL, "chunk(key, t, flags, start, end, length, n, inputs[i])")), FOLLOW),
            # every lane's counter one more; the counters the other way round; the counters of the two halves exchanged
            ("next_counter", both(one, once(CALL, "chunk(key, t + i + 1, flags, start, end, length, n, inputs[i])")), FOLLOW),
            ("counters_reversed", both(one, once(CALL, "chunk(key, t + 31 - i, flags, start, end, length, n, inputs[i])")), FOLLOW),
            ("halves_exchanged", both(one, once(CALL, "chunk(key, t + (i + 16) % 32, flags, start, end, length, n, inputs[i])")), FOLLOW),
            # each lane's counter doubled in its distance
            ("twice", both(one, once(CALL, "chunk(key, t + 2 * i, flags, start, end, length, n, inputs[i])")), FOLLOW),
            # each lane with another lane's blocks
            ("lanes_reversed", both(one, once(CALL, "chunk(key, t + i, flags, start, end, length, n, inputs[31 - i])")), FOLLOW),
        ]
        for tag, change, why in cases:
            with self.subTest(what=tag):
                self.refused(tag, lines_of(change), why)

    def test_a_changed_instruction_is_refused(self):
        swapped = LOW_0[:-12] + "0000000000000001#512"           # the numbers of lanes 0 and 1 exchanged
        self.assertTrue(LOW_0.endswith("0000000100000000#512"))
        cases = [
            # entered as the other entry is: every lane gets the counter t
            ("entered_as_the_other", ENTRY, "i 4 10 .mov 32 (.reg .r10) (.imm 0x0)", FOLLOW),
            # the numbers added to the low word: two of them exchanged; the first half's given to the second half too
            ("numbers_exchanged", LOW_0, swapped, FOLLOW),
            ("second_half_from_0", LOW_16, LOW_16[:22] + LOW_0[22:], FOLLOW),
            # the compare the other way round: the high word is one more in the lanes that did not wrap
            ("compare_reversed", BELOW_0, "i 127 134 .zpcmpud 1 0 2 1", FOLLOW),
            # the first half's high words under the second half's mask
            ("mask_of_the_other_half", HIGH_0, "i 147 153 .zpaddd_k 5 2 1 4", FOLLOW),
            # no carry into the high word (false where the low word and i pass 2^32)
            ("no_carry", HIGH_0, "i 147 153 .zmov 5 1", FOLLOW),
            # the high word doubled where the low word wrapped, in place of one more
            ("carry_doubles", HIGH_0, "i 147 153 .zpaddd_k 5 1 1 1", FOLLOW),
        ]
        for tag, old, new, why in cases:
            with self.subTest(what=tag):
                self.refused(tag, self.changed(old, new), why)

    def test_a_mask_register_with_no_meaning_is_refused(self):
        """Written as a mask, k0 says "no mask" to the processor. The account gives no meaning to an
        instruction that names it, and so the verifier refuses a compare into it and an add under it. An add
        under a mask register that nothing has set is refused too: nothing is known of its lanes."""
        self.refused("compare_into_k0", self.changed(BELOW_0, "i 127 134 .zpcmpud 0 2 0 1"), NO_PLACE)
        self.refused("under_k0", self.changed(HIGH_0, "i 147 153 .zpaddd_k 5 0 1 4"), NO_MASK)
        self.refused("under_k3", self.changed(HIGH_0, "i 147 153 .zpaddd_k 5 3 1 4"), NO_MASK)


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Loop(Files, unittest.TestCase):
    """The contract as it is: every count of blocks, by the place at the loop's bottom."""
    name = NAME

    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.dir = Path(tempfile.mkdtemp(prefix="ode-k32-loop-"))
        with (HERE / "examples/kernel/k32.places").open() as f:
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

    def test_every_count_of_blocks_is_shown(self):
        self.assertEqual(self.verify_files(self.statement, self.proof), "shown\n")
        # the kept proof is what the prover finds, and shows it from the files
        kept = HERE / "proofs" / f"{NAME}.proof"
        self.assertEqual(lean_verify.verify(spec_text(), [(OBJ, NAME)], str(kept)), (True, "shown"))
        with kept.open() as f, self.proof.open() as g:
            self.assertEqual(f.read(), g.read())
        self.assertEqual(sum(l.startswith("i ") for l in self.lines), 702)
        self.assertEqual([l for l in self.lines if l.split()[0] in ("atleast", "below")], ["atleast n 1"])
        self.assertLess(self.proof.stat().st_size, 8192)
        # the place as the prover writes it for the verifier: the counters of the lanes, and of the cells
        self.assertEqual(self.place[0], "place 3920")
        first, second = "(bin + (call counter (name t)) (name i))", "(bin + (bin + (call counter (name t)) (name i)) (num 16))"
        lanes = [l for l in self.place if l.startswith("lane ")]
        self.assertEqual(len(lanes), 2)
        self.assertIn(f"(call chunk.h (call words (name key)) {first} ", lanes[0])
        self.assertIn(f"(call chunk.h (call words (name key)) {second} ", lanes[1])
        self.assertEqual([l for l in self.place if l.startswith("cell ")], [
            f"cell 2048 i (call lo {first})", f"cell 2112 i (call hi {first})",
            f"cell 2176 i (call lo {second})", f"cell 2240 i (call hi {second})"])

    def test_a_changed_contract_is_refused(self):
        cases = [
            # what the other entry does: every lane with the counter t
            ("same_counter", once(CALL, "chunk(key, t, flags, start, end, length, n, inputs[i])"), FOLLOW),
            ("next_counter", once(CALL, "chunk(key, t + i + 1, flags, start, end, length, n, inputs[i])"), FOLLOW),
            ("halves_exchanged", once(CALL, "chunk(key, t + (i + 16) % 32, flags, start, end, length, n, inputs[i])"), FOLLOW),
            # the first block's flags and the last block's, exchanged (false where there are two blocks or more)
            ("first_last", once(CALL, "chunk(key, t + i, flags, end, start, length, n, inputs[i])"), FOLLOW),
        ]
        for tag, change, why in cases:
            with self.subTest(what=tag):
                self.refused(tag, lines_of(change), why)

    def test_a_changed_instruction_is_refused(self):
        cases = [
            # entered as the other entry is: every lane then has the counter t
            ("entered_as_the_other", ENTRY, "i 4 10 .mov 32 (.reg .r10) (.imm 0x0)", AT_PLACE),
            # the compare the other way round; no carry into the high word
            ("compare_reversed", BELOW_0, "i 127 134 .zpcmpud 1 0 2 1", AT_PLACE),
            ("no_carry", HIGH_16, "i 153 159 .zmov 6 1", AT_PLACE),
            # in the loop: the first half's high words read from the cell of the second half's
            ("cell_of_the_other_half", "i 2195 2203 .zload true 21 .rsp 0x840", "i 2195 2203 .zload true 21 .rsp 0x8C0", AT_PLACE),
        ]
        for tag, old, new, why in cases:
            with self.subTest(what=tag):
                self.refused(tag, self.changed(old, new), why)

    def test_a_changed_place_is_refused(self):
        first, second = "(bin + (call counter (name t)) (name i))", "(bin + (bin + (call counter (name t)) (name i)) (num 16))"
        cases = [
            # the cells as the other entry leaves them: the words of t in every word
            ("cell_same_counter", self.with_place(f"cell 2048 i (call lo {first})", "cell 2048 i (call lo (call counter (name t)))"), AT_CELL),
            ("cell_high_same_counter", self.with_place(f"cell 2112 i (call hi {first})", "cell 2112 i (call hi (call counter (name t)))"), AT_CELL),
            # a cell of the first half said to hold the second half's counters; the low words where the high ones are
            ("cell_of_the_other_half", self.with_place(f"cell 2112 i (call hi {first})", f"cell 2112 i (call hi {second})"), AT_CELL),
            ("cell_low_for_high", self.with_place(f"cell 2240 i (call hi {second})", f"cell 2240 i (call lo {second})"), AT_CELL),
            # the lanes of the second half said to have the first half's counters
            ("lanes_of_the_other_half", self.with_place(f"(call chunk.h (call words (name key)) {second} ", f"(call chunk.h (call words (name key)) {first} "), AT_PLACE),
        ]
        for tag, place, why in cases:
            with self.subTest(what=tag):
                self.refused(tag, self.lines, why, place=place)


if __name__ == "__main__":
    unittest.main()
