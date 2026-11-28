#!/usr/bin/env pypy3
"""Verify the shipped 16-way kernel: for every count of blocks, and for chunks of one block and of two.

    pypy3 test_p16.py        (skipped where Lean's `lake` is not installed)

The function is `blake3_servil_avx512_p16` as it lies in ../kcheck/b3hashr.o: 460 instructions. Its bytes
are not changed here. Its contract is examples/kernel/p16.contract, which is the contract of
../kcheck/proofs/inner.spec: sixteen lanes, each a chunk of `n` blocks read through a table of addresses,
the same counter in every lane, and four bytes of one register that give the flags, the flags of the first
and of the last block, and the last block's length. `trace depends on n`: which instructions run and which
addresses are touched depend on the count of blocks, and not on the key's bytes, the blocks' bytes, the
counter or those four bytes.

The kernel loops over the blocks. The class `Loop` verifies the contract as it is, for every `n` from 1 up.
The loop is cut at a place (written in ../wide/p16.ode, at the loop's bottom), which says how many blocks are
still to do, how far into the lanes the code has read, and what the vector registers hold: in each lane,
the chunk's chaining value after the blocks done. The verifier shows that of the first time round, and of
any later time round from the time before.

The class `P16` narrows the contract by one line, `requires n < 2` (one block a lane) or `requires n < 3`
(one or two), and gives no place. The verifier then follows each count of blocks as a path of its own.
With one block the jump back to the loop's head is never taken; with two it is taken once. What the
one-block case exercises beyond test_p16_table.py: the kinds `16 inputs`, `bytes a b c d` and `16 cvs` of
the contract language, the four bytes taken out of the register by shifts and masks, the two ORs that make
the first and last block's flags, the counter's two halves, the block length, and the choice between a last
block and any other.

The controls change the contract, one instruction, or the place. Each is a statement that is false, or a
place that says too little or something false. Each must be refused.
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
for folder in ("proof-core", "kcheck", "lang"):
    sys.path.insert(0, str(ROOT / folder))

import built
import lean_verify
import odec
import prove
import statement

NAME = "blake3_servil_avx512_p16"
OBJ = str(ROOT / "kcheck/b3hashr.o")
FOLLOW = "refused: the specification's words are not followed on the terms the function made"
OTHER_WORD = "refused: a word of the run is not known to hold what the specification says"
AT_PLACE = "refused: at the place 2471 the vector registers are not shown to hold what the place says"
AT_LEAST = "    requires n >= 1\n"
TRACE = "    trace depends on n\n"
JUMP = "refused: a jump on a flag that may depend on values kept out of the trace: which instructions run would depend on them"
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
    "disjoint inputs key 1",
    "disjoint inputs out 1",
    "disjoint key out 1",
    "hidden key",
    "hidden t",
    "hidden packed",
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
        ensures = [l for l in lines if l.startswith("ensuresw ")]
        low = "(bin % (name packed) (num 4294967296))"
        lane = lambda i: (
            "(call chunk (call words (name key)) (call counter (name t)) "
            "(bin % (name packed) (num 256)) "
            f"(bin % (bin / {low} (num 256)) (num 256)) "
            f"(bin % (bin / {low} (num 65536)) (num 256)) "
            f"(bin / {low} (num 16777216)) "
            f"(name n) (index (name inputs) (num {i})))"
        )
        # one line a lane: the 32 bytes of the lane's value, from byte 32 * i of the run on
        self.assertEqual(ensures, [f"ensuresw out {32 * i} 32 (call bytes_of {lane(i)})" for i in range(16)])

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
            ("no line of what overlaps", once("    requires disjoint(inputs, key, out, 1)\n", ""), "does not say `requires disjoint(inputs, key, out, 1)`"),
        ]
        for what, change, why in cases:
            with self.subTest(what=what):
                with self.assertRaises(SystemExit) as e:
                    lines_of(change)
                self.assertIn(why, str(e.exception))


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
    def prove_file(cls, st, pf, seconds=None, place=()):
        """(a proof was found and written to `pf`, the verifier's last word where none was). With `seconds`,
        the search gives up after that time. `place`: the lines of the function's places."""
        prover = prove.Prover(str(st), [f"for {NAME}"] + list(place), str(pf), until=None if seconds is None else time.time() + seconds)
        prover.last = ""
        try:
            try:
                items = prover.solve([])
            except prove.GaveUp:
                return False, "gave up"
            except prove.Unkept as e:
                return False, f"a kept register does not hold what it held: {e.args}"
            except prove.Marked as e:
                return False, f"refused: at the place {e.args[0]} register {e.args[1]} may depend on values kept out of the trace, which it did not on first coming there"
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
class P16(Files, unittest.TestCase):
    """The contract narrowed to one block a lane, or to one or two: no place."""

    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.dir = Path(tempfile.mkdtemp(prefix="ode-p16-"))
        cls.lines = lines_of(below(2))
        cls.statement = cls.write("one", cls.lines)
        cls.proof = cls.dir / "one.proof"
        got, last = cls.prove_file(cls.statement, cls.proof)
        assert got, last

    def refused(self, tag, lines, expected, proof=None):
        """The statement is not shown with the good proof, the prover finds no proof of it, and it says why."""
        st = self.write(tag, lines)
        self.assertNotEqual(self.verify_files(st, proof or self.proof), "shown\n", tag)
        got, last = self.prove_file(st, self.dir / f"{tag}.proof")
        self.assertFalse(got, tag)
        self.assertIn(expected, last.splitlines()[0], tag)

    def test_one_block_a_lane_is_shown(self):
        self.assertEqual(self.verify_files(self.statement, self.proof), "shown\n")
        self.assertLess(self.proof.stat().st_size, 4096)
        # The contract also verifies with the least stack the kernel can do with: 48 bytes of saved registers,
        # up to 63 to reach a 64-byte boundary, and 256 below that.
        st = self.write("stack_367", self.changed("stack 4096", "stack 367"))
        pf367 = self.dir / "stack_367.proof"
        got, last = self.prove_file(st, pf367)
        self.assertTrue(got, last)
        self.assertEqual(self.verify_files(st, pf367), "shown\n")

    def test_two_blocks_a_lane_are_shown(self):
        st, pf = self.write("two", lines_of(below(3))), self.dir / "two.proof"
        got, last = self.prove_file(st, pf)
        self.assertTrue(got, last)
        self.assertEqual(self.verify_files(st, pf), "shown\n")
        self.assertLess(pf.stat().st_size, 8192)
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

    def test_a_changed_line_of_a_lane_is_refused(self):
        """The statement has one line a lane: `ensuresw out FIRST COUNT …` says what 32 bytes of the run are.
        With one such line changed by hand, so that it is false or speaks of no part of the run that is
        whole words, nothing is shown."""
        at = lambda i: next(l for l in self.lines if l.startswith(f"ensuresw out {32 * i} 32 "))
        expr = lambda i: at(i)[len(f"ensuresw out {32 * i} 32 "):]
        self.assertEqual(sum(l.startswith("ensuresw out ") for l in self.lines), 16)
        cases = [
            # two lanes' values, each said of the other's bytes
            ("lanes_exchanged", [f"ensuresw out 0 32 {expr(1)}" if l == at(0) else f"ensuresw out 32 32 {expr(0)}" if l == at(1) else l for l in self.lines]),
            # a lane's value said of the 32 bytes that begin four bytes further on
            ("four_bytes_on", self.changed(at(3), f"ensuresw out 100 32 {expr(3)}")),
            # ... of 32 bytes that do not begin at a whole word
            ("two_bytes_on", self.changed(at(3), f"ensuresw out 98 32 {expr(3)}")),
            # the last lane's value said of 32 bytes that begin where the run ends
            ("past_the_run", self.changed(at(15), f"ensuresw out 512 32 {expr(15)}")),
            # a lane's value said to be 28 bytes, and 36
            ("28_bytes", self.changed(at(3), f"ensuresw out 96 28 {expr(3)}")),
            ("36_bytes", self.changed(at(3), f"ensuresw out 96 36 {expr(3)}")),
        ]
        for tag, lines in cases:
            with self.subTest(what=tag):
                self.refused(tag, lines, OTHER_WORD)
        # still true: a lane's line left out (less is said), and a lane's line twice
        for tag, lines in [("one_lane_less", [l for l in self.lines if l != at(7)]), ("one_lane_twice", self.lines + [at(7)])]:
            with self.subTest(what=tag):
                self.assertEqual(self.verify_files(self.write(tag, lines), self.proof), "shown\n")

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


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Loop(Files, unittest.TestCase):
    """The contract as it is: every count of blocks, by the place at the loop's bottom."""

    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.dir = Path(tempfile.mkdtemp(prefix="ode-p16-loop-"))
        cls.places = odec.places(str(ROOT / "wide/p16.ode"), "p16")          # the place, written at the loop in the source
        cls.statement, cls.proof = cls.dir / "every.statement", cls.dir / "every.proof"
        cls.runs, cls.found = prove.prove(spec_text(), [(OBJ, NAME, cls.places)], str(cls.statement), str(cls.proof))[NAME]
        with cls.statement.open() as f:
            cls.lines = f.read().split("\n")[:-1]
        with cls.proof.open() as f:
            proof = f.read().split("\n")[:-1]
        # the place as the verifier reads it (with the registers the prover found it keeps), then what was found
        cls.place = [l for l in proof if l.split()[0] in ("place", "name", "fact", "keep", "marked", "decreases", "lane")]
        cls.items = [l for l in proof if l.split()[0] in ("t", "p", "r", "s", "q")]
        assert proof == [f"for {NAME}"] + cls.place + cls.items, "the proof's lines are not: for, the place, what was found"

    def test_the_trace(self):
        """The key's bytes, the counter and the register of the four bytes are marked (`hidden key`, `hidden t`,
        `hidden packed`): shown, since the kernel only loads them into vector registers. The count of blocks is
        not marked (`trace depends on n`). With the table of addresses marked too it is refused: the addresses
        the blocks are read at would depend on something marked. With the count of blocks marked (the contract
        without its `trace` line) it is refused: the loop is left when the count is done."""
        hidden = [l for l in self.lines if l.startswith("hidden ")]
        self.assertEqual(hidden, ["hidden key", "hidden t", "hidden packed"])
        k = self.lines.index("hidden key")
        self.refused("hidden-table", self.lines[:k] + ["hidden inputs"] + self.lines[k:], "refused: an address may depend on values kept out of the trace")
        no_line = lines_of(once(TRACE, ""))
        self.assertEqual(no_line, self.lines[:k + 1] + ["hidden n"] + self.lines[k + 1:])
        self.refused("hidden-count", no_line, JUMP)
        # a contract that hides less says less: with the counter and the four bytes named too, the same place shows it
        named = lines_of(once(TRACE, "    trace depends on n, t, packed\n"))
        self.assertEqual(named, [l for l in self.lines if l not in ("hidden t", "hidden packed")])
        got, last = self.prove_file(self.write("named", named), self.dir / "named.proof", seconds=120, place=self.place)
        self.assertTrue(got, last)
        self.assertEqual(self.verify_files(self.dir / "named.statement", self.dir / "named.proof"), "shown\n")

    def refused(self, tag, lines, expected, place=None):
        """With these lines for the statement and these for the place: what was found for the good ones does
        not show it, the prover finds no proof of it, and it says why."""
        place = self.place if place is None else place
        st = self.write(tag, lines)
        with (self.dir / f"{tag}.good.proof").open("w") as f:
            f.write("\n".join([f"for {NAME}"] + place + self.items) + "\n")
        self.assertNotEqual(self.verify_files(st, self.dir / f"{tag}.good.proof"), "shown\n", tag)
        got, last = self.prove_file(st, self.dir / f"{tag}.proof", seconds=40, place=place)
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
        self.assertEqual(sum(l.startswith("i ") for l in self.lines), 460)
        self.assertEqual([l for l in self.lines if l.split()[0] in ("atleast", "below")], ["atleast n 1"])
        self.assertLess(self.proof.stat().st_size, 65536)
        # the place as the prover writes it for the verifier
        # (`marked rdx`: at the loop's bottom rdx holds the length of the block just done, which for the last
        # block is one of the four bytes the contract hides; the prover finds the line)
        self.assertEqual(self.place[:8], [
            "place 2471", "name left r13", "name off r14",
            "fact (bin >= (name left) (num 1))", "fact (bin <= (name left) (name n))",
            "fact (bin == (name off) (bin * (num 64) (bin - (name n) (name left))))",
            "keep rcx rbx rsp rbp rsi rdi r8 r9 r11 r12 r15", "marked rdx"])
        low = "(bin % (name packed) (num 4294967296))"
        self.assertEqual(self.place[8:], [
            "decreases (name left)",
            "lane i zmm0 zmm1 zmm2 zmm3 zmm4 zmm5 zmm6 zmm7 = (call chunk.h (call words (name key)) (call counter (name t)) "
            "(bin % (name packed) (num 256)) "
            f"(bin % (bin / {low} (num 256)) (num 256)) "
            f"(bin % (bin / {low} (num 65536)) (num 256)) "
            f"(bin / {low} (num 16777216)) "
            "(name n) (index (name inputs) (name i)) (bin + (bin - (name n) (name left)) (num 1)))"])
        # The contract also verifies with the least stack the kernel can do with.
        st = self.write("stack_367", self.changed("stack 4096", "stack 367"))
        pf367 = self.dir / "loop_stack_367.proof"
        got, last = self.prove_file(st, pf367, place=self.place)
        self.assertTrue(got, last)
        self.assertEqual(self.verify_files(st, pf367), "shown\n")

    def test_a_changed_contract_is_refused(self):
        cases = [
            # the first block's flags and the last block's, exchanged (false where there are two blocks or more)
            ("first_last", once(CALL, "chunk(key, t, flags, end, start, length, n, inputs[i])"), FOLLOW),
            ("end_length", once(CALL, "chunk(key, t, flags, start, length, end, n, inputs[i])"), FOLLOW),
            ("no_end", once(CALL, "chunk(key, t, flags, start, 0, length, n, inputs[i])"), FOLLOW),
            ("length_64", once(CALL, "chunk(key, t, flags, start, end, 64, n, inputs[i])"), FOLLOW),
            ("next_counter", once(CALL, "chunk(key, t + 1, flags, start, end, length, n, inputs[i])"), FOLLOW),
            # one block fewer than the function compresses, and two blocks whatever n is
            ("one_block_fewer", once(CALL, "chunk(key, t, flags, start, end, length, n - 1, inputs[i])"), OTHER_WORD),
            ("two_blocks", once(CALL, "chunk(key, t, flags, start, end, length, 2, inputs[i])"), FOLLOW),
            ("lanes_reversed", once(CALL, "chunk(key, t, flags, start, end, length, n, inputs[15 - i])"), OTHER_WORD),
            # with no lower bound a lane may have no block: the read at offset 0 is not shown to lie within it
            ("no_lower_bound", once(AT_LEAST, ""), "need entail"),
        ]
        for tag, change, why in cases:
            with self.subTest(what=tag):
                self.refused(tag, lines_of(change), why)
        with self.subTest(what="stack_366"):
            self.refused("stack_366", self.changed("stack 4096", "stack 366"), "need entail")

    def test_a_changed_instruction_is_refused(self):
        cases = [
            # at the loop's bottom the flags are no longer made those of a block that is not the first
            ("start_stays", "i 2471 2474 .mov 32 (.reg .r10) (.reg .r8)", "i 2471 2474 .nop", AT_PLACE),
            # the next block is read two blocks on
            ("two_blocks_on", "i 2474 2478 .add 64 (.reg .r14) (.imm 0x40)", "i 2474 2478 .add 64 (.reg .r14) (.imm 0x80)", "need entail"),
            # the last block's flags left out, and its length
            ("no_end", "i 766 768 .or 32 (.reg .rax) (.reg .rdi)", "i 766 768 .nop", AT_PLACE),
            ("no_length", "i 768 770 .mov 32 (.reg .rdx) (.reg .rsi)", "i 768 770 .nop", AT_PLACE),
            # the first block's flags taken from the wrong bits of the register; the counter's high half
            ("start_shift", "i 115 119 .shr32 .r10 8", "i 115 119 .shr32 .r10 9", AT_PLACE),
            ("counter_high", "i 819 823 .shr64 .rcx 32", "i 819 823 .shr64 .rcx 31", AT_PLACE),
        ]
        for tag, old, new, why in cases:
            with self.subTest(what=tag):
                self.refused(tag, self.changed(old, new), why)

    def test_a_changed_place_is_refused(self):
        done = "(bin + (bin - (name n) (name left)) (num 1)))"
        registers = "zmm0 zmm1 zmm2 zmm3 zmm4 zmm5 zmm6 zmm7"
        cases = [
            # the chaining value after one block fewer, or one more, than are done
            ("one_block_behind", self.with_place(done, "(bin - (name n) (name left)))"), AT_PLACE),
            ("one_block_ahead", self.with_place(done, "(bin + (bin - (name n) (name left)) (num 2)))"), AT_PLACE),
            # each lane with another lane's blocks; two registers exchanged; one register left out
            ("lanes_reversed", self.with_place("(index (name inputs) (name i))", "(index (name inputs) (bin - (num 15) (name i)))"), AT_PLACE),
            ("registers_exchanged", self.with_place(registers, "zmm1 zmm0 zmm2 zmm3 zmm4 zmm5 zmm6 zmm7"), AT_PLACE),
            ("seven_registers", self.with_place(registers, "zmm0 zmm1 zmm2 zmm3 zmm4 zmm5 zmm6"), AT_PLACE),
            # what another definition gives
            ("another_definition", self.with_place("(call chunk.h ", "(call compress "), AT_PLACE),
            # nothing said of the vector registers: the next time round they hold anything
            ("no_lanes", self.without("lane i "), "refused: a 512-bit register whose lanes are not all known"),
            # too little said of the count of blocks still to do, or of how far the code has read
            ("no_upper_bound", self.without("fact (bin <= (name left) (name n))"), "need entail"),
            ("no_lower_bound", self.without("fact (bin >= (name left) (num 1))"), "need entail"),
            ("no_offset", self.without("fact (bin == (name off)"), "need entail"),
            # something false of how far the code has read
            ("offset_ahead", self.with_place("(bin * (num 64) (bin - (name n) (name left)))", "(bin * (num 64) (bin + (bin - (name n) (name left)) (num 1)))"), "need entail"),
            # a number that does not decrease
            ("does_not_decrease", self.with_place("decreases (name left)", "decreases (bin - (name n) (name left))"), "need entail"),
            # a register kept that the loop changes; a register not kept that the loop needs
            ("keeps_r10", self.with_place("keep rcx", "keep r10 rcx"), "a kept register does not hold what it held"),
            ("does_not_keep_r8", self.with_place(" r8 r9", " r9"), AT_PLACE),
            # rdx is not said to be a register that may depend on a secret on a later coming there
            ("rdx_not_marked", self.without("marked rdx"), "refused: at the place 2471 register 2 may depend on values kept out of the trace, which it did not on first coming there"),
        ]
        for tag, place, why in cases:
            with self.subTest(what=tag):
                self.refused(tag, self.lines, why, place=place)

    def test_a_place_that_is_not_read_is_refused(self):
        # the readable form of a place's lanes (prove.places): what it does not read
        spec = prove.ode.Spec(spec_text())
        kinds = statement.kinds_of(spec.contracts[NAME], NAME, spec.layouts)
        counted = {name: m["state"] for name, m in prove.ode.Parser(spec_text()).file()[2].items()}
        self.assertEqual(counted, {"chunk": "h"})
        cases = [
            ("no sequence with a count", once("chunk(key, t, flags, start, end, length, n, inputs[i]) after", "compress(key, inputs[i][0], t, length, flags) after"), "a sequence with a count"),
            ("a register that is no vector register", once("zmm0 .. zmm7", "zmm0 .. r8"), "vector registers"),
            ("registers the wrong way round", once("zmm0 .. zmm7", "zmm7 .. zmm0"), "no such vector registers"),
            ("the lane counted by a name of the contract", once("lane i: ", "lane flags: "), "count by a name the contract gives"),
        ]
        for what, change, why in cases:
            with self.subTest(what=what):
                with self.assertRaises(SystemExit) as e:
                    prove.places(change(self.places), {}, statement.sequences(spec), kinds, counted, NAME)
                self.assertIn(why, str(e.exception))


if __name__ == "__main__":
    unittest.main()
