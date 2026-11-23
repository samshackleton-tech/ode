#!/usr/bin/env python3
"""Three functions for AArch64, in the verifier in Lean (Core.lean): a measurement, on a branch.

The verifier is given AArch64's table (../arm64/arm64.tab) in place of x86-64's, and each function's lines
say `machine arm64`: its arguments are then in x0 to x7, the address to return to is in x30, and x19 to x29
are the registers it gives back as it found them. The three functions (examples/arm64/mix.s, assembled by
clang into armmix.o; their contracts in mix.spec):

  arm_mix16_3      the mixing step of the trial on a block of sixteen words: `eor` and `rev32` on four lanes
  arm_mix16_again  the same by a call of arm_mix16_3 through `bl`, the address to return to kept in the frame
  arm_mix16_6      two such calls, a block of the frame handed to the first to write and to the second to read

The verifier says `shown` of the three with a proof file of three lines. With a function changed in one
instruction, or its contract in one place, so that what is stated is false, it is not shown, and the prover
finds no proof: each case names what the verifier then says. One change leaves the statement true and is
still shown (a control).

On an AArch64 machine the functions' own instruction words are run on the processor and compared with the
contract written in C, on random blocks; the changed copies that can be run safely give other bytes.

    python3 test_arm.py        (the verification: skipped where Lean's `lake` is not installed;
                                the runs: skipped where the machine is no AArch64 one, or has no clang)"""
import os, platform, random, shutil, subprocess, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path[:0] = [HERE, os.path.join(HERE, "..", "arm64"), os.path.join(HERE, "..", "core")]
import built, lean_verify, prove, statement, table
import obj as aobj, word

LAKE = lean_verify.LAKE
ARM = os.path.join(HERE, "examples", "arm64")
OBJ = os.path.join(ARM, "armmix.o")
KEPT = os.path.join(HERE, "proofs", "arm_mix16_6.proof")
MIX, AGAIN, SIX = NAMES = ["arm_mix16_3", "arm_mix16_again", "arm_mix16_6"]
WAYS = {w.row.name: w for w in word.ways(table.read(word.TABLE))}

FOLLOWED = "refused: the specification's words are not followed on the terms the function made"
WORD = "refused: a word of the run is not known to hold what the specification says"
LACKS = "need entail"                    # an inequality is to be shown, and the proof has no proof of it (the prover finds none)
LINK = "refused: at the return the register that held the address to return to does not hold what it held at entry"
KEEPS = "refused: at the return a register a callee keeps does not hold what it held at entry"
EMPTY_CELL = "refused: a read of the frame where nothing was written"
ON16 = "refused: the stack pointer is the base of a load or store where it is not shown to be a multiple of 16"
CALL = "refused: a call that is not one this function's machine makes of a function for that machine, or a stack pointer that is not shown to be a multiple of 16 at a call"
NO_RUN = "refused: a called function is given a run that is no part of a run this function was given to read"
# (what is changed, [(function, which instruction, the row of the instruction put there, its placeholders)], what the verifier then says)
CHANGES = [
    ("a word is turned in the other register", [(MIX, 3, "rev32_8h", {"X": 0, "Y": 1})], FOLLOWED),
    ("the second step is left out", [(MIX, 4, "nop", {})], FOLLOWED),
    ("a's words are stored", [(MIX, 8, "st1_4s", {"X": 1, "B": "x0"})], WORD),
    ("out is stepped by 8 bytes", [(MIX, 11, "add_rri", {"D": "x0", "S": "x0", "I": 8})], WORD),
    ("d is stepped by 32 bytes, so that words are read past its end", [(MIX, 9, "add_rri", {"D": "x1", "S": "x1", "I": 32})], LACKS),
    ("the first words are read from out", [(MIX, 0, "ld1_4s", {"X": 0, "B": "x0"})], FOLLOWED),
    ("a's address is taken from x19", [(MIX, 1, "ld1_4s", {"X": 1, "B": "x19"})], "refused: sixteen bytes that are of no run of words given to read"),
    ("the return is left out", [(MIX, 45, "nop", {})], "refused: no instruction at 184"),
    ("x30 is written, and the function returns by it", [(MIX, 9, "add_rri", {"D": "x30", "S": "x1", "I": 16})], LINK),
    ("x19 is written", [(MIX, 10, "add_rri", {"D": "x19", "S": "x2", "I": 16})], KEEPS),
    ("the stack pointer is moved down, in a function whose contract allows no stack", [(MIX, 10, "sub_sp", {"I": 16})], LACKS),
    ("a register is stored at the stack pointer, in a function with no frame", [(MIX, 9, "str64_sp", {"S": "x1", "N": 0})],
     "refused: a write that is not eight bytes of the frame in use"),
    ("the address to return to is kept in another cell than it is taken back from", [(AGAIN, 1, "str64_sp", {"S": "x30", "N": 0})], EMPTY_CELL),
    ("a frame of 8 bytes: the stack pointer is then no multiple of 16 where a register is stored at it",
     [(AGAIN, 0, "sub_sp", {"I": 8}), (AGAIN, 4, "add_sp", {"I": 8})], ON16),
    ("the stack pointer is no multiple of 16 at the call", [(AGAIN, 0, "sub_sp", {"I": 8}), (AGAIN, 1, "nop", {})], CALL),
    ("the address to return to is not taken back after the call", [(AGAIN, 3, "nop", {})], LINK),
    ("the stack pointer is moved up by 32 bytes after a frame of 16", [(AGAIN, 4, "add_sp", {"I": 32})], LACKS),
    ("a frame of 32 bytes, where the contract allows 16", [(AGAIN, 0, "sub_sp", {"I": 32}), (AGAIN, 4, "add_sp", {"I": 32})], LACKS),
    ("the second call is given out as a", [(SIX, 19, "mov_rr", {"D": "x2", "S": "x19"})], NO_RUN),
    ("x19 is kept in the cell of the address to return to", [(SIX, 2, "str64_sp", {"S": "x19", "N": 64})], EMPTY_CELL),
    ("the second call reads the frame from 8 bytes on", [(SIX, 18, "add_of_sp", {"D": "x1", "I": 8})], NO_RUN),
    ("x19 is taken back from x20's cell", [(SIX, 22, "ldr64_sp", {"D": "x19", "N": 80})], KEEPS),
    ("the first call is given d to write", [(SIX, 15, "mov_rr", {"D": "x0", "S": "x1"})],
     "refused: a called function is given to write what is not whole words of a run this function may read and write, each of them known"),
    ("a cell of the frame's block is not written before the first call", [(SIX, 10, "nop", {})],
     "refused: a called function is given to write what is not whole cells of this function's frame, each of them known"),
]
# A change that leaves the statement true: the frame's block is written with ones, not zeros, before the first call writes it.
STILL_TRUE = ("the frame's block is written with ones first", [(SIX, 6, "mov_ri", {"D": "x9", "I": 1})])
# (what is changed, the specification as it is, the specification changed, what the verifier then says)
SPECS = [
    ("arm_mix16_again's contract allows 8 bytes of stack", "    stack 16\n", "    stack 8\n", LACKS),
    ("arm_mix16_6's contract allows 80 bytes of stack", "    stack 96\n", "    stack 80\n", LACKS),
    ("arm_mix16_6's contract says the three steps once", "ensures out = mix16_chain_3(mix16_chain_3(d, a), a)", "ensures out = mix16_chain_3(d, a)", WORD),
    ("a step turns a word by 8", "(d ^ a) >>> 16", "(d ^ a) >>> 8", FOLLOWED),
]
# The changed copies that a processor can run without harm, and the control: each named by what is changed.
RUN = ["a word is turned in the other register", "the second step is left out", "a's words are stored", "out is stepped by 8 bytes",
       "the first words are read from out", "the second call is given out as a"]
ARM_MACHINE = platform.machine() in ("arm64", "aarch64")


def changed(patches, path):
    """The object file with instructions of its functions replaced, each by the word the table writes for the instance."""
    with open(OBJ, "rb") as f: b = bytearray(f.read())
    for fn, at, row, bind in patches:
        _, start = aobj.words(OBJ, fn)
        b[start + 4 * at:start + 4 * at + 4] = word.encode(WAYS[row], bind)
    with open(path, "wb") as f: f.write(bytes(b))
    return path


@unittest.skipUnless(LAKE, "Lean's lake is not installed")
class Verified(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.dir = tempfile.mkdtemp(prefix="odearm-")
        cls.addClassCleanup(shutil.rmtree, cls.dir)
        with open(os.path.join(ARM, "mix.spec")) as f: cls.spec = f.read()

    def path(self, name): return os.path.join(self.dir, name)
    def fns(self, o=OBJ): return [(o, n) for n in NAMES]

    def found(self, spec, o, name="try"):
        """The prover's numbers; or, where it finds no proof, the verifier's last word."""
        try: return prove.prove(spec, [(o, n, "") for n in NAMES], self.path(name + ".statement"), self.path(name + ".proof"))
        except SystemExit as e:
            said = str(e)
            self.assertTrue(said.startswith("prove: no proof of arm_mix16_"), said[:200])
            return said.split("\n", 1)[1]

    def test_shown_and_the_kept_proof_is_what_the_prover_finds(self):
        self.assertEqual(lean_verify.verify(self.spec, self.fns(), KEPT), (True, "shown"))
        numbers = self.found(self.spec, OBJ, "kept")
        self.assertEqual(list(numbers), NAMES)
        with open(KEPT) as f, open(self.path("kept.proof")) as g: self.assertEqual(f.read(), g.read())
        with open(KEPT) as f: self.assertEqual(f.read(), "".join(f"for {n}\n" for n in NAMES))       # (three lines: no arithmetic had to be shown)
        with open(self.path("kept.statement")) as f: lines = f.read().split("\n")
        self.assertEqual(lines.count("machine arm64"), 3)
        self.assertEqual([len([l for l in lines[lines.index(f"fn {n}"):] if l.startswith("i ")]) for n in NAMES], [78, 32, 26])      # 46, 6 and 26 instructions
        self.assertIn("i 8 12 .bl arm_mix16_3", lines)
        self.assertIn("i 4 8 .str64_sp .x30 0x8", lines)

    def test_a_function_changed_in_one_place(self):
        for what, patches, why in CHANGES:
            with self.subTest(what=what):
                o = changed(patches, self.path("changed.o"))
                shown, said = lean_verify.verify(self.spec, self.fns(o), KEPT)
                self.assertFalse(shown, what)
                self.assertTrue(said.startswith(why), f"{what}: {said[:200]}")
                self.assertTrue(said.endswith("\nin " + patches[0][0]), said[-60:])     # (the verifier names the function)
                last = self.found(self.spec, o)
                self.assertIsInstance(last, str, what)                  # no proof is found
                self.assertTrue(last.startswith(why), f"{what}: {last[:200]}")

    def test_a_change_that_leaves_the_statement_true_is_still_shown(self):
        what, patches = STILL_TRUE
        o = changed(patches, self.path("true.o"))
        with open(o, "rb") as f, open(OBJ, "rb") as g: self.assertNotEqual(f.read(), g.read())
        self.assertEqual(lean_verify.verify(self.spec, self.fns(o), KEPT), (True, "shown"))

    def test_a_contract_changed_in_one_place(self):
        for what, old, new, why in SPECS:
            with self.subTest(what=what):
                self.assertEqual(self.spec.count(old), 1)
                spec = self.spec.replace(old, new)
                shown, said = lean_verify.verify(spec, self.fns(), KEPT)
                self.assertFalse(shown, what)
                self.assertTrue(said.startswith(why), f"{what}: {said[:200]}")
                last = self.found(spec, OBJ)
                self.assertIsInstance(last, str, what)
                self.assertTrue(last.startswith(why), f"{what}: {last[:200]}")

    def test_the_statement_says_the_machine(self):
        lines = statement.statement(self.spec, self.fns())
        say = lambda tab, st, pf: subprocess.run([lean_verify.EXE, tab, st, pf], capture_output=True, text=True).stdout
        with open(self.path("s.statement"), "w") as f: f.write("\n".join(lines) + "\n")
        self.assertEqual(say(statement.TABLES["arm64"], self.path("s.statement"), KEPT), "shown\n")
        # x86-64's table has no row for these instructions
        self.assertEqual(say(statement.TABLES["x86-64"], self.path("s.statement"), KEPT), "refused: an instruction that is no row of the table: .ld1 0 .x1\n")
        # without its `machine` lines the statement is of functions for x86-64: their arguments are then in other registers
        with open(self.path("x.statement"), "w") as f: f.write("\n".join(l for l in lines if l != "machine arm64") + "\n")
        self.assertEqual(say(statement.TABLES["arm64"], self.path("x.statement"), KEPT), "refused: sixteen bytes that are of no run of words given to read\nin arm_mix16_3\n")
        # the machine is the statement's to say: a proof cannot
        with open(self.path("m.proof"), "w") as f: f.write("for arm_mix16_3\nmachine arm64\n")
        self.assertEqual(say(statement.TABLES["arm64"], self.path("s.statement"), self.path("m.proof")), "refused: a line of the statement in the proof: machine arm64\n")
        # and it is said before the function's instructions
        at = lines.index("machine arm64")
        moved = lines[:at] + lines[at + 1:at + 3] + ["machine arm64"] + lines[at + 3:]
        with open(self.path("late.statement"), "w") as f: f.write("\n".join(moved) + "\n")
        self.assertEqual(say(statement.TABLES["arm64"], self.path("late.statement"), KEPT), "refused: `machine` after an instruction or an argument of the function: machine arm64\n")

    def test_the_object_file_is_read_by_the_table_alone(self):
        rows = aobj.read(OBJ, MIX)
        self.assertEqual(len(rows), 46)
        self.assertEqual([r[2].split()[0] for r in rows[:12]], [".ld1", ".ld1", ".eor", ".rev32", ".eor", ".rev32", ".eor", ".rev32", ".st1", ".addi", ".addi", ".addi"])
        self.assertEqual(aobj.called(OBJ, SIX), [MIX])
        with open(OBJ, "rb") as f: b = bytearray(f.read())
        _, start = aobj.words(OBJ, MIX)
        b[start:start + 4] = bytes.fromhex("1f2003d5")                        # (a nop: read)
        b[start + 4:start + 8] = (0x9B007C00).to_bytes(4, "little")           # mul x0, x0, x0: no row of the table
        with open(self.path("norow.o"), "wb") as f: f.write(bytes(b))
        with self.assertRaises(aobj.Stop) as e: aobj.read(self.path("norow.o"), MIX)
        self.assertIn("is no instance of a row of the table", str(e.exception))


HARNESS = r"""
#include <stdint.h>
#include <stdio.h>
#include <string.h>
void arm_mix16_3(uint8_t *out, const uint8_t *d, const uint8_t *a);
void arm_mix16_again(uint8_t *out, const uint8_t *d, const uint8_t *a);
void arm_mix16_6(uint8_t *out, const uint8_t *d, const uint8_t *a);
static uint32_t ror(uint32_t x, int n) { return (x >> n) | (x << (32 - n)); }
static void step(uint32_t *d, const uint32_t *a) { for (int i = 0; i < 16; i++) d[i] = ror(d[i] ^ a[i], 16); }
/* mix16_chain_3 of mix.spec: d, then a, then d again */
static void chain3(uint8_t *out, const uint8_t *d, const uint8_t *a) {
    uint32_t D[16], A[16];
    memcpy(D, d, 64); memcpy(A, a, 64);
    step(D, A); step(A, D); step(D, A);
    memcpy(out, D, 64);
}
int main(void) {
    uint8_t in[192], want[64], got[3][64], guard[3][64 + 32], t[64];
    int same[3] = {1, 1, 1};
    long cases = 0;
    while (fread(in, 1, 192, stdin) == 192) {
        cases++;
        for (int f = 0; f < 3; f++) {
            uint8_t *out = guard[f] + 16;
            memcpy(guard[f], in + 128, 16); memcpy(out, in + 128, 64); memcpy(out + 64, in + 144, 16);      /* out holds bytes before; so do the bytes around it */
            if (f == 0) arm_mix16_3(out, in, in + 64);
            if (f == 1) arm_mix16_again(out, in, in + 64);
            if (f == 2) arm_mix16_6(out, in, in + 64);
            memcpy(got[f], out, 64);
            if (memcmp(guard[f], in + 128, 16) || memcmp(out + 64, in + 144, 16)) same[f] = 0;                /* nothing around out is written */
        }
        chain3(want, in, in + 64);
        if (memcmp(got[0], want, 64)) same[0] = 0;
        if (memcmp(got[1], want, 64)) same[1] = 0;
        chain3(t, in, in + 64); chain3(want, t, in + 64);
        if (memcmp(got[2], want, 64)) same[2] = 0;
    }
    printf("%ld cases: arm_mix16_3 %s, arm_mix16_again %s, arm_mix16_6 %s\n", cases, same[0] ? "same" : "differs", same[1] ? "same" : "differs", same[2] ? "same" : "differs");
    return 0;
}
"""


@unittest.skipUnless(ARM_MACHINE and shutil.which("clang"), "an AArch64 processor and clang are needed")
class Run(unittest.TestCase):
    """The functions' instruction words on this machine's processor. A RUN, not a proof."""
    @classmethod
    def setUpClass(cls):
        cls.dir = tempfile.mkdtemp(prefix="odearmrun-")
        cls.addClassCleanup(shutil.rmtree, cls.dir)
        rng = random.Random(8)
        cls.cases = bytes(rng.getrandbits(8) for _ in range(192 * 500))

    def run_words(self, o):
        """What the harness says of the three functions, laid down word for word as the object file has them."""
        lines = ["#ifdef __APPLE__", "#define SYM(x) _##x", "#else", "#define SYM(x) x", "#endif", ".text", ".p2align 2"]
        for name in NAMES:
            words, _ = aobj.words(o, name)
            rows = aobj.read(o, name)
            lines += [f".globl SYM({name})", f"SYM({name}):"]
            for w, (_, _, text) in zip(words, rows):
                # (a call's word names no place: the function it calls is named, as the file's relocation names it)
                lines.append(f"    bl SYM({text.split()[1]})" if text.startswith(".bl ") else f"    .long 0x{int.from_bytes(w, 'little'):08x}")
        with open(os.path.join(self.dir, "fns.S"), "w") as f: f.write("\n".join(lines) + "\n")
        with open(os.path.join(self.dir, "harness.c"), "w") as f: f.write(HARNESS)
        exe = os.path.join(self.dir, "run")
        subprocess.run(["clang", "-O1", "-o", exe, os.path.join(self.dir, "harness.c"), os.path.join(self.dir, "fns.S")], check=True, capture_output=True)
        r = subprocess.run([exe], input=self.cases, capture_output=True, timeout=60)
        return r.stdout.decode().strip() if r.returncode == 0 else f"ended with {r.returncode}"

    def test_the_functions_do_what_their_contracts_say(self):
        self.assertEqual(self.run_words(OBJ), "500 cases: arm_mix16_3 same, arm_mix16_again same, arm_mix16_6 same")

    def test_changed_copies_do_something_else(self):
        by_name = {what: patches for what, patches, _ in CHANGES}
        for what in RUN:
            with self.subTest(what=what):
                said = self.run_words(changed(by_name[what], os.path.join(self.dir, "changed.o")))
                self.assertIn("differs", said, what)
        # the control: other instructions, the same bytes out
        self.assertEqual(self.run_words(changed(STILL_TRUE[1], os.path.join(self.dir, "true.o"))), "500 cases: arm_mix16_3 same, arm_mix16_again same, arm_mix16_6 same")


if __name__ == "__main__":
    unittest.main()
