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
import json, os, platform, random, shutil, subprocess, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path[:0] = [HERE, os.path.join(HERE, "..", "arm64"), os.path.join(HERE, "..", "core"), os.path.join(HERE, "..", "lang")]
import built, lean_verify, odec, prove, statement, table
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
    ("the first call is given a block reaching past the frame's top", [(SIX, 15, "add_of_sp", {"D": "x0", "I": 64})],
     "refused: a called function is given to write what is not whole cells of this function's frame"),
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
        for what, patches in (STILL_TRUE, ("a cell of the frame's write-only block is not zeroed before the first call", [(SIX, 10, "nop", {})])):
            with self.subTest(what=what):
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
        r = subprocess.run([exe], input=self.cases, capture_output=True)
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


PAD_HARNESS = r"""
#include <stdint.h>
#include <stdio.h>
#include <string.h>
void b3l_pad_arm64(uint8_t *block, const uint8_t *src, uint64_t n);
int main(void) {
    uint8_t src[64], guard[16 + 64 + 16], want[64];
    for (int i = 0; i < 64; i++) src[i] = (uint8_t)(0x37 + i * 7);
    for (uint64_t n = 0; n <= 64; n++) {
        memset(guard, 0xA5, sizeof(guard));
        uint8_t *block = guard + 16;
        b3l_pad_arm64(block, src, n);
        for (int g = 0; g < 16; g++) {
            if (guard[g] != 0xA5 || guard[16 + 64 + g] != 0xA5) {
                printf("guard clobbered at n=%llu\n", (unsigned long long)n);
                return 1;
            }
        }
        memset(want, 0, 64);
        memcpy(want, src, n);
        if (memcmp(block, want, 64) != 0) {
            printf("differs at n=%llu\n", (unsigned long long)n);
            return 1;
        }
    }
    printf("65 lengths: b3l_pad_arm64 same\n");
    return 0;
}
"""


class PadArm64(unittest.TestCase):
    """First real BLAKE3 function verified on AArch64: `b3l_pad_arm64` against kcheck/blake3.spec."""

    @classmethod
    def setUpClass(cls):
        cls.dir = tempfile.mkdtemp(prefix="odearmpad-")
        cls.addClassCleanup(shutil.rmtree, cls.dir)
        cls.src_path = os.path.join(ARM, "pad_arm64.ode")
        cls.spec_path = os.path.join(ARM, "pad_arm64.spec")
        with open(os.path.join(HERE, "..", "kcheck", "blake3.spec")) as f:
            b3 = f.read()
        with open(cls.spec_path) as f:
            cls.spec = b3 + "\n" + f.read()
        with open(cls.src_path) as f:
            cls.src = f.read()
        cls.obj = os.path.join(cls.dir, "pad_arm64.o")
        odec.build(cls.src_path, "pad", cls.obj)
        cls.places = odec.places(cls.src_path, "pad")

    @unittest.skipUnless(LAKE, "Lean's lake is not installed")
    def test_b3l_pad_arm64_verified_and_false_mutants_refused(self):
        built.built("odeverify")
        st = os.path.join(self.dir, "pad.statement")
        pf = os.path.join(self.dir, "pad.proof")
        nums = prove.prove(self.spec, [(self.obj, "b3l_pad_arm64", self.places)], st, pf)
        self.assertIn("b3l_pad_arm64", nums)
        self.assertEqual(lean_verify.verify(self.spec, [(self.obj, "b3l_pad_arm64")], pf), (True, "shown"))

        # Negative control 1: zero-fill writes 1 instead of 0 -> refused.
        bad1_ode = os.path.join(self.dir, "bad1.ode")
        bad1_obj = os.path.join(self.dir, "bad1.o")
        self.assertEqual(self.src.count("  bytex := 0\n"), 1)
        with open(bad1_ode, "w") as f:
            f.write(self.src.replace("  bytex := 0\n", "  bytex := 1\n", 1))
        odec.build(bad1_ode, "pad", bad1_obj)
        ok, _ = lean_verify.verify(self.spec, [(bad1_obj, "b3l_pad_arm64")], pf)
        self.assertFalse(ok)

        # Negative control 2: contract drops `trace depends on n` -> refused at branch on `n`.
        bad_spec = self.spec.replace("    trace depends on n\n", "")
        ok, said = lean_verify.verify(bad_spec, [(self.obj, "b3l_pad_arm64")], pf)
        self.assertFalse(ok)
        self.assertIn("kept out of the trace", said)

        # Negative control 3: branch reversed (`b.lo @zero` instead of `b.hs @zero`) -> out-of-bounds / wrong value refused.
        bad3_ode = os.path.join(self.dir, "bad3.ode")
        bad3_obj = os.path.join(self.dir, "bad3.o")
        self.assertEqual(self.src.count("  b.hs @zero\n"), 1)
        with open(bad3_ode, "w") as f:
            f.write(self.src.replace("  b.hs @zero\n", "  b.lo @zero\n", 1))
        odec.build(bad3_ode, "pad", bad3_obj)
        ok, _ = lean_verify.verify(self.spec, [(bad3_obj, "b3l_pad_arm64")], pf)
        self.assertFalse(ok)

    @unittest.skipUnless(ARM_MACHINE and shutil.which("clang"), "an AArch64 processor and clang are needed")
    def test_b3l_pad_arm64_runs_on_hardware(self):
        words, _ = aobj.words(self.obj, "b3l_pad_arm64")
        lines = ["#ifdef __APPLE__", "#define SYM(x) _##x", "#else", "#define SYM(x) x", "#endif",
                 ".text", ".p2align 2", ".globl SYM(b3l_pad_arm64)", "SYM(b3l_pad_arm64):"]
        for w in words:
            lines.append(f"    .long 0x{int.from_bytes(w, 'little'):08x}")
        asm_p = os.path.join(self.dir, "pad.S")
        c_p = os.path.join(self.dir, "pad_harness.c")
        exe_p = os.path.join(self.dir, "pad_run")
        with open(asm_p, "w") as f: f.write("\n".join(lines) + "\n")
        with open(c_p, "w") as f: f.write(PAD_HARNESS)
        subprocess.run(["clang", "-O1", "-o", exe_p, c_p, asm_p], check=True, capture_output=True)
        r = subprocess.run([exe_p], capture_output=True, text=True, check=True)
        self.assertEqual(r.stdout.strip(), "65 lengths: b3l_pad_arm64 same")


COMPRESS_HARNESS = r"""
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void b3l_pad_arm64(uint8_t *block, const uint8_t *src, uint64_t n);
void blake3_servil_compress_in_place_arm64(uint8_t *h, const uint8_t *m, uint64_t length, uint64_t t, uint64_t flags);

static const uint32_t IV_U32[8] = {
    0x6A09E667u, 0xBB67AE85u, 0x3C6EF372u, 0xA54FF53Au,
    0x510E527Fu, 0x9B05688Cu, 0x1F83D9ABu, 0x5BE0CD19u,
};

static int call_compress_guarded(uint8_t h[32], const uint8_t m[64], uint64_t len, uint64_t t, uint32_t flg) {
    uint8_t guard[16 + 32 + 16];
    memset(guard, 0x5A, sizeof(guard));
    memcpy(guard + 16, h, 32);
    /* Pass non-zero upper 32 bits in flags to exercise the `flags: low word` contract. */
    uint64_t noisy_flags = 0xDEADBEEF00000000ULL | (uint64_t)flg;
    blake3_servil_compress_in_place_arm64(guard + 16, m, len, t, noisy_flags);
    for (int i = 0; i < 16; i++) {
        if (guard[i] != 0x5A || guard[16 + 32 + i] != 0x5A) return 0;
    }
    memcpy(h, guard + 16, 32);
    return 1;
}

static int compress_chunk(uint8_t out_cv[32], const uint8_t key[32], const uint8_t *data, size_t len,
                          uint64_t chunk_idx, uint32_t base_flags, int is_root) {
    uint8_t cv[32], blk[64];
    memcpy(cv, key, 32);
    if (len == 0) {
        b3l_pad_arm64(blk, data, 0);
        uint32_t f = base_flags | 1u | 2u | (is_root ? 8u : 0u);
        if (!call_compress_guarded(cv, blk, 0, chunk_idx, f)) return 0;
    } else {
        size_t pos = 0;
        while (pos + 64 < len) {
            uint32_t f = base_flags | (pos == 0 ? 1u : 0u);
            if (!call_compress_guarded(cv, data + pos, 64, chunk_idx, f)) return 0;
            pos += 64;
        }
        size_t rem = len - pos;
        b3l_pad_arm64(blk, data + pos, rem);
        uint32_t f = base_flags | (pos == 0 ? 1u : 0u) | 2u | (is_root ? 8u : 0u);
        if (!call_compress_guarded(cv, blk, rem, chunk_idx, f)) return 0;
    }
    memcpy(out_cv, cv, 32);
    return 1;
}

static int blake3_hash_32(uint8_t out[32], const uint8_t key[32], uint32_t base_flags,
                          const uint8_t *msg, size_t len) {
    if (len <= 1024) {
        return compress_chunk(out, key, msg, len, 0, base_flags, 1);
    }
    uint8_t stack[54][32];
    int sp = 0;
    size_t total_chunks = (len + 1023) / 1024;
    for (size_t c = 0; c + 1 < total_chunks; c++) {
        uint8_t cv[32];
        if (!compress_chunk(cv, key, msg + c * 1024, 1024, (uint64_t)c, base_flags, 0)) return 0;
        size_t n = c + 1;
        while ((n & 1) == 0) {
            uint8_t blk[64], pcv[32];
            sp--;
            memcpy(blk, stack[sp], 32);
            memcpy(blk + 32, cv, 32);
            memcpy(pcv, key, 32);
            if (!call_compress_guarded(pcv, blk, 64, 0, base_flags | 4u)) return 0;
            memcpy(cv, pcv, 32);
            n >>= 1;
        }
        memcpy(stack[sp++], cv, 32);
    }
    size_t last = total_chunks - 1;
    uint8_t cv[32];
    if (!compress_chunk(cv, key, msg + last * 1024, len - last * 1024, (uint64_t)last, base_flags, 0)) return 0;
    while (sp > 0) {
        uint8_t blk[64], pcv[32];
        sp--;
        memcpy(blk, stack[sp], 32);
        memcpy(blk + 32, cv, 32);
        memcpy(pcv, key, 32);
        uint32_t f = base_flags | 4u | (sp == 0 ? 8u : 0u);
        if (!call_compress_guarded(pcv, blk, 64, 0, f)) return 0;
        memcpy(cv, pcv, 32);
    }
    memcpy(out, cv, 32);
    return 1;
}

static void hex32(const uint8_t b[32], char out[65]) {
    static const char H[] = "0123456789abcdef";
    for (int i = 0; i < 32; i++) {
        out[2 * i] = H[b[i] >> 4];
        out[2 * i + 1] = H[b[i] & 15];
    }
    out[64] = '\0';
}

int main(void) {
    uint8_t iv[32];
    for (int i = 0; i < 8; i++) {
        iv[4 * i + 0] = (uint8_t)(IV_U32[i] & 0xffu);
        iv[4 * i + 1] = (uint8_t)((IV_U32[i] >> 8) & 0xffu);
        iv[4 * i + 2] = (uint8_t)((IV_U32[i] >> 16) & 0xffu);
        iv[4 * i + 3] = (uint8_t)((IV_U32[i] >> 24) & 0xffu);
    }
    const uint8_t keyed_key[32] = "whats the Elvish word for friend";
    size_t max_len = 102400;
    uint8_t *msg = (uint8_t *)malloc(max_len);
    for (size_t i = 0; i < max_len; i++) msg[i] = (uint8_t)(i % 251);
    size_t len;
    int count = 0;
    while (scanf("%zu", &len) == 1) {
        uint8_t h1[32], h2[32];
        char s1[65], s2[65];
        if (!blake3_hash_32(h1, iv, 0u, msg, len)) { printf("guard fail hash %zu\n", len); return 2; }
        if (!blake3_hash_32(h2, keyed_key, 16u, msg, len)) { printf("guard fail keyed %zu\n", len); return 2; }
        hex32(h1, s1);
        hex32(h2, s2);
        printf("%zu %s %s\n", len, s1, s2);
        count++;
    }
    free(msg);
    return 0;
}
"""


class CompressArm64(unittest.TestCase):
    """AArch64 NEON one-block BLAKE3 compression kernel (`blake3_servil_compress_in_place_arm64`)."""

    SYM = "blake3_servil_compress_in_place_arm64"
    KEPT_PROOF = os.path.join(HERE, "proofs", "blake3_servil_compress_in_place_arm64.proof")

    @classmethod
    def setUpClass(cls):
        cls.dir = tempfile.mkdtemp(prefix="odearmcomp-")
        cls.addClassCleanup(shutil.rmtree, cls.dir)
        cls.src_path = os.path.join(ARM, "compress_arm64.ode")
        cls.spec_path = os.path.join(ARM, "compress_arm64.spec")
        with open(os.path.join(HERE, "..", "kcheck", "blake3.spec")) as f:
            cls.b3_spec = f.read()
        with open(cls.spec_path) as f:
            cls.contract_spec = f.read()
        cls.spec = cls.b3_spec + "\n" + cls.contract_spec
        with open(cls.src_path) as f:
            cls.src = f.read()
        cls.obj = os.path.join(cls.dir, "compress_arm64.o")
        odec.build(cls.src_path, "compress1_arm64", cls.obj)
        cls.pad_obj = os.path.join(cls.dir, "pad_arm64.o")
        odec.build(os.path.join(ARM, "pad_arm64.ode"), "pad", cls.pad_obj)

    def test_advice_budget_passes_on_both_arm64_profiles(self):
        tool = os.path.join(HERE, "..", "lang", "ode_tool.py")
        for arch in ("apple_m", "ampere1"):
            r = subprocess.run(
                [sys.executable, tool, "advise", "--arch", arch, self.src_path],
                capture_output=True, text=True, check=True,
            )
            self.assertIn("116 instructions, 464 bytes", r.stdout)
            self.assertNotIn("budget exceeded", r.stdout)

    @unittest.skipUnless(LAKE, "Lean's lake is not installed")
    def test_compress_arm64_shown_and_matches_kept_proof(self):
        built.built("odeverify")
        self.assertEqual(lean_verify.verify(self.spec, [(self.obj, self.SYM)], self.KEPT_PROOF), (True, "shown"))
        st = os.path.join(self.dir, "comp.statement")
        pf = os.path.join(self.dir, "comp.proof")
        nums = prove.prove(self.spec, [(self.obj, self.SYM, "")], st, pf)
        self.assertIn(self.SYM, nums)
        with open(self.KEPT_PROOF) as f, open(pf) as g:
            self.assertEqual(f.read(), g.read())

    @unittest.skipUnless(LAKE, "Lean's lake is not installed")
    def test_compress_arm64_refuses_wrong_spec_contract_and_code(self):
        built.built("odeverify")
        spec_muts = [
            ("rotation 16 -> 15", ">>> 16", ">>> 15"),
            ("rotation 12 -> 13", ">>> 12", ">>> 13"),
            ("rotation 8 -> 9", ">>> 8", ">>> 9"),
            ("rotation 7 -> 9", ">>> 7", ">>> 9"),
            ("IV[0] changed", "0x6A09E667", "0x6A09E668"),
            ("counter halves swapped", "lo(t), hi(t)", "hi(t), lo(t)"),
            ("length and flags swapped", "word(length), word(flags)", "word(flags), word(length)"),
            ("six rounds", "[s[7][i] ^ s[7][i + 8] for i in 0..8]", "[s[6][i] ^ s[6][i + 8] for i in 0..8]"),
        ]
        for label, old, new in spec_muts:
            with self.subTest(spec_mut=label):
                self.assertEqual(self.b3_spec.count(old), 1, label)
                bad_spec = self.b3_spec.replace(old, new, 1) + "\n" + self.contract_spec
                ok, _ = lean_verify.verify(bad_spec, [(self.obj, self.SYM)], self.KEPT_PROOF)
                self.assertFalse(ok, label)

        contract_muts = [
            ("contract swaps length and flags", "compress(h, m, t, length, flags)", "compress(h, m, t, flags, length)"),
            ("contract omits word bound on length", "length: word", "length: number"),
            ("contract omits counter type on t", "t: counter", "t: number"),
            ("contract swaps h and m", "compress(h, m, t, length, flags)", "compress(m, h, t, length, flags)"),
        ]
        for label, old, new in contract_muts:
            with self.subTest(contract_mut=label):
                self.assertEqual(self.contract_spec.count(old), 1, label)
                bad_spec = self.b3_spec + "\n" + self.contract_spec.replace(old, new, 1)
                ok, _ = lean_verify.verify(bad_spec, [(self.obj, self.SYM)], self.KEPT_PROOF)
                self.assertFalse(ok, label)

        code_muts = [
            ("wrong shift 12 -> 11", "  ushr t.4s, b.4s, 12\n", "  ushr t.4s, b.4s, 11\n", ""),
            ("dropped rev32", "  rev32 d.8h, d.8h\n", "  nop\n", ""),
            ("six rounds", "  rounds := 7\n", "  rounds := 6\n", ""),
            ("wrong IV[0] low half", "  tmp := 0xE667\n", "  tmp := 0xE668\n", ""),
            ("wrong flags shift", "  lsl tmp, flg, 32\n", "  lsl tmp, flg, 31\n", ""),
            ("wrong diagonal ext", "  ext v0.16b, v0.16b, v0.16b, 12\n", "  ext v0.16b, v0.16b, v0.16b, 4\n", ""),
            ("missing final xor", "  eor v0.16b, v0.16b, v2.16b\n", "  nop\n", ""),
            ("branch on hidden flags", "  rounds := 7\n", "  cmp flg, 0\n  b.eq @done\n  rounds := 7\n", "kept out of the trace"),
        ]
        for idx, (label, old, new, want) in enumerate(code_muts):
            with self.subTest(code_mut=label):
                self.assertEqual(self.src.count(old), 1, label)
                bad_ode = os.path.join(self.dir, f"bad_comp_{idx}.ode")
                bad_obj = os.path.join(self.dir, f"bad_comp_{idx}.o")
                with open(bad_ode, "w") as f:
                    f.write(self.src.replace(old, new, 1))
                odec.build(bad_ode, "compress1_arm64", bad_obj)
                ok, said = lean_verify.verify(self.spec, [(bad_obj, self.SYM)], self.KEPT_PROOF)
                self.assertFalse(ok, label)
                if want:
                    self.assertIn(want, said, label)

    @unittest.skipUnless(ARM_MACHINE and shutil.which("clang"), "an AArch64 processor and clang are needed")
    def test_compress_arm64_matches_all_official_blake3_vectors_on_hardware(self):
        tv_path = os.path.join(HERE, "..", "reference", "blake3-servil", "test_vectors", "test_vectors.json")
        with open(tv_path) as f:
            cases = json.load(f)["cases"]
        self.assertEqual(len(cases), 35)

        def run_with(comp_obj, tag):
            lines = ["#ifdef __APPLE__", "#define SYM(x) _##x", "#else", "#define SYM(x) x", "#endif", ".text", ".p2align 2"]
            for o_path, sym in ((self.pad_obj, "b3l_pad_arm64"), (comp_obj, self.SYM)):
                words, _ = aobj.words(o_path, sym)
                lines += [f".globl SYM({sym})", f"SYM({sym}):"]
                for w in words:
                    lines.append(f"    .long 0x{int.from_bytes(w, 'little'):08x}")
            asm_p = os.path.join(self.dir, f"b3_{tag}.S")
            c_p = os.path.join(self.dir, f"b3_{tag}.c")
            exe_p = os.path.join(self.dir, f"b3_{tag}")
            with open(asm_p, "w") as f: f.write("\n".join(lines) + "\n")
            with open(c_p, "w") as f: f.write(COMPRESS_HARNESS)
            subprocess.run(["clang", "-O1", "-o", exe_p, c_p, asm_p], check=True, capture_output=True)
            inp = "\n".join(str(c["input_len"]) for c in cases) + "\n"
            r = subprocess.run([exe_p], input=inp, capture_output=True, text=True, check=True)
            got = {}
            for ln in r.stdout.strip().splitlines():
                n_s, h1, h2 = ln.split()
                got[int(n_s)] = (h1, h2)
            return got

        got = run_with(self.obj, "good")
        for c in cases:
            n = c["input_len"]
            h1, h2 = got[n]
            self.assertEqual(h1, c["hash"][:64], f"hash differs at len={n}")
            self.assertEqual(h2, c["keyed_hash"][:64], f"keyed_hash differs at len={n}")

        # Hardware negative control: 6 rounds produces wrong digests on the real processor.
        bad_ode = os.path.join(self.dir, "bad6.ode")
        bad_obj = os.path.join(self.dir, "bad6.o")
        with open(bad_ode, "w") as f:
            f.write(self.src.replace("  rounds := 7\n", "  rounds := 6\n", 1))
        odec.build(bad_ode, "compress1_arm64", bad_obj)
        bad_got = run_with(bad_obj, "bad6")
        self.assertNotEqual(bad_got[0][0], cases[0]["hash"][:64])


if __name__ == "__main__":
    unittest.main()
