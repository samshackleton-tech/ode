#!/usr/bin/env python3
"""The library's wide kernels, by kfn.py with kwide.py's prover (until November 17, 2026 by a verifier and a
prover of their own, kloop.py; the cases are those): a proof is found and checked for each, and wrong kernels
and wrong proofs are refused. (The changes of the rounds, and the controls of the frame, of a sum that
doubles and of a changed specification, were asked of kcheck.py's machine too until November 18, 2026.)

    python3 test_kloop.py"""
import copy, os, shutil, subprocess, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "reference", "blake3-servil"))
sys.path.insert(0, HERE)
import kfn, kterms, kwide
from test_kdecode import assemble

SYMBOL = {name: "blake3_servil_avx512_" + name for name in ("k32", "p32", "p16")}
START = {"k32": SYMBOL["k32"], "p32": SYMBOL["k32"], "p16": SYMBOL["p16"]}          # the 32-lane kernel has two ways in


class kloop:
    """What these tests ask, of kfn.py and of kwide.py."""
    @staticmethod
    def load(obj, name): return kfn.load_from(obj, SYMBOL[name], START[name])
    @staticmethod
    def find(rows, data, name, entry):
        kfn.CONTRACTS.clear()
        return kwide.find(rows, data, SYMBOL[name], entry)
    @staticmethod
    def check(rows, data, name, proof, entry):
        kfn.CONTRACTS.clear()
        return kfn.check(rows, None, proof=proof, symbol=SYMBOL[name], entry=entry, data=data)

# changes of the loop over blocks and of the flags' bytes, which a kernel for one block count does not show
LOOP_MUTANTS = [
    ("the end flag a block early", ".cmp 64 (.reg .r13) (.imm 0x1)", ".cmp 64 (.reg .r13) (.imm 0x2)"),
    ("the start byte read from the end byte", ".shr32 .rdx 8", ".shr32 .rdx 16"),
    ("the end byte read from the start byte", ".shr32 .rcx 16", ".shr32 .rcx 8"),
    ("the last length read from the end byte", ".shr32 .rdx 24", ".shr32 .rdx 16"),
    ("the start flag on every block but the first", ".jne 0x10846", ".je 0x10846"),
    ("every second block skipped", ".add 64 (.reg .r14) (.imm 0x40)", ".add 64 (.reg .r14) (.imm 0x80)"),
    ("the count of blocks left never falls", ".dec64 .r13", ".nop"),
    ("a block length of 65", ".mov 32 (.reg .rdx) (.imm 0x40)", ".mov 32 (.reg .rdx) (.imm 0x41)"),
    ("the loop entered past its first instruction", ".jne 0x10133", ".jne 0x1013B"),
    ("the loop left a block early", ".jne 0x10133", ".nop"),
]
# changes of the rounds, the stores, the frame and the flags
MUTANTS = [("a rotation 12 -> 13", ".zprord 4 4 12", ".zprord 4 4 13"), ("a rotation 7 -> 8, second half", ".zprord 12 12 7", ".zprord 12 12 8"),
           ("an xor's source", ".zpxord 20 20 0", ".zpxord 20 20 1"), ("the mask of the carry", ".zpaddd_k 5 1 1 4", ".zpaddd_k 5 2 1 4"),
           ("the comparison's operands", ".zpcmpud 1 2 0 1", ".zpcmpud 1 0 2 1"), ("a message word's offset", ".zpadddm 9 9 .rsi .rcx 0x400", ".zpadddm 9 9 .rsi .rcx 0x0"),
           ("an output store's offset", ".zstore false .r15 0x100 4", ".zstore false .r15 0x140 4"), ("a transpose's shuffle", ".zshufi32x4 30 31 18 136", ".zshufi32x4 30 31 18 221"),
           ("the end flag's shift", ".shr32 .rcx 16", ".shr32 .rcx 8"), ("the start flag left out", ".or 32 (.reg .rax) (.reg .rdx)", ".nop"),
           ("the feed-forward's register", ".zpxord 3 3 19", ".zpxord 3 3 18"), ("a callee-saved register not restored", ".pop .r13", ".pop .rax"),
           ("a store below the frame", ".zstore true .rsp 0x900 15", ".zstore true .rsp 0x940 15"), ("the block offset's step", ".add 64 (.reg .r14) (.imm 0x40)", ".add 64 (.reg .r14) (.imm 0x80)")]


class Kloop(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.dir = tempfile.mkdtemp(prefix="kloop-")
        cls.obj = os.path.join(cls.dir, "k.o")
        assemble(os.path.join(ROOT, "c", "blake3_avx512_32.S"), cls.obj)
        cls.k32 = kloop.load(cls.obj, "k32")
        cls.proof = kloop.find(*cls.k32[:2], "k32", cls.k32[2])

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.dir)

    def test_a_proof_is_found_and_checked_for_each_kernel(self):
        for name, place in (("k32", 0x133), ("p32", 0x133), ("p16", 0x91)):
            rows, data, entry = kloop.load(self.obj, name)
            proof = kloop.find(rows, data, name, entry)
            self.assertEqual(proof["place"], place, name)
            done = kloop.check(rows, data, name, proof, entry)
            self.assertEqual((done["place"], done["return"]), (1, 2), name)          # the step: one path back to the place, one to the return; and the return after one block

    def changed(self, old, new):
        rows, data, entry = self.k32
        hits = [k for k, r in enumerate(rows) if r[2] == old]
        self.assertTrue(hits, f"no instruction `{old}`")
        rows = list(rows); rows[hits[0]] = (rows[hits[0]][0], rows[hits[0]][1], new)
        return rows, data, entry

    def test_no_proof_is_found_for_a_changed_kernel_and_the_true_proof_is_refused_on_it(self):
        for label, old, new in LOOP_MUTANTS + MUTANTS:
            rows, data, entry = self.changed(old, new)
            with self.assertRaises(kterms.Fail, msg="the prover on: " + label):
                kloop.find(rows, data, "k32", entry)
            with self.assertRaises(kterms.Fail, msg="the verifier with the true proof on: " + label):
                kloop.check(rows, data, "k32", self.proof, entry)
        rows, data, entry = self.k32
        bad = bytearray(data); bad[0xC0 + 64 + 4] ^= 0x40           # one entry of the message schedule
        with self.assertRaises(kterms.Fail):
            kloop.find(rows, bytes(bad), "k32", entry)

    def test_a_wrong_proof_is_refused_on_the_true_kernel(self):
        rows, data, entry = self.k32
        def wrong(change):
            proof = copy.deepcopy(self.proof); change(proof); return proof
        def swap(p): p["vectors"]["0"], p["vectors"]["1"] = p["vectors"]["1"], p["vectors"]["0"]
        for label, change in (("the place moved", lambda p: p.update(place=p["place"] + 8)),
                              ("the block offset said to move by 128", lambda p: p["registers"]["r14"]["lin"].update(b=128)),
                              ("the count said not to fall", lambda p: p["registers"]["r13"]["lin"].update(b=0)),
                              ("two words of the state exchanged", swap),
                              ("a state register not named", lambda p: p["vectors"].pop("5")),
                              ("a counter's cell not named", lambda p: p["frame"].pop("2048")),
                              ("the inputs' table not named", lambda p: p["registers"].pop("r12"))):
            with self.assertRaises(kterms.Fail, msg=label):
                kloop.check(rows, data, "k32", wrong(change), entry)

    def test_a_changed_contract_refuses_the_true_kernel(self):
        # the kernels' contracts are text in blake3.spec
        import kspec, ode
        true = kspec.SPEC
        text = ode.source()
        k32 = "contract blake3_servil_avx512_k32(inputs: 32 inputs, n: number, key: cv, t: counter, packed: bytes flags start end length, out: 32 cvs) {\n    requires n >= 1\n    requires no_overlap(inputs, key, out)\n    ensures out[i] = chunk(key, t + i, flags, start, end, length, n, inputs[i]) for i in 0..32"
        self.assertEqual(text.count(k32), 1)
        rows, data, entry = self.k32
        try:
            for old, new in (("t + i", "t"), ("t + i", "t + i + 1"), ("flags, start, end, length", "flags, end, start, length"), ("inputs[i])", "inputs[31 - i])"),
                             ("requires n >= 1", "requires n >= 0"), ("for i in 0..32", "for i in 0..16"), ("bytes flags start end length", "bytes start flags end length"),
                             ("chunk(key,", "chunk(key[0..4] ++ key[0..4],"), ("32 inputs", "16 inputs")):
                self.assertEqual(k32.count(old), 1, old)
                kspec.SPEC = ode.Spec(text.replace(k32, k32.replace(old, new)))
                with self.assertRaises(kterms.Fail, msg=new):
                    kloop.find(rows, data, "k32", entry)
        finally:
            kspec.SPEC = true

    def test_a_frame_that_is_not_whole_cells_is_refused(self):
        # found by kflip.py: `sub rsp, 0x101` was accepted by the first machine, and its aligned stores fault on a processor
        rows, data, entry = kloop.load(self.obj, "p16")
        k = next(k for k, r in enumerate(rows) if r[2] == ".sub 64 (.reg .rsp) (.imm 0x100)")
        for size in ("0x101", "0x120", "0xC0"):
            changed = list(rows); changed[k] = (rows[k][0], rows[k][1], f".sub 64 (.reg .rsp) (.imm {size})")
            with self.assertRaises(kterms.Fail, msg=size):
                kloop.find(changed, data, "p16", entry)

    def test_a_sum_that_doubles_is_stopped(self):
        # found by kflip.py: a changed kernel that adds a register to itself in a loop ran out of memory
        T = kterms.Terms()
        x = T.add(T.var("key", 0), T.var("key", 1))
        with self.assertRaises(kterms.Fail):
            for _ in range(12): x = T.add(x, x)

    def test_a_changed_specification_refuses_the_true_kernel(self):
        # the specification is blake3.spec (test_ode.py: it gives the official vectors): one change of its text,
        # and the kernel that met it does not
        import kspec, ode
        true = kspec.SPEC
        text = ode.source()
        rows, data, entry = kloop.load(self.obj, "p16")
        try:
            for old, new in (("(b1 ^ c2) >>> 7", "(b1 ^ c2) >>> 8"), ("if b == n - 1 then length else 64,", "63,"), ("[s[7][i] ^ s[7][i + 8] for i in 0..8]", "[s[7][i + 8] ^ s[7][i] ^ s[7][i] for i in 0..8]")):
                self.assertEqual(text.count(old), 1, old)
                kspec.SPEC = ode.Spec(text.replace(old, new))
                with self.assertRaises(kterms.Fail, msg=old):
                    kloop.find(rows, data, "p16", entry)
        finally:
            kspec.SPEC = true

    def test_the_other_entry_is_refused_with_this_ones_specification(self):
        rows, data, entry = self.k32
        p32 = kloop.load(self.obj, "p32")[2]
        with self.assertRaises(kterms.Fail):
            kloop.find(rows, data, "k32", p32)           # the entry that does not count, the counting specification
        with self.assertRaises(kterms.Fail):
            kloop.find(rows, data, "p32", entry)


if __name__ == "__main__":
    unittest.main()
