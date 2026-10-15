"""AArch64: the model (reliance R4) against this CPU, and the checker's teeth.

The model of each instruction form (ode/a64.py) is cross-checked
against the real CPU on random states: the same snippet runs natively
and through the model with concrete inputs, and every output word must
agree. Then the decoder and checker must reject what lies outside the
model and the mutants a producer could ship. Skipped off aarch64 Linux.

Run: pypy3 -m unittest discover -s tests
"""
import os
import platform
import random
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from ode import a64, check, produce, word  # noqa: E402
from ode.blake3 import blake3  # noqa: E402
from ode.canon import Bytes, Sym, assoc, canonical_bytes, field, parse  # noqa: E402
from ode.store import Reject  # noqa: E402
from ode.check import Dag  # noqa: E402

ON_A64 = platform.machine() == "aarch64" and sys.platform.startswith("linux")
ROOT = os.path.join(os.path.dirname(__file__), "..")


def enc(words):
    return b"".join(w.to_bytes(4, "little") for w in words)


def LDR(rt, base, idx): return 0xB9400000 | (idx << 10) | (base << 5) | rt
def STR(rt, base, idx): return 0xB9000000 | (idx << 10) | (base << 5) | rt
def MOVZ(rd, imm, hw): return 0x52800000 | (hw << 21) | (imm << 5) | rd
def MOVK(rd, imm, hw): return 0x72800000 | (hw << 21) | (imm << 5) | rd
def ADD(rd, rn, rm): return 0x0B000000 | (rm << 16) | (rn << 5) | rd
def EOR(rd, rn, rm): return 0x4A000000 | (rm << 16) | (rn << 5) | rd
def ROR(rd, rn, r): return 0x13800000 | (rn << 16) | (r << 10) | (rn << 5) | rd
RET = 0xD65F03C0


def model(code, values, n_out):
    dag = Dag()
    outs = a64.execute(dag, a64.decode(code),
                       lambda i: dag.const(values[i]),
                       {"in": len(values), "out": n_out, "scratch": 4})
    results = []
    for o in outs:
        node = dag.nodes[o]
        assert node[0] == "const", node
        results.append(node[1])
    return results


@unittest.skipUnless(ON_A64, "needs an aarch64 Linux CPU")
class ModelAgainstCpuTest(unittest.TestCase):
    """Reliance R4, checked: each form, random states, model == silicon."""

    def agree(self, code, n_in, n_out, trials=200, seed=0):
        from ode import native
        fn = native.Function(code, n_in, n_out, 4)
        rng = random.Random(seed)
        for _ in range(trials):
            vals = [rng.choice([0, 1, 0xFFFFFFFF, 0x80000000, rng.getrandbits(32)])
                    for _ in range(n_in)]
            self.assertEqual(fn(vals), model(code, vals, n_out), (code.hex(), vals))

    def test_add_and_eor(self):
        for rd, rn, rm in ((3, 4, 5), (17, 3, 3), (9, 9, 10)):
            for op in (ADD, EOR):
                self.agree(enc([LDR(rn, 0, 0), LDR(rm, 0, 1), op(rd, rn, rm),
                                STR(rd, 1, 0), RET]), 2, 1)

    def test_ror_every_count(self):
        for r in range(32):
            self.agree(enc([LDR(4, 0, 0), ROR(5, 4, r), STR(5, 1, 0), RET]),
                       1, 1, trials=40, seed=r)

    def test_movz_movk(self):
        rng = random.Random(5)
        for _ in range(50):
            lo, hi = rng.getrandbits(16), rng.getrandbits(16)
            for code in (enc([MOVZ(6, lo, 0), STR(6, 1, 0), RET]),
                         enc([MOVZ(6, hi, 1), STR(6, 1, 0), RET]),
                         enc([MOVZ(6, lo, 0), MOVK(6, hi, 1), STR(6, 1, 0), RET])):
                self.agree(code, 1, 1, trials=2)

    def test_scratch_round_trip_and_loads(self):
        self.agree(enc([LDR(3, 0, 2), STR(3, 2, 3), LDR(4, 2, 3),
                        STR(4, 1, 1), LDR(5, 0, 0), STR(5, 1, 0), RET]), 3, 2)


class DecoderTeethTest(unittest.TestCase):
    """Anything outside the eight forms, or the contract, is a reject."""

    def rejects(self, words, n_out=1, scratch=4):
        dag = Dag()
        with self.assertRaises(Reject):
            a64.execute(dag, a64.decode(enc(words)), lambda i: dag.var(f"i{i}"),
                        {"in": 2, "out": n_out, "scratch": scratch})

    def test_rejections(self):
        self.rejects([0x14000000, RET])                      # B: a branch
        self.rejects([0xF9400003, RET])                      # LDR X3 (64-bit)
        self.rejects([LDR(3, 0, 0), 0x0B040463, RET])        # ADD with shift
        self.rejects([LDR(3, 0, 0), STR(3, 0, 1), RET])      # store to inputs
        self.rejects([LDR(18, 0, 0), STR(18, 1, 0), RET])    # w18, platform reg
        self.rejects([LDR(0, 0, 0), STR(0, 1, 0), RET])      # clobber base x0
        self.rejects([LDR(3, 0, 2), STR(3, 1, 0), RET])      # in[2] of 2
        self.rejects([LDR(3, 0, 0), STR(3, 2, 4), LDR(3, 0, 0), STR(3, 1, 0), RET])
        self.rejects([LDR(3, 2, 0), STR(3, 1, 0), RET])      # scratch read unwritten
        self.rejects([STR(3, 1, 0), RET])                    # register unwritten
        self.rejects([LDR(3, 0, 0), RET])                    # out[0] never written
        self.rejects([LDR(3, 0, 0), RET, STR(3, 1, 0)])      # RET not last
        self.rejects([LDR(3, 0, 0), LDR(4, 0, 1), 0x13846C65, STR(5, 1, 0), RET])  # EXTR, two regs
        self.rejects([LDR(3, 0, 0), MOVK(3, 1, 1), STR(3, 1, 0), RET])  # MOVK on unknown


class CheckerOnA64Test(unittest.TestCase):
    def setUp(self):
        with open(os.path.join(ROOT, "examples", "blake3-g.sexp"), "rb") as f:
            self.spec = parse(f.read())

    def certify(self, code, scratch):
        tmp = tempfile.mkdtemp()
        with open(os.path.join(tmp, blake3(code).hex() + ".bin"), "wb") as f:
            f.write(code)
        cert = assoc("certificate", ("cert", Sym("correctness")),
                     ("property", Sym("equals-spec-a64-v1")),
                     ("spec", produce.put_definition(tmp, self.spec)),
                     ("binary-hash", Bytes(blake3(code))), ("scratch", scratch))
        return check.check_certificate(tmp, cert)

    def test_honest_g_is_proved(self):
        code, scratch = produce.emit_a64(produce.compile_spec(self.spec))
        record, _ = self.certify(code, scratch)
        self.assertEqual(field(record, "verdict"), "accept")

    def test_mutants_rejected(self):
        code, scratch = produce.emit_a64(produce.compile_spec(self.spec))
        words = [int.from_bytes(code[i:i + 4], "little") for i in range(0, len(code), 4)]
        rors = [i for i, w in enumerate(words) if (w & 0xFFE00000) == 0x13800000]
        adds = [i for i, w in enumerate(words) if (w & 0xFFE0FC00) == 0x0B000000]
        mutants = []
        w = list(words); w[rors[0]] ^= 1 << 10; mutants.append(w)   # rotation off by one
        w = list(words); w[adds[0]] ^= 0x0B000000 ^ 0x4A000000; mutants.append(w)  # add -> eor
        w = list(words); w[-2] = STR(9, 1, 2); mutants.append(w)     # last output dropped
        for m in mutants:
            with self.assertRaises(Reject):
                self.certify(enc(m), scratch)
        with self.assertRaises(Reject):
            self.certify(code, scratch - 1)                     # scratch too small


if __name__ == "__main__":
    unittest.main()
