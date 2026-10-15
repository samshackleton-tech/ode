"""BLAKE3 in Ode: specifications against the reference, and the checker
proving W32 bytes for all inputs -- and rejecting what it must."""
import os
import random
import struct
import subprocess
import sys
import tempfile
import unittest

ROOT = os.path.join(os.path.dirname(__file__), "..")
sys.path.insert(0, ROOT)

from ode import check, produce, word  # noqa: E402
from ode.blake3 import IV, CHUNK_START, CHUNK_END, _compress, _g, blake3  # noqa: E402
from ode.canon import Bytes, Sym, assoc, canonical_bytes, field, hash_of, parse  # noqa: E402
from ode.cli import check_store  # noqa: E402
from ode.store import Reject  # noqa: E402


def load(name):
    with open(os.path.join(ROOT, "examples", name), "rb") as f:
        return parse(f.read())


def words_of(spec, msg):
    n = len(word.inputs_of(spec))
    return list(struct.unpack(f"<{n}I", msg + b"\0" * (4 * n - len(msg))))


def certify(spec, binary, prop="equals-spec-w32-v1", extra=()):
    """A store holding spec, binary, and a certificate for them."""
    tmp = tempfile.mkdtemp()
    with open(os.path.join(tmp, blake3(binary).hex() + ".bin"), "wb") as f:
        f.write(binary)
    cert = assoc("certificate", ("cert", Sym("correctness")),
                 ("property", Sym(prop)), ("spec", produce.put_definition(tmp, spec)),
                 ("binary-hash", Bytes(blake3(binary))), *extra)
    return tmp, cert


class SpecsMatchReferenceTest(unittest.TestCase):
    def test_g(self):
        spec = load("blake3-g.sexp")
        rng = random.Random(1)
        for _ in range(200):
            v = [rng.getrandbits(32) for _ in range(16)]
            x, y = rng.getrandbits(32), rng.getrandbits(32)
            ins = [v[0], v[4], v[8], v[12], x, y]
            _g(v, 0, 4, 8, 12, x, y)
            self.assertEqual(word.run_program(spec, ins), [v[0], v[4], v[8], v[12]])

    def test_compress(self):
        spec, rng = load("blake3-compress.sexp"), random.Random(42)
        for _ in range(20):
            cv = [rng.getrandbits(32) for _ in range(8)]
            block = bytes(rng.getrandbits(8) for _ in range(64))
            counter, blen, flags = rng.getrandbits(40), rng.randrange(65), rng.randrange(16)
            ins = cv + list(struct.unpack("<16I", block)) + [
                counter & 0xFFFFFFFF, counter >> 32, blen, flags]
            self.assertEqual(word.run_program(spec, ins),
                             _compress(cv, block, counter, blen, flags))

    def test_hash_at_committed_and_generated_lengths(self):
        for L in (3, 65):
            spec = load(f"blake3-hash-{L}.sexp")
            msg = bytes(range(L))
            self.assertEqual(word.run_program(spec, words_of(spec, msg)),
                             list(struct.unpack("<8I", blake3(msg))))
        gen = os.path.join(ROOT, "examples", "make_hash_spec.py")
        for L in (0, 1, 64, 1024, 1025, 2048, 3072):  # boundaries, tree, carry
            spec = parse(subprocess.run(["pypy3", gen, str(L)], capture_output=True,
                                        text=True, check=True).stdout)
            msg = bytes((i * 13 + 5) & 0xFF for i in range(L))
            self.assertEqual(word.run_program(spec, words_of(spec, msg)),
                             list(struct.unpack("<8I", blake3(msg))), L)


class CheckerTest(unittest.TestCase):
    def test_proves_and_runs_g(self):
        tmp = tempfile.mkdtemp()
        produce.build(load("blake3-g.sexp"), tmp)
        self.assertEqual(field(check_store(tmp), "verdict"), "accept")

    def test_proves_compress_and_hash65(self):
        for name in ("blake3-compress.sexp", "blake3-hash-65.sexp"):
            tmp = tempfile.mkdtemp()
            produce.build(load(name), tmp)
            self.assertEqual(field(check_store(tmp), "verdict"), "accept", name)

    def test_rejects_mutant_rotation(self):
        spec = load("blake3-g.sexp")
        text = canonical_bytes(spec).decode().replace("(d1 (rotr (xor d a1) 16))",
                                                      "(d1 (rotr (xor d a1) 15))")
        mutant = produce.compile_spec(parse(text))
        tmp, cert = certify(spec, produce.emit_w32(mutant))
        with self.assertRaises(Reject) as cm:
            check.check_certificate(tmp, cert)
        self.assertIn("differs", str(cm.exception))

    def test_rejects_dropped_root_flag(self):
        spec = load("blake3-hash-65.sexp")
        text = canonical_bytes(spec).decode()
        mutant = text.replace(" 0 0 1 10))", " 0 0 1 2))")  # CHUNK_END|ROOT -> CHUNK_END
        self.assertNotEqual(text, mutant)
        tmp, cert = certify(spec, produce.emit_w32(produce.compile_spec(parse(mutant))))
        with self.assertRaises(Reject):
            check.check_certificate(tmp, cert)

    def test_rejects_tampered_binary_file(self):
        tmp = tempfile.mkdtemp()
        result = produce.build(load("blake3-g.sexp"), tmp)
        path = os.path.join(tmp, result["binary_hash"] + ".bin")
        raw = bytearray(open(path, "rb").read())
        raw[20] ^= 1
        open(path, "wb").write(bytes(raw))
        with self.assertRaises(Reject) as cm:
            check_store(tmp)
        self.assertIn("binary file", str(cm.exception))

    def test_rejects_spec_file_under_a_false_name(self):
        tmp = tempfile.mkdtemp()
        result = produce.build(load("blake3-g.sexp"), tmp)
        evil = parse("(spec (name g) (inputs (a b c d x y)) (steps ()) (outputs (a b c d)))")
        open(os.path.join(tmp, result["spec"] + ".sexp"), "wb").write(canonical_bytes(evil))
        with self.assertRaises(Reject):
            check_store(tmp)


class NamesTest(unittest.TestCase):
    """Names in a spec must never collide with names the tools mint."""

    def test_inlining_cannot_capture_the_callers_names(self):
        callee = parse("(spec (name inner) (inputs (a b)) "
                       "(steps ((t0 (add a b)) (t1 (xor t0 a)))) (outputs (t1 t0)))")
        ch = hash_of(callee).hex()
        caller = parse(f"(spec (name outer) (inputs (t0 a)) "
                       f"(defs ((#{ch} {canonical_bytes(callee).decode()}))) "
                       f"(steps (((u v) (call #{ch} a t0)) (t1 (add u v)) "
                       f"((w z) (call #{ch} t1 t0)))) (outputs (w z t1)))")
        program, rng = produce.compile_spec(caller), random.Random(9)
        for _ in range(100):
            v = [rng.getrandbits(32), rng.getrandbits(32)]
            self.assertEqual(word.run_program(caller, v), word.run_program(program, v))
        tmp = tempfile.mkdtemp()
        produce.build(caller, tmp)
        self.assertEqual(field(check_store(tmp), "verdict"), "accept")

    def test_decoder_names_cannot_collide_with_inputs(self):
        spec = parse("(spec (name s) (inputs (s0 s1)) (steps ((r (add s0 s1)))) (outputs (r)))")
        tmp = tempfile.mkdtemp()
        produce.build(spec, tmp)
        self.assertEqual(field(check_store(tmp), "verdict"), "accept")


if __name__ == "__main__":
    unittest.main()


class CallsByCertificateTest(unittest.TestCase):
    """A proved callee is checked once and is one opaque function after."""

    def test_composed_hash_is_small_to_check_and_right(self):
        gen = os.path.join(ROOT, "examples", "make_hash_spec.py")
        spec = parse(subprocess.run(["pypy3", gen, "3072"], capture_output=True,
                                    text=True, check=True).stdout)
        tmp = tempfile.mkdtemp()
        produce.build(spec, tmp)
        from ode.cli import _check
        record, program = _check(tmp)
        self.assertLess(field(record, "dag-nodes"), 2000)  # 50 calls, not 50 bodies
        msg = bytes((i * 7 + 1) & 0xFF for i in range(3072))
        self.assertEqual(check.run(program, words_of(spec, msg)),
                         list(struct.unpack("<8I", blake3(msg))))

    def test_inlined_and_composed_both_prove(self):
        spec = load("blake3-hash-65.sexp")
        tmp, cert = certify(spec, produce.emit_w32(produce.compile_spec(spec)))
        record, _ = check.check_certificate(tmp, cert)  # no calls: expanded
        self.assertGreater(field(record, "dag-nodes"), 10000)
        tmp = tempfile.mkdtemp()
        produce.build(spec, tmp)                          # calls by certificate
        self.assertLess(field(check_store(tmp), "dag-nodes"), 200)
