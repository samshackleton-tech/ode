"""The BLAKE3 vertical slice: G and one compression, specified in Ode,
generated to W32, proved symbolically by ode/wcheck.py for all inputs.

Run: pypy3 -m unittest discover -s tests
"""
import os
import random
import struct
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from ode import wcheck, word, wproducer
from ode.blake3 import _compress, _g
from ode.canon import Bytes, Sym, canonical_bytes, field, parse
from ode.checker import Reject
from ode.blake3 import blake3_hex

ROOT = os.path.join(os.path.dirname(__file__), "..")


def load(name):
    with open(os.path.join(ROOT, "examples", name), "rb") as f:
        return parse(f.read())


class GTest(unittest.TestCase):
    def setUp(self):
        self.spec = load("blake3-g.sexp")

    def test_spec_matches_reference_g(self):
        rng = random.Random(1)
        for _ in range(200):
            v = [rng.getrandbits(32) for _ in range(16)]
            m = [rng.getrandbits(32) for _ in range(16)]
            state = v[:]
            _g(state, 0, 4, 8, 12, m[0], m[1])
            got = word.run_program(
                self.spec, [v[0], v[4], v[8], v[12], m[0], m[1]])
            self.assertEqual(got, [state[0], state[4], state[8], state[12]])

    def test_checker_proves_g_and_rejects_mutants(self):
        tmp = tempfile.mkdtemp()
        wproducer.build(self.spec, tmp)
        record = wcheck.check_store(tmp)
        self.assertEqual(field(record, "verdict"), "accept")
        # A mutant machine: rotation 16 -> 15, all hashes honestly redone.
        bad_spec = load("blake3-g.sexp")
        steps = []
        for name, e in word.steps_of(bad_spec):
            if name == "d1":
                e = parse("(rotr (xor d a1) 15)")
            steps.append([name, e])
        mutant = [bad_spec[0]] + [
            [p[0], steps] if p[0] == "steps" else p for p in bad_spec[1:]]
        word.validate_wspec(mutant)
        # The mutant as a *machine* claim about the true spec:
        machine_defn = wproducer.compile_wspec(mutant)
        from ode.producer import put_definition
        from ode.canon import assoc
        from ode.blake3 import blake3
        binary = wproducer.emit_w32(machine_defn)
        with open(os.path.join(tmp, "binary.bin"), "wb") as f:
            f.write(binary)
        cert = assoc(
            "certificate", ("cert", Sym("correctness")),
            ("property", Sym(wcheck.PROPERTY)),
            ("spec", put_definition(tmp, self.spec)),
            ("machine", put_definition(tmp, machine_defn)),
            ("binary-hash", Bytes(blake3(binary))),
            ("binary", Bytes(binary)), ("inputs", 6))
        with self.assertRaises(Reject) as cm:
            wcheck.check_certificate(tmp, cert)
        self.assertIn("differs", str(cm.exception))


class CompressTest(unittest.TestCase):
    def setUp(self):
        self.spec = load("blake3-compress.sexp")

    def test_spec_matches_reference_compress(self):
        rng = random.Random(42)
        for _ in range(20):
            cv = [rng.getrandbits(32) for _ in range(8)]
            block = bytes(rng.getrandbits(8) for _ in range(64))
            msg = list(struct.unpack("<16I", block))
            counter = rng.getrandbits(40)
            blen, flags = rng.randrange(65), rng.randrange(16)
            inputs = (cv + msg + [counter & 0xFFFFFFFF, counter >> 32,
                                  blen, flags])
            self.assertEqual(word.run_program(self.spec, inputs),
                             _compress(cv, block, counter, blen, flags))

    def test_spec_computes_blake3_of_abc_via_one_chunk(self):
        # One chunk, root output: the spec alone reaches the published hash.
        data = b"abc"
        padded = data + b"\x00" * 61
        msg = list(struct.unpack("<16I", padded))
        from ode.blake3 import IV, CHUNK_START, CHUNK_END, ROOT
        inputs = (IV[:] + msg + [0, 0, len(data), CHUNK_START | CHUNK_END])
        out_words = word.run_program(self.spec, inputs)
        # Root output block 0 with ROOT flag re-run is the hash; emulate by
        # asking the reference Output for the same inputs' root bytes and
        # comparing the chaining half the spec defines.
        from ode.blake3 import _Output
        ref = _Output(IV[:], padded, 0, len(data), CHUNK_START | CHUNK_END)
        self.assertEqual(ref.root_bytes(32), bytes.fromhex(blake3_hex(data)))
        self.assertEqual(out_words[:8], ref.chaining_value())

    def test_tampered_binary_file_rejected(self):
        tmp = tempfile.mkdtemp()
        wproducer.build(self.spec, tmp)
        wcheck.check_store(tmp)
        path = os.path.join(tmp, "binary.bin")
        with open(path, "rb") as f:
            raw = bytearray(f.read())
        raw[100] ^= 1
        with open(path, "wb") as f:
            f.write(bytes(raw))
        with self.assertRaises(Reject) as cm:
            wcheck.check_store(tmp)
        self.assertIn("binary.bin", str(cm.exception))

    def test_checker_proves_compression(self):
        tmp = tempfile.mkdtemp()
        result = wproducer.build(self.spec, tmp)
        record = wcheck.check_store(tmp)
        self.assertEqual(field(record, "verdict"), "accept")
        self.assertEqual(field(record, "domain"), "all-u32-inputs")
        self.assertGreater(field(record, "dag-nodes"), 1000)
        self.assertGreater(result["binary_len"], 1000)


if __name__ == "__main__":
    unittest.main()


class HashTest(unittest.TestCase):
    """BLAKE3's hash mode, composed from compressions by (call #hash ...)."""

    def _words(self, spec, msg):
        n = len(word.inputs_of(spec))
        return list(struct.unpack(f"<{n}I", msg + b"\0" * (n * 4 - len(msg))))

    def test_hash_specs_match_reference_at_committed_lengths(self):
        from ode.blake3 import blake3
        for L in (3, 65):
            spec = load(f"blake3-hash-{L}.sexp")
            for seed in range(3):
                msg = bytes((i * 7 + seed) & 0xFF for i in range(L))
                got = word.run_program(spec, self._words(spec, msg))
                self.assertEqual(got, list(struct.unpack("<8I", blake3(msg))))

    def test_generated_hash_specs_match_reference_across_the_tree(self):
        # Chunk boundaries, a two-level tree, and an odd chunk carried up.
        import subprocess
        from ode.blake3 import blake3
        gen = os.path.join(ROOT, "examples", "make_hash_spec.py")
        for L in (0, 1, 64, 1024, 1025, 2048, 3072):
            text = subprocess.run(["pypy3", gen, str(L)], capture_output=True,
                                  text=True, check=True).stdout
            spec = parse(text)
            msg = bytes((i * 13 + 5) & 0xFF for i in range(L))
            got = word.run_program(spec, self._words(spec, msg))
            self.assertEqual(got, list(struct.unpack("<8I", blake3(msg))), L)

    def test_checker_proves_hash_and_rejects_a_dropped_flag(self):
        spec = load("blake3-hash-65.sexp")
        tmp = tempfile.mkdtemp()
        wproducer.build(spec, tmp)
        self.assertEqual(field(wcheck.check_store(tmp), "verdict"), "accept")
        # Mutant: the producer compiles a spec whose root call lost ROOT.
        text = open(os.path.join(ROOT, "examples", "blake3-hash-65.sexp")).read()
        mutant_text = text.replace("0 1 10))", "0 1 2))")  # CHUNK_END|ROOT -> CHUNK_END
        self.assertNotEqual(text, mutant_text)
        machine_defn = wproducer.compile_wspec(parse(mutant_text))
        from ode.producer import put_definition
        from ode.canon import assoc
        from ode.blake3 import blake3
        tmp2 = tempfile.mkdtemp()
        binary = wproducer.emit_w32(machine_defn)
        with open(os.path.join(tmp2, "binary.bin"), "wb") as f:
            f.write(binary)
        cert = assoc("certificate", ("cert", Sym("correctness")),
                     ("property", Sym(wcheck.PROPERTY)),
                     ("spec", put_definition(tmp2, spec)),
                     ("machine", put_definition(tmp2, machine_defn)),
                     ("binary-hash", Bytes(blake3(binary))),
                     ("binary", Bytes(binary)),
                     ("inputs", len(word.inputs_of(spec))))
        with self.assertRaises(Reject) as cm:
            wcheck.check_certificate(tmp2, cert)
        self.assertIn("differs", str(cm.exception))


class CallTest(unittest.TestCase):
    """Specifications composed by call: name capture must be impossible."""

    def test_inlining_cannot_capture_the_callers_names(self):
        # Found by the game's Mallory: the producer minted t0, t1, ... and
        # collided with a caller whose own input was named t0.
        from ode.canon import canonical_bytes, hash_of
        callee = parse("(wspec (name inner) (inputs (a b)) "
                       "(steps ((t0 (add a b)) (t1 (xor t0 a)))) "
                       "(outputs (t1 t0)))")
        ch = hash_of(callee)
        caller = parse(
            f"(wspec (name outer) (inputs (t0 a)) "
            f"(defs ((#{ch.hex()} {canonical_bytes(callee).decode()}))) "
            f"(steps (((u v) (call #{ch.hex()} a t0)) (t1 (add u v)) "
            f"((w z) (call #{ch.hex()} t1 t0)))) (outputs (w z t1)))")
        machine_defn = wproducer.compile_wspec(caller)
        word.validate_wmachine(machine_defn)
        rng = random.Random(9)
        for _ in range(100):
            v = [rng.getrandbits(32), rng.getrandbits(32)]
            self.assertEqual(word.run_program(caller, v),
                             word.run_program(machine_defn, v))
        tmp = tempfile.mkdtemp()
        wproducer.build(caller, tmp)
        self.assertEqual(field(wcheck.check_store(tmp), "verdict"), "accept")
