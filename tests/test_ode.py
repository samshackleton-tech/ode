"""Conformance tests at toy scale (SPEC s9).

Every checker ships with checks that it can fail: mutant subjects,
mutant binaries, and wrong conclusions, each of which it must reject
(blake3-servil, lesson 3). Run: pypy3 -m unittest discover -s tests
"""
import os
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from ode import checker, machine, producer, spec as spec_mod
from ode.blake3 import blake3_hex
from ode.canon import (Sym, assoc, canonical_bytes, field, hash_of, parse,
                       read_canonical)

EXAMPLE = os.path.join(os.path.dirname(__file__), "..", "examples", "mix.sexp")


def load_example():
    with open(EXAMPLE, "rb") as f:
        return parse(f.read())


class Blake3Test(unittest.TestCase):
    def test_vectors(self):
        # Published BLAKE3 test vectors (C2SP appendix / BLAKE3 paper),
        # cross-checked against the reference implementation.
        self.assertEqual(
            blake3_hex(b""),
            "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262")
        self.assertEqual(
            blake3_hex(b"abc"),
            "6437b3ac38465133ffb63b75273a8db548c558465d79db03fd359c6cd5bd9d85")
        self.assertEqual(len(blake3_hex(b"x" * 5000)), 64)


class CanonTest(unittest.TestCase):
    def test_round_trip_and_strictness(self):
        d = parse("(spec (name mix) (inputs 2))")
        self.assertEqual(canonical_bytes(d), b"(spec (name mix) (inputs 2))")
        self.assertEqual(read_canonical(canonical_bytes(d)), d)
        with self.assertRaises(ValueError):
            read_canonical(b"(spec  (name mix))")   # double space
        with self.assertRaises(ValueError):
            read_canonical(b"(spec (name mix))\n")  # trailing newline
        with self.assertRaises(ValueError):
            parse("(spec (name 'mix))")

    def test_hash_binds_content(self):
        self.assertNotEqual(hash_of(parse("(a 1)")), hash_of(parse("(a 2)")))


class EndToEndTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp()
        self.spec = load_example()
        self.result = producer.build(self.spec, self.tmp)

    def _cert(self):
        with open(os.path.join(self.tmp, "certificate.sexp"), "rb") as f:
            return read_canonical(f.read())

    def _rewrite_cert(self, cert):
        producer.put_definition(self.tmp, cert)
        with open(os.path.join(self.tmp, "certificate.sexp"), "wb") as f:
            f.write(canonical_bytes(cert))

    def _set(self, cert, name, value):
        return [cert[0]] + [[p[0], value] if p[0] == name else p
                            for p in cert[1:]]

    def test_check_accepts_and_counts_the_whole_domain(self):
        record = checker.check_store(self.tmp)
        self.assertEqual(field(record, "verdict"), "accept")
        self.assertEqual(field(record, "cases-checked"), 256 * 256)

    def test_run_matches_spec_on_vectors(self):
        with open(os.path.join(self.tmp, "binary.bin"), "rb") as f:
            binary = f.read()
        for inputs, want in producer.self_test_vectors(self.spec):
            self.assertEqual(machine.run_binary(binary, inputs), want)
            self.assertEqual(spec_mod.eval_spec(self.spec, inputs), want)

    def test_determinism(self):
        tmp2 = tempfile.mkdtemp()
        again = producer.build(self.spec, tmp2)
        self.assertEqual(again, self.result)

    def test_mutant_binary_rejected(self):
        cert = self._cert()
        raw = bytearray(bytes.fromhex(str(field(cert, "binary-hex"))))
        raw[-1] ^= 1
        cert = self._set(cert, "binary-hex", Sym(bytes(raw).hex()))
        cert = self._set(cert, "binary-hash", Sym(blake3_hex(bytes(raw))))
        self._rewrite_cert(cert)
        with self.assertRaises(checker.Reject):
            checker.check_store(self.tmp)

    def test_mutant_machine_definition_rejected(self):
        cert = self._cert()
        bad = parse("(machine (isa ODE8) (inputs 2) "
                    "(code ((load 0) (load 1) (xor) (const 61) (add) "
                    "(rotl 3))))")
        cert = self._set(cert, "machine",
                         Sym(producer.put_definition(self.tmp, bad)))
        binary = machine.emit(bad)  # honest emitter output, honestly hashed
        cert = self._set(cert, "binary-hex", Sym(binary.hex()))
        cert = self._set(cert, "binary-hash", Sym(blake3_hex(binary)))
        self._rewrite_cert(cert)
        with self.assertRaises(checker.Reject) as cm:
            checker.check_store(self.tmp)
        self.assertIn("disagreement", str(cm.exception))

    def test_mutant_spec_rejected_by_hash(self):
        evil = parse("(spec (name mix) (inputs 2) "
                     "(body (xor (var 0) (var 1))))")
        path = os.path.join(self.tmp, self.result["spec"] + ".sexp")
        with open(path, "wb") as f:
            f.write(canonical_bytes(evil))  # bytes no longer match the name
        with self.assertRaises(checker.Reject):
            checker.check_store(self.tmp)

    def test_wrong_property_rejected(self):
        cert = self._set(self._cert(), "property", Sym("equals-spec-v99"))
        self._rewrite_cert(cert)
        with self.assertRaises(checker.Reject):
            checker.check_store(self.tmp)

    def test_assurance_map_is_generated_from_the_record(self):
        record = checker.check_store(self.tmp)
        text = checker.assurance_markdown(record)
        self.assertIn(str(field(record, "spec")), text)
        self.assertIn("ode/checker.py", text)
        self.assertIn("unproved", text)


if __name__ == "__main__":
    unittest.main()
