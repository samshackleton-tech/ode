"""BLAKE3 and the canonical form: the hash and the reader (R6, R2)."""
import os
import sys
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from ode.blake3 import blake3  # noqa: E402
from ode.canon import Bytes, canonical_bytes, hash_of, parse, read_canonical  # noqa: E402


class Blake3Test(unittest.TestCase):
    def test_published_vectors(self):
        self.assertEqual(blake3(b"").hex(),
                         "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262")
        self.assertEqual(blake3(b"abc").hex(),
                         "6437b3ac38465133ffb63b75273a8db548c558465d79db03fd359c6cd5bd9d85")


class CanonTest(unittest.TestCase):
    def test_round_trip_and_strictness(self):
        d = parse("(spec (name mix) (inputs 2))")
        self.assertEqual(canonical_bytes(d), b"(spec (name mix) (inputs 2))")
        self.assertEqual(read_canonical(canonical_bytes(d)), d)
        for bad in (b"(spec  (name mix))", b"(spec (name mix))\n"):
            with self.assertRaises(ValueError):
                read_canonical(bad)
        # No token is both an integer and a symbol; bytes are #hex.
        self.assertEqual(parse("#0a0b"), Bytes(b"\x0a\x0b"))
        self.assertEqual(canonical_bytes(parse("(x #)")), b"(x #)")
        for bad in ("007", "#0A", "#abc", "1abc", "(name 'mix)"):
            with self.assertRaises(ValueError):
                parse(bad)

    def test_hash_binds_content(self):
        self.assertNotEqual(hash_of(parse("(a 1)"), 'spec'), hash_of(parse("(a 2)"), 'spec'))


if __name__ == "__main__":
    unittest.main()
