"""Tests for lang/ode_canon.py: pure-Python BLAKE3-256, 52-char base-32 IDs, canonicalization, and glossaries."""

import base64
import glob
import os
import shutil
import subprocess
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for d in (HERE, os.path.join(ROOT, "kcheck")):
    if d not in sys.path:
        sys.path.insert(0, d)

import ode
import ode_canon


class TestBlake3(unittest.TestCase):
    def test_known_empty_vector(self):
        # Official BLAKE3-256("") hex = af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262
        expected_hex = "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
        got = ode_canon.blake3_256(b"")
        self.assertEqual(got.hex(), expected_hex)
        b32 = ode_canon.blake3_b32(b"")
        self.assertEqual(len(b32), 52)
        self.assertRegex(b32, r"^[a-z2-7]{52}$")
        self.assertEqual(b32, base64.b32encode(bytes.fromhex(expected_hex)).decode().rstrip("=").lower())

    def test_matches_b3sum_across_chunk_boundaries(self):
        b3sum = shutil.which("b3sum")
        if not b3sum:
            self.skipTest("b3sum not installed")
        for size in (0, 1, 63, 64, 65, 1023, 1024, 1025, 2048, 3073, 4096, 10000):
            data = bytes((i * 251 + 17) & 0xFF for i in range(size))
            out = subprocess.check_output([b3sum, "--no-names"], input=data).decode().strip()
            self.assertEqual(ode_canon.blake3_256(data).hex(), out, f"mismatch at size {size}")


class TestCanonicalize(unittest.TestCase):
    UTF8_A = """
    // Author A's version with comments and human names
    def utf8_cp2(a) {
        if len(a) == 0 then 4294967295
        else if a[0] < 128 then a[0]
        else if a[0] >= 194 && a[0] <= 223 then
            if len(a) >= 2 && a[1] >= 128 && a[1] <= 191 then
                (a[0] - 192) * 64 + (a[1] - 128)
            else 4294967295
        else 4294967295
    }

    contract ode_utf8_decode_2byte(input: n bytes, n: number) {
        returns utf8_cp2(input)
        trace depends on input, n
        stack 0
    }
    """

    UTF8_B = """
    // Completely different names, decoy unused helpers, reordered trace args, nameless contract!
    const UNUSED_DECOY = 999999
    def unused_helper(x, y) { x + y + UNUSED_DECOY }

    def completely_other_helper_name(buf) {
        if len(buf) == 0 then 4294967295
        else if buf[0] < 128 then buf[0]
        else if buf[0] >= 194 && buf[0] <= 223 then
            if len(buf) >= 2 && buf[1] >= 128 && buf[1] <= 191 then
                (buf[0] - 192) * 64 + (buf[1] - 128)
            else 4294967295
        else 4294967295
    }

    contract (bytes_ptr: count bytes, count: number) {
        stack 0
        trace depends on count, bytes_ptr
        returns completely_other_helper_name(bytes_ptr)
    }
    """

    def test_rename_comment_decoy_and_order_invariance(self):
        ra = ode_canon.canonicalize(self.UTF8_A)
        rb = ode_canon.canonicalize(self.UTF8_B)
        self.assertEqual(ra["canonical"], rb["canonical"])
        self.assertEqual(ra["contract_id"], rb["contract_id"])
        self.assertEqual(ra["symbol"], rb["symbol"])
        self.assertEqual(len(ra["contract_id"]), 52)
        self.assertEqual(len(ra["symbol"]), 56)
        self.assertTrue(ra["symbol"].startswith("ode_"))
        self.assertNotIn("UNUSED_DECOY", ra["canonical"])
        self.assertNotIn("unused_helper", ra["canonical"])
        self.assertNotIn("ode_utf8_decode_2byte", ra["canonical"])
        self.assertNotIn("utf8_cp2", ra["canonical"])
        self.assertNotIn("//", ra["canonical"])
        # Author glossaries differ while canonical ID is identical!
        self.assertEqual(ra["glossary"]["f0"], "utf8_cp2")
        self.assertEqual(rb["glossary"]["f0"], "completely_other_helper_name")
        self.assertEqual(ra["glossary"]["a0"], "input")
        self.assertEqual(rb["glossary"]["a0"], "bytes_ptr")

    def test_idempotence_and_bind_symbol(self):
        r1 = ode_canon.canonicalize(self.UTF8_A)
        self.assertTrue(ode_canon.is_canonical(r1["canonical"]))
        self.assertFalse(ode_canon.is_canonical(self.UTF8_A))
        r2 = ode_canon.canonicalize(r1["canonical"])
        self.assertEqual(r1["canonical"], r2["canonical"])
        self.assertEqual(r1["contract_id"], r2["contract_id"])
        # Binding to the hash symbol parses cleanly in kcheck/ode.py and evaluates identically.
        bound = ode_canon.bind_symbol(r1["canonical"], r1["symbol"])
        sp = ode.Spec(bound)
        self.assertIn(r1["symbol"], sp.contracts)
        self.assertEqual(sp.call(ode.Numbers(), "f0", [0x41]), 65)
        self.assertEqual(sp.call(ode.Numbers(), "f0", [0xC0, 0xAF]), 4294967295)

    def test_semantic_changes_change_contract_id(self):
        base = ode_canon.canonicalize(self.UTF8_A)["contract_id"]
        mutations = [
            self.UTF8_A.replace("194", "195"),
            self.UTF8_A.replace("< 128", "<= 128"),
            self.UTF8_A.replace("stack 0", "stack 16"),
            self.UTF8_A.replace("trace depends on input, n", "trace depends on n"),
            self.UTF8_A.replace("trace depends on input, n\n", ""),
        ]
        for idx, mut in enumerate(mutations):
            cid = ode_canon.canonicalize(mut)["contract_id"]
            self.assertNotEqual(cid, base, f"mutation {idx} failed to change contract_id")

    def test_glossary_rendering_preserves_canonical_id(self):
        r = ode_canon.canonicalize(self.UTF8_A)
        rendered = ode_canon.render_with_glossary(r["canonical"], r["glossary"])
        self.assertIn("utf8_cp2", rendered)
        self.assertIn("input", rendered)
        r_back = ode_canon.canonicalize(rendered)
        self.assertEqual(r_back["contract_id"], r["contract_id"])
        # Malicious glossary attempting keyword collision or duplicate alias is safely ignored.
        evil = {"a0": "if", "a1": "dup", "f0": "dup"}
        safe_rendered = ode_canon.render_with_glossary(r["canonical"], evil)
        self.assertEqual(ode_canon.canonicalize(safe_rendered)["contract_id"], r["contract_id"])

    def test_all_factory_and_blake3_and_chacha20_specs_roundtrip_idempotently(self):
        spec_files = sorted(
            glob.glob(os.path.join(ROOT, "factory", "verified", "*.spec"))
            + glob.glob(os.path.join(ROOT, "proof-core", "examples", "chacha20", "*.spec"))
            + [os.path.join(ROOT, "kcheck", "blake3.spec")]
        )
        self.assertGreaterEqual(len(spec_files), 40)
        ids_by_base = {}
        for path in spec_files:
            with open(path) as f:
                txt = f.read()
            sp = ode.Spec(txt)
            for cname in sp.contracts:
                r1 = ode_canon.canonicalize(txt, contract_name=cname)
                r2 = ode_canon.canonicalize(r1["canonical"])
                self.assertEqual(r1["canonical"], r2["canonical"], f"not idempotent: {path}:{cname}")
                self.assertEqual(r1["contract_id"], r2["contract_id"], f"id drift: {path}:{cname}")
                self.assertTrue(ode_canon.is_canonical(r1["canonical"]), f"is_canonical false: {path}:{cname}")
                # Must re-parse cleanly via kcheck/ode.py after bind_symbol
                bound = ode_canon.bind_symbol(r1["canonical"], r1["symbol"])
                sp2 = ode.Spec(bound)
                self.assertIn(r1["symbol"], sp2.contracts)
                ids_by_base[(os.path.basename(path), cname)] = r1["contract_id"]

        # Same contract on x86-64 and AArch64 (utf8_decode_2byte, zero stack, no arch `needs`)
        # MUST yield the EXACT SAME 52-char base-32 contract ID!
        x86_utf8 = ids_by_base[("utf8_decode_2byte_x86_64.spec", "ode_utf8_decode_2byte")]
        arm_utf8 = ids_by_base[("utf8_decode_2byte_arm64.spec", "ode_utf8_decode_2byte")]
        self.assertEqual(x86_utf8, arm_utf8)

        # ChaCha20 block on x86-64 (needs avx) vs AArch64 (no `needs avx`) MUST differ because `needs` differs!
        x86_c20 = ids_by_base[("chacha20_block_x86_64.spec", "ode_chacha20_block")]
        arm_c20 = ids_by_base[("chacha20_block_arm64.spec", "ode_chacha20_block")]
        self.assertNotEqual(x86_c20, arm_c20)

        # Canonical BLAKE3 contract must strip record field names AND still evaluate exact BLAKE3("")!
        with open(os.path.join(ROOT, "kcheck", "blake3.spec")) as f:
            b3 = ode_canon.canonicalize(f.read())
        self.assertNotIn("block:", b3["canonical"])
        self.assertNotIn("counter:", b3["canonical"])
        sp_b3 = ode.Spec(ode_canon.bind_symbol(b3["canonical"], b3["symbol"]))
        iv = []
        for w in ode_canon._IV:
            iv.extend([w & 0xFF, (w >> 8) & 0xFF, (w >> 16) & 0xFF, (w >> 24) & 0xFF])
        got_words = sp_b3.call(ode.Numbers(), "f0", ode.Numbers().words(iv), 0, [])
        self.assertEqual(bytes(ode.Numbers().bytes_of(got_words)), ode_canon.blake3_256(b""))

    def test_reordered_requires_helper_fixed_point(self):
        s1 = """
        def alpha(x) { x + 1 }
        def beta(x) { x + 2 }
        contract c1(x: number, y: number) {
            requires y == beta(x)
            requires x == alpha(y)
            returns x + y
            stack 0
        }
        """
        s2 = """
        def u(z) { z + 1 }
        def v(z) { z + 2 }
        contract c2(a: number, b: number) {
            requires a == u(b)
            requires b == v(a)
            returns a + b
            stack 0
        }
        """
        r1 = ode_canon.canonicalize(s1)
        r2 = ode_canon.canonicalize(s2)
        self.assertEqual(r1["canonical"], r2["canonical"])
        self.assertEqual(r1["contract_id"], r2["contract_id"])
        self.assertTrue(ode_canon.is_canonical(r1["canonical"]))

    def test_ode_symbol_refuses_truncated_or_bad_ids(self):
        with self.assertRaises(ValueError):
            ode_canon.ode_symbol("abcdef1234567890")  # truncated 16 chars
        with self.assertRaises(ValueError):
            ode_canon.ode_symbol("A" * 52)            # uppercase forbidden
        with self.assertRaises(ValueError):
            ode_canon.ode_symbol("0" * 52)            # '0' not in RFC 4648 base-32


if __name__ == "__main__":
    unittest.main()
