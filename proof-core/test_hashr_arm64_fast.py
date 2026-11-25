#!/usr/bin/env pypy3
"""Verify the fast AArch64 BLAKE3 bundle (`examples/hashr_arm64_fast/` — 8/8 functions,
1,891 instructions, 100% Ode source: custom-calling `b3l_pad_fast_arm64`, `stack 0`
tail-jumping `b3l_node_out_fast_arm64` & `<= 64 B` `b3l_chunk_node_fast_arm64`,
direct 4-KiB `b3l_wide4_fast_arm64` dispatch, and 14-insn zero-copy 64-byte tail jump
`b` in `b3l_hashr_arm64`), test negative controls, and run 226 official/boundary vectors
on real AArch64 silicon.

    pypy3 proof-core/test_hashr_arm64_fast.py
"""
import os
import platform
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
FAST = os.path.join(HERE, "examples", "hashr_arm64_fast")
sys.path[:0] = [
    HERE,
    FAST,
    os.path.join(ROOT, "lang"),
    os.path.join(ROOT, "arm64"),
    os.path.join(ROOT, "core"),
    os.path.join(ROOT, "kcheck"),
]

import lean_verify
import ode_audit
import odec
import prove_arm64_fast as pf
import test_hashr_arm64 as base_arm64

HAVE_LEAN = os.path.isfile(os.path.join(HERE, ".lake", "build", "bin", "odeverify"))
ARM_MACHINE = platform.machine() in ("arm64", "aarch64")
CC = shutil.which("clang") or shutil.which("cc")
CONTRACT_B32 = "ckdrhllybtjzr7vgscyhlgz6sxqaga347kozoepvqk3b54ohbfra"
KEPT_PROOF = os.path.join(FAST, "b3hashr_arm64_fast.proof")


class TestHashrArm64Fast(unittest.TestCase):
    @unittest.skipUnless(HAVE_LEAN, "requires built proof-core odeverify binary")
    def test_01_full_8fn_bundle_audit(self):
        """All 8 AArch64 functions pack into one hash-bound ELF64 bundle audited `shown`."""
        spec_text = pf.load_full_spec()
        with tempfile.TemporaryDirectory() as d:
            unit_elfs = []
            order = []
            for src, ode_fn, sym in pf.FUNCTIONS:
                obj_p = os.path.join(d, sym + ".o")
                odec.build(src, ode_fn, obj_p)
                with open(obj_p, "rb") as f:
                    unit_elfs.append(f.read())
                order.append(sym)
            out_o = os.path.join(d, "b3hashr_arm64_fast.o")
            out_p = os.path.join(d, "b3hashr_arm64_fast.proof")
            res = ode_audit.pack_bundle(
                unit_elfs, order, "b3l_hashr_arm64", spec_text, out_o, out_p,
                existing_proof_path=KEPT_PROOF,
            )
            self.assertEqual(res["verdict"], "shown", res)
            self.assertEqual(res["contract_b32"], CONTRACT_B32)
            self.assertEqual(res["coverage"]["functions"], 8)
            self.assertEqual(res["coverage"]["local_helpers"], 7)
            self.assertEqual(res["coverage"]["exported_symbols"], 1)
            self.assertEqual(res["coverage"]["hooks"], 0)
            self.assertEqual(res["coverage"]["instructions"], 1891)

    @unittest.skipUnless(HAVE_LEAN, "requires built proof-core odeverify binary")
    def test_02_negative_controls_refused(self):
        """Mutated 64-byte tail-call root flag and broken tail-call preserves must be refused."""
        spec_text = pf.load_full_spec()
        with tempfile.TemporaryDirectory() as d:
            pairs = []
            for src, ode_fn, sym in pf.FUNCTIONS:
                obj_p = os.path.join(d, sym + ".o")
                odec.build(src, ode_fn, obj_p)
                pairs.append((obj_p, sym))

            # Control 1: drop `x29` from `b3l_pad_fast_arm64` preserves (breaks tail call from C-ABI chunk_node)
            bad_spec1 = spec_text.replace(
                "preserves x15, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29",
                "preserves x15, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28",
                1,
            )
            self.assertNotEqual(bad_spec1, spec_text)
            ok1, _ = lean_verify.verify(bad_spec1, pairs, KEPT_PROOF)
            self.assertFalse(ok1, "tail call with missing callee-saved x29 must be refused")

            # Control 2: drop ROOT flag (`x9 := 8` -> `x9 := 0`) on the 64-byte zero-copy tail-call path
            with open(os.path.join(FAST, "hash_fast_arm64.ode"), "r", encoding="utf-8") as f:
                hsrc = f.read()
            old_64 = "  x9 := 8\n  orr x4, x4, x9\n  b blake3_servil_compress_in_place_arm64"
            new_64 = "  x9 := 0\n  orr x4, x4, x9\n  b blake3_servil_compress_in_place_arm64"
            self.assertEqual(hsrc.count(old_64), 1)
            bad_ode = os.path.join(d, "bad_hash.ode")
            with open(bad_ode, "w", encoding="utf-8") as f:
                f.write(hsrc.replace(old_64, new_64, 1))
            bad_obj = os.path.join(d, "bad_hashr.o")
            odec.build(bad_ode, "hashr_fast_arm64", bad_obj)
            bad_pairs = pairs[:-1] + [(bad_obj, "b3l_hashr_arm64")]
            ok2, _ = lean_verify.verify(spec_text, bad_pairs, KEPT_PROOF)
            self.assertFalse(ok2, "missing ROOT flag on 64B tail-call fast path must be refused")

            # Control 3: drop `trace depends on len` from `b3l_hashr_arm64`
            bad_spec3 = spec_text.replace(
                "contract b3l_hashr_arm64(out: 32 bytes, input: len bytes, len: number, key: 32 bytes, flags: byte) {\n"
                "    requires no_overlap(out, input, key)\n"
                "    ensures out = bytes_of(hash_words(words(key), flags, input))\n"
                "    trace depends on len\n",
                "contract b3l_hashr_arm64(out: 32 bytes, input: len bytes, len: number, key: 32 bytes, flags: byte) {\n"
                "    requires no_overlap(out, input, key)\n"
                "    ensures out = bytes_of(hash_words(words(key), flags, input))\n",
                1,
            )
            self.assertNotEqual(bad_spec3, spec_text)
            ok3, _ = lean_verify.verify(bad_spec3, pairs, KEPT_PROOF)
            self.assertFalse(ok3, "missing trace depends on len must be refused")

    @unittest.skipUnless(ARM_MACHINE and CC, "requires AArch64 hardware with C compiler")
    def test_03_native_hardware_vectors(self):
        """Assemble the 8 verified functions with `bl`/`b` relocations and run 226 BLAKE3 vectors."""
        with tempfile.TemporaryDirectory() as d:
            pairs = []
            for src, ode_fn, sym in pf.FUNCTIONS:
                obj_p = os.path.join(d, sym + ".o")
                odec.build(src, ode_fn, obj_p)
                pairs.append((obj_p, sym))
            asm_p = os.path.join(d, "b3fast.S")
            c_p = os.path.join(d, "harness.c")
            bin_p = os.path.join(d, "run_b3fast")
            with open(asm_p, "w", encoding="utf-8") as f:
                f.write(pf.emit_asm(pairs, CONTRACT_B32, "test"))
            with open(c_p, "w", encoding="utf-8") as f:
                f.write(base_arm64.NATIVE_HARNESS)
            subprocess.run([CC, "-O2", c_p, asm_p, "-o", bin_p], check=True)
            r = subprocess.run([bin_p], capture_output=True, text=True, check=True)
            self.assertIn("b3l_hashr_arm64: 226 vectors + boundaries same", r.stdout.strip())


if __name__ == "__main__":
    unittest.main()
