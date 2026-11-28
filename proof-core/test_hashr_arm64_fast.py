#!/usr/bin/env pypy3
"""Verify the fast AArch64 BLAKE3 bundle (`examples/hashr_arm64_fast/` — 8/8 functions,
1,891 instructions, 100% unified `.ode` with linked local namespaces `use`: custom-calling
`pad_fast`, `stack 0` tail-jumping `node_out_fast` & `<= 64 B` `chunk_node_fast`, direct
4-KiB `wide4_fast` dispatch, and 14-insn zero-copy 64-byte tail jump `b` in `hashr_arm64`),
test negative controls, and run 226 official/boundary vectors on real AArch64 silicon.

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
    os.path.join(ROOT, "lang"),
    os.path.join(ROOT, "arm64"),
    os.path.join(ROOT, "core"),
    os.path.join(ROOT, "kcheck"),
]

import obj as aobj
import ode_audit
import ode_unified
import odec
import test_hashr_arm64 as base_arm64

HAVE_LEAN = os.path.isfile(os.path.join(HERE, ".lake", "build", "bin", "odeverify"))
ARM_MACHINE = platform.machine() in ("arm64", "aarch64")
CC = shutil.which("clang") or shutil.which("cc")
CONTRACT_B32 = "atjviztehovcdbhilsklolv27dydrtly3dw75bpu3nfzujbpij6a"
HASH_ODE = os.path.join(FAST, "hash_fast_arm64.ode")
KEPT_PROOF = os.path.join(FAST, "b3hashr_arm64_fast.proof")


def _emit_asm_from_bundle(obj_path, export_sym="b3l_hashr_arm64"):
    """Emit cross-platform `.S` from the compiled multi-function ELF bundle for native execution."""
    e = aobj.Elf(obj_path)
    symbols, symtab = e.symbols()
    # Collect all defined STT_FUNC symbols in .text
    funcs = []
    for nm, _bind, kind, st_shndx, st_val, st_size in symbols:
        if nm and st_shndx != 0 and st_size > 0 and kind == 2:
            funcs.append((st_val, nm, st_shndx, st_size))
    funcs.sort()
    lines = [
        "#ifdef __APPLE__",
        "#define SYM(x) _##x",
        "#define LSYM(x) L_ode_##x",
        "#else",
        "#define SYM(x) x",
        "#define LSYM(x) .L_ode_##x",
        "#endif",
        ".text",
    ]
    for st_val, nm, shndx, size in funcs:
        _, value, _, at = aobj.place(e, nm)
        relocs = e.relocations(shndx, symtab)
        code = e.b[at:at + size]
        lines.append(".p2align 4")
        if nm.startswith("ode_"):
            lines += [f".globl SYM({export_sym})", f"SYM({export_sym}):", f"LSYM({nm}):"]
        else:
            lines.append(f"LSYM({nm}):")
        for off in range(0, size, 4):
            rel = relocs.get(value + off)
            if rel is not None:
                rtype, sym_idx = rel[0], rel[1]
                target_sym = symbols[sym_idx][0]
                if rtype == 282:
                    lines.append(f"  b LSYM({target_sym})")
                elif rtype == 283:
                    lines.append(f"  bl LSYM({target_sym})")
                else:
                    raise ValueError(f"unsupported relocation {rtype} in {nm}+{off}")
            else:
                w = int.from_bytes(code[off:off + 4], "little")
                lines.append(f"  .word 0x{w:08x}")
    return "\n".join(lines) + "\n"


class TestHashrArm64Fast(unittest.TestCase):
    @unittest.skipUnless(HAVE_LEAN, "requires built proof-core odeverify binary")
    def test_01_full_8fn_bundle_audit(self):
        """All 8 AArch64 functions pack from unified `.ode` + `use` into one bundle audited `shown`."""
        with tempfile.TemporaryDirectory() as d:
            out_o = os.path.join(d, "b3hashr_arm64_fast.o")
            res = ode_audit.pack_verified(
                HASH_ODE, None, out_o, None,
                fn_name="hashr_arm64", target="arm64",
                existing_bundle_proof=KEPT_PROOF,
                verifier="both",
            )
            self.assertEqual(res["verdict"], "shown", res)
            self.assertEqual(list(res["verifiers"].keys()), ["odeverify", "verify2"])
            self.assertEqual(res["contract_b32"], CONTRACT_B32)
            self.assertEqual(res["coverage"]["functions"], 8)
            self.assertEqual(res["coverage"]["local_helpers"], 7)
            self.assertEqual(res["coverage"]["exported_symbols"], 1)
            self.assertEqual(res["coverage"]["hooks"], 0)
            self.assertEqual(res["coverage"]["instructions"], 1891)

    @unittest.skipUnless(HAVE_LEAN, "requires built proof-core odeverify binary")
    def test_02_negative_controls_refused(self):
        """Mutated 64-byte tail-call root flag, broken tail-call preserves, and missing trace must be refused."""
        with tempfile.TemporaryDirectory() as d:
            for fn in ("blake3_spec.ode", "compress_arm64.ode", "wide4_fast_arm64.ode", "hash_fast_arm64.ode"):
                shutil.copy2(os.path.join(FAST, fn), os.path.join(d, fn))
            work_ode = os.path.join(d, "hash_fast_arm64.ode")
            with open(work_ode, "r", encoding="utf-8") as f:
                orig_src = f.read()

            # Control 1: drop `x29` from `pad_fast` preserves (breaks tail call from C-ABI chunk_node_fast)
            with open(KEPT_PROOF, "r", encoding="utf-8") as f:
                orig_proof = f.read()
            bad_proof1 = orig_proof.replace(
                "preserves x15, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29",
                "preserves x15, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28",
                1,
            )
            self.assertNotEqual(bad_proof1, orig_proof)
            bad_p1 = os.path.join(d, "bad1.proof")
            with open(bad_p1, "w", encoding="utf-8") as f:
                f.write(bad_proof1)
            out_o1 = os.path.join(d, "b1.o")
            res1 = ode_audit.pack_verified(
                work_ode, None, out_o1, None,
                fn_name="hashr_arm64", target="arm64",
                existing_bundle_proof=bad_p1,
            )
            self.assertEqual(res1["verdict"], "refused", "tail call with missing callee-saved x29 must be refused")

            # Control 2: drop ROOT flag (`x9 := 8` -> `x9 := 0`) on the 64-byte zero-copy tail-call path
            old_64 = "x9 := 8\n          orr x4, x4, x9\n          b comp.compress1"
            new_64 = "x9 := 0\n          orr x4, x4, x9\n          b comp.compress1"
            self.assertEqual(orig_src.count(old_64), 1)
            with open(work_ode, "w", encoding="utf-8") as f:
                f.write(orig_src.replace(old_64, new_64, 1))
            out_o2 = os.path.join(d, "b2.o")
            res2 = ode_audit.pack_verified(
                work_ode, None, out_o2, None,
                fn_name="hashr_arm64", target="arm64",
                existing_bundle_proof=KEPT_PROOF,
            )
            self.assertEqual(res2["verdict"], "refused", "missing ROOT flag on 64B tail-call fast path must be refused")

            # Control 3: drop `trace depends on len` from `hashr_arm64`
            old_tr = (
                "fn hashr_arm64(out: 32 bytes, input: len bytes, len: number, key: 32 bytes, flags: byte)\n"
                "    requires disjoint(out, input, key, 1)\n"
                "    ensures out = bytes_of(b3.hash_words(words(key), flags, input))\n"
                "    trace depends on len\n"
            )
            new_tr = (
                "fn hashr_arm64(out: 32 bytes, input: len bytes, len: number, key: 32 bytes, flags: byte)\n"
                "    requires disjoint(out, input, key, 1)\n"
                "    ensures out = bytes_of(b3.hash_words(words(key), flags, input))\n"
            )
            self.assertEqual(orig_src.count(old_tr), 1)
            with open(work_ode, "w", encoding="utf-8") as f:
                f.write(orig_src.replace(old_tr, new_tr, 1))
            out_o3 = os.path.join(d, "b3.o")
            res3 = ode_audit.pack_verified(
                work_ode, None, out_o3, None,
                fn_name="hashr_arm64", target="arm64",
                existing_bundle_proof=KEPT_PROOF,
            )
            self.assertEqual(res3["verdict"], "refused", "missing trace depends on len must be refused")

    @unittest.skipUnless(ARM_MACHINE and CC, "requires AArch64 hardware with C compiler")
    def test_03_native_hardware_vectors(self):
        """Assemble the 8 verified functions from unified `.ode` and run 226 BLAKE3 vectors."""
        with tempfile.TemporaryDirectory() as d:
            # Build the merged ELF bundle directly (no Lean needed for native silicon execution)
            src_text = odec.read_source(HASH_ODE)
            parsed = ode_unified.parse_unified(src_text, HASH_ODE)
            full_spec, _ = ode_unified.extract_spec(parsed, target_key="arm64", fn_name=None, include_calling=True, src=HASH_ODE)
            unit_elfs, orig_order = [], []
            for f in parsed["fns"]:
                inf = odec.compile_info(HASH_ODE, f["name"], target="arm64")
                unit_elfs.append(inf["elf"])
                orig_order.append(inf["symbol"])
            import ode_canon
            canon = ode_canon.canonicalize(full_spec, contract_name=orig_order[-1])
            hash_sym = canon["symbol"]
            rename_map = {orig: f"h{i}" for i, orig in enumerate(orig_order[:-1])}
            rename_map[orig_order[-1]] = hash_sym
            obj_bytes = ode_audit.merge_elf_objects(
                unit_elfs, "arm64", rename_map, hash_sym,
                embedded_ocl_bytes=canon["canonical"].encode("utf-8"),
            )
            out_o = os.path.join(d, "b3fast.o")
            with open(out_o, "wb") as f:
                f.write(obj_bytes)
            asm_p = os.path.join(d, "b3fast.S")
            c_p = os.path.join(d, "harness.c")
            bin_p = os.path.join(d, "run_b3fast")
            with open(asm_p, "w", encoding="utf-8") as f:
                f.write(_emit_asm_from_bundle(out_o))
            with open(c_p, "w", encoding="utf-8") as f:
                f.write(base_arm64.NATIVE_HARNESS)
            subprocess.run([CC, "-O2", c_p, asm_p, "-o", bin_p], check=True)
            r = subprocess.run([bin_p], capture_output=True, text=True, check=True)
            self.assertIn("b3l_hashr_arm64: 226 vectors + boundaries same", r.stdout.strip())


if __name__ == "__main__":
    unittest.main()
