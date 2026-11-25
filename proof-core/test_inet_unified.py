#!/usr/bin/env pypy3
"""Verify unified two-target RFC 1071 Internet Checksum (`examples/inet/inet_unified.ode`,
using `use rfc = "inet_spec.ode"`, `stack 0`, `trace depends on n` only, tail-calling `fold2`)
on both x86-64 and AArch64, and execute natively on AArch64 against RFC 1071 test vectors.
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
INET = os.path.join(HERE, "examples", "inet")
sys.path[:0] = [
    HERE,
    os.path.join(ROOT, "lang"),
    os.path.join(ROOT, "arm64"),
    os.path.join(ROOT, "core"),
    os.path.join(ROOT, "kcheck"),
]

import obj as aobj
import ode_audit
import ode_canon
import ode_unified
import odec

HAVE_LEAN = os.path.isfile(os.path.join(HERE, ".lake", "build", "bin", "odeverify"))
ARM_MACHINE = platform.machine() in ("arm64", "aarch64")
CC = shutil.which("clang") or shutil.which("cc")
SRC = os.path.join(INET, "inet_unified.ode")
CONTRACT_B32 = "kmrqitc6meivkfsy4zx3pqjjgpkyqx35cetjr7tpa3p2x2tse5mq"


def ref_inet_checksum(data: bytes) -> int:
    s = 0
    n = len(data)
    for i in range(0, n - (n & 1), 2):
        s += (data[i] << 8) + data[i + 1]
    if n & 1:
        s += data[-1] << 8
    while s >> 16:
        s = (s & 0xFFFF) + (s >> 16)
    return (~s) & 0xFFFF


class TestInetUnified(unittest.TestCase):
    def test_01_same_canonical_contract_both_targets(self):
        c_x86 = ode_canon.canonicalize_file(SRC, contract_name="inet_checksum", target="x86_64")
        c_arm = ode_canon.canonicalize_file(SRC, contract_name="inet_checksum", target="arm64")
        self.assertEqual(c_x86["contract_id"], CONTRACT_B32)
        self.assertEqual(c_arm["contract_id"], CONTRACT_B32)

    @unittest.skipUnless(HAVE_LEAN, "requires built proof-core odeverify binary")
    def test_02_pack_and_audit_both_targets(self):
        with tempfile.TemporaryDirectory() as d:
            for tgt, want_insns in (("x86_64", 39), ("arm64", 31)):
                out_o = os.path.join(d, f"inet_{tgt}.o")
                out_p = os.path.join(d, f"inet_{tgt}.proof")
                res = ode_audit.pack_verified(SRC, None, out_o, out_p, fn_name="inet_checksum", target=tgt)
                self.assertEqual(res["verdict"], "shown", res)
                self.assertEqual(res["contract_b32"], CONTRACT_B32)
                self.assertEqual(res["coverage"]["functions"], 2)
                self.assertEqual(res["coverage"]["instructions"], want_insns)

    @unittest.skipUnless(ARM_MACHINE and CC, "requires AArch64 hardware with C compiler")
    def test_03_native_arm64_matches_rfc1071(self):
        with tempfile.TemporaryDirectory() as d:
            src_text = odec.read_source(SRC)
            parsed = ode_unified.parse_unified(src_text, SRC)
            full_spec, _ = ode_unified.extract_spec(parsed, target_key="arm64", fn_name=None, include_calling=True, src=SRC)
            unit_elfs, orig_order = [], []
            for f in parsed["fns"]:
                inf = odec.compile_info(SRC, f["name"], target="arm64")
                unit_elfs.append(inf["elf"])
                orig_order.append(inf["symbol"])
            canon = ode_canon.canonicalize(full_spec, contract_name="inet_checksum")
            hash_sym = canon["symbol"]
            rename_map = {"fold2": "h0", "inet_checksum": hash_sym}
            obj_bytes = ode_audit.merge_elf_objects(
                unit_elfs, "arm64", rename_map, hash_sym,
                embedded_ocl_bytes=canon["canonical"].encode("utf-8"),
            )
            obj_p = os.path.join(d, "inet.o")
            with open(obj_p, "wb") as f:
                f.write(obj_bytes)

            e = aobj.Elf(obj_p)
            symbols, symtab = e.symbols()
            funcs = sorted(
                (st_val, nm, st_shndx, st_size)
                for nm, _bind, kind, st_shndx, st_val, st_size in symbols
                if nm and st_shndx != 0 and st_size > 0 and kind == 2
            )
            asm_lines = [
                "#ifdef __APPLE__",
                "#define SYM(x) _##x",
                "#define LSYM(x) L_ode_##x",
                "#else",
                "#define SYM(x) x",
                "#define LSYM(x) .L_ode_##x",
                "#endif",
                ".text",
            ]
            for _, nm, shndx, size in funcs:
                _, value, _, at = aobj.place(e, nm)
                relocs = e.relocations(shndx, symtab)
                code = e.b[at:at + size]
                asm_lines.append(".p2align 4")
                if nm.startswith("ode_"):
                    asm_lines += [".globl SYM(ode_inet_arm64)", "SYM(ode_inet_arm64):", f"LSYM({nm}):"]
                else:
                    asm_lines.append(f"LSYM({nm}):")
                for off in range(0, size, 4):
                    rel = relocs.get(value + off)
                    if rel is not None:
                        rtype, sym_idx = rel[0], rel[1]
                        tnm = symbols[sym_idx][0]
                        op = "b" if rtype == 282 else "bl"
                        asm_lines.append(f"  {op} LSYM({tnm})")
                    else:
                        w = int.from_bytes(code[off:off + 4], "little")
                        asm_lines.append(f"  .word 0x{w:08x}")
            asm_p = os.path.join(d, "inet.S")
            with open(asm_p, "w", encoding="utf-8") as f:
                f.write("\n".join(asm_lines) + "\n")

            vecs = [
                b"",
                b"\x00",
                b"\x00\x01\xf2\x03\xf4\xf5\xf6\xf7",  # RFC 1071 section 3 example
                b"\x45\x00\x00\x73\x00\x00\x40\x00\x40\x11\x00\x00\xc0\xa8\x00\x01\xc0\xa8\x00\xc7",  # IPv4 header
                b"\xff" * 1001,
                bytes(range(256)),
            ]
            c_checks = []
            for idx, v in enumerate(vecs):
                want = ref_inet_checksum(v)
                arr = ", ".join(str(b) for b in v) if v else "0"
                c_checks.append(
                    f"  {{ static const uint8_t d{idx}[] = {{{arr}}}; "
                    f"uint64_t g = ode_inet_arm64(d{idx}, {len(v)}); "
                    f"if (g != {want}ULL) return {idx + 1}; }}"
                )
            c_p = os.path.join(d, "run.c")
            with open(c_p, "w", encoding="utf-8") as f:
                f.write(
                    "#include <stdint.h>\n#include <stdio.h>\n"
                    "uint64_t ode_inet_arm64(const uint8_t *p, uint64_t n);\n"
                    "int main(void) {\n" + "\n".join(c_checks) + "\n  printf(\"inet_arm64: 6 vectors OK\\n\"); return 0;\n}\n"
                )
            bin_p = os.path.join(d, "run")
            subprocess.run([CC, "-O2", c_p, asm_p, "-o", bin_p], check=True)
            r = subprocess.run([bin_p], capture_output=True, text=True, check=True)
            self.assertIn("inet_arm64: 6 vectors OK", r.stdout)


if __name__ == "__main__":
    unittest.main()
