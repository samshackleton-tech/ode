#!/usr/bin/env python3
"""Tests for target arm64 in lang/odec.py, arm64/asm.py, and compile_info() source-line maps
across both x86-64 and AArch64."""
import os, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path[:0] = [HERE, os.path.join(ROOT, "arm64"), os.path.join(ROOT, "core")]
import odec, obj as aobj

MIX_ODE = os.path.join(ROOT, "proof-core", "examples", "arm64", "mix.ode")
MIX_REF = os.path.join(ROOT, "proof-core", "examples", "arm64", "armmix.o")
COMMON_ODE = os.path.join(ROOT, "kcheck", "programs", "common", "common.ode")
QUAD32_ODE = os.path.join(ROOT, "paper", "trial", "src", "quad32.ode")


class Arm64Ode(unittest.TestCase):
    def refused(self, text, fn, line, substr):
        with tempfile.TemporaryDirectory() as d:
            p = os.path.join(d, "bad.ode")
            with open(p, "w") as f:
                f.write(text)
            with self.assertRaises(SystemExit) as cm:
                odec.build(p, fn, os.path.join(d, "bad.o"))
            msg = str(cm.exception)
            self.assertIn(f"line {line}:", msg, msg)
            self.assertIn(substr, msg, msg)

    def test_mix_ode_matches_clang_armmix_byte_for_byte(self):
        with tempfile.TemporaryDirectory() as d:
            for fn, sym, want_words in [("mix16_3", "arm_mix16_3", 46), ("mix16_again", "arm_mix16_again", 6), ("mix16_6", "arm_mix16_6", 26)]:
                out = os.path.join(d, f"{sym}.o")
                odec.build(MIX_ODE, fn, out)
                got_w, _ = aobj.words(out, sym)
                ref_w, _ = aobj.words(MIX_REF, sym)
                self.assertEqual(len(got_w), want_words)
                self.assertEqual(got_w, ref_w, sym)
                self.assertEqual(aobj.read(out, sym), aobj.read(MIX_REF, sym), sym)

    def test_compile_info_line_maps_both_targets(self):
        arm = odec.compile_info(MIX_ODE, "mix16_6")
        self.assertEqual(arm["target"], "arm64")
        self.assertEqual(arm["symbol"], "arm_mix16_6")
        self.assertEqual(arm["code_bytes"], 104)
        self.assertEqual(len(arm["line_map"]), 26)
        self.assertEqual(arm["regs"], {"keep_out": "x19", "keep_a": "x20", "zero": "x9"})
        self.assertEqual(arm["frame"]["size"], 96)
        self.assertEqual([f["name"] for f in arm["frame"]["fields"]], ["mid", "saved_lr", "saved_out", "saved_a", "pad"])
        # Every AArch64 instruction is 4 bytes and pc advances by 4
        for idx, row in enumerate(arm["line_map"]):
            self.assertEqual(row["pc"], idx * 4)
            self.assertEqual(row["len"], 4)
        self.assertEqual(arm["line_map"][1]["typed"], "saved_lr[0] := x30")
        self.assertEqual(arm["line_map"][1]["asm"], "str x30, [sp, 64]")

        x86 = odec.compile_info(COMMON_ODE, "common")
        self.assertEqual(x86["target"], "x86_64")
        self.assertEqual(x86["symbol"], "ode_common")
        self.assertGreater(x86["code_bytes"], 0)
        self.assertGreater(len(x86["line_map"]), 10)
        # Verify pcs are strictly increasing and match decoded lengths
        for a, b in zip(x86["line_map"], x86["line_map"][1:]):
            self.assertEqual(a["pc"] + a["len"], b["pc"])

        q32 = odec.compile_info(QUAD32_ODE, "quad32")
        self.assertEqual(q32["target"], "x86_64")
        self.assertIsNotNone(q32["frame"])
        self.assertGreater(q32["frame"]["size"], 0)

    def test_arm64_negative_controls_name_source_line(self):
        with open(MIX_ODE) as f:
            base = f.read()
        # 1. distinct violation in inline fn
        self.refused(base.replace("mix_step(d, a)", "mix_step(d, d)", 1), "mix16_3", 15, "must differ")
        # 2. changes violation in inline fn (eor writes a, which is not in `changes d`)
        self.refused(base.replace("eor d.16b, d.16b, a.16b", "eor a.16b, d.16b, a.16b", 1), "mix16_3", 7, "does not list")
        # 3. frame slot out of bounds
        self.refused(base.replace("for i in 0..8 {", "for i in 0..9 {", 1), "mix16_6", 69, "slots of `mid.u64` are 0 to 7")
        # 4. size mismatch on :=
        self.refused(base.replace("x30 := saved_lr[0]", "w0 := saved_lr[0]", 1), "mix16_again", 45, "has 4 and `saved_lr[0]` has 8")
        # 5. store of immediate directly to memory refused on arm64
        self.refused(base.replace("mid.u64[$i] := zero", "mid.u64[$i] := 0", 1), "mix16_6", 69, "no store of an immediate to memory")
        # 6. misaligned sp displacement refused by arm64.tab
        self.refused(base.replace("saved_lr[0] := x30", "str x30, [sp, 4]", 1), "mix16_again", 43, "multiple of 8")
        # 7. sp used as a general register where x0..x30 is required
        self.refused(base.replace("mov x19, x0", "mov x19, sp", 1).replace("keep_out := x0", "mov x19, sp", 1), "mix16_6", 65, "not a general 64-bit register")
        # 8. unknown instruction refused at its line
        self.refused(base.replace("ret", "mul x0, x1, x2", 1), "mix16_3", 34, "no row in arm64.tab matches")


if __name__ == "__main__":
    unittest.main()
