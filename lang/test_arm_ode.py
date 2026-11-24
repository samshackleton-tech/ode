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

    def test_place_reg_and_frame_rewriting(self):
        src = """target x86_64
fn f as "f_sym" {
  frame {
    buf: 2 * block
  }
  reg idx = r13
  reg acc = zmm0
  idx := 0
  place {
    name i = idx
    keep idx
    lane acc: h = x after i
    cell buf[1]: word k = w(k)
    fact 0 <= i
    decreases n - i
  }
  ret
}
"""
        with tempfile.TemporaryDirectory() as d:
            p = os.path.join(d, "pl.ode")
            with open(p, "w") as f: f.write(src)
            info = odec.compile_info(p, "f")
            pl = info["places"]["f_sym"]
            self.assertIn("name i = r13", pl)
            self.assertIn("keep r13", pl)
            self.assertIn("lane zmm0: h = x after i", pl)
            self.assertIn("cell [rsp + 64]: word k = w(k)", pl)
            self.assertIn("fact 0 <= i", pl)
            # Out-of-range frame cell in place is refused with line number
            self.refused(src.replace("cell buf[1]:", "cell buf[2]:"), "f", 13, "out of range")

    def test_budget_parsing_invariance_and_controls(self):
        src_plain = """target arm64
fn f as "f_sym" {
  add x0, x0, 1
  ret
}
"""
        src_budget = """target arm64
fn f as "f_sym" {
  budget {
    max_bytes 16
    max_icache_lines: 1
    max_line_splits = 0
  }
  add x0, x0, 1
  ret
}
"""
        with tempfile.TemporaryDirectory() as d:
            pa, pb = os.path.join(d, "a.ode"), os.path.join(d, "b.ode")
            with open(pa, "w") as f: f.write(src_plain)
            with open(pb, "w") as f: f.write(src_budget)
            ia, ib = odec.compile_info(pa, "f"), odec.compile_info(pb, "f")
            # Advisory budget changes zero bytes in the emitted ELF object
            self.assertEqual(ia["elf"], ib["elf"])
            self.assertEqual(ia["budget"], {})
            self.assertEqual(ib["budget"], {"max_bytes": 16, "max_icache_lines": 1, "max_line_splits": 0})
        # Negative controls
        self.refused(src_budget.replace("max_bytes 16", "max_bogus 16"), "f", 4, "no budget key")
        self.refused(src_budget.replace("max_bytes 16", "max_bytes -1"), "f", 4, "nonnegative whole number")
        self.refused(src_budget.replace("max_line_splits = 0", "max_bytes 32"), "f", 6, "listed twice")
        self.refused(src_budget.replace("ret", "budget {\n    max_bytes 8\n  }\n  ret"), "f", 9, "second budget")

    def test_arm64_loop_branches_and_zero_arm64(self):
        z_ode = os.path.join(ROOT, "proof-core", "examples", "verifier", "zero_arm64.ode")
        info = odec.compile_info(z_ode, "all_zero")
        self.assertEqual(info["target"], "arm64")
        self.assertEqual(info["symbol"], "arm_all_zero")
        self.assertEqual(info["code_bytes"], 52)
        self.assertEqual(len(info["line_map"]), 13)
        # Forward b.hs jumps from pc=12 to pc=48 (+36); backward b.lo jumps from pc=44 to pc=16 (-28)
        with tempfile.TemporaryDirectory() as d:
            obj_p = os.path.join(d, "zero.o")
            with open(obj_p, "wb") as f:
                f.write(info["elf"])
            rows = aobj.read(obj_p, "arm_all_zero")
            by_at = {at: (ins, nxt) for at, nxt, ins in rows}
            self.assertEqual(by_at[8][0], ".bhs 0x24")
            self.assertEqual(by_at[24][0], ".bne 0x2c")
            self.assertEqual(by_at[32][0], ".b 0x4")
            self.assertEqual(by_at[40][0], ".b 0x30")
            # Native AArch64 execution test when running on arm64 with clang
            import platform, shutil, subprocess
            if platform.machine() in ("arm64", "aarch64") and shutil.which("clang"):
                driver = os.path.join(d, "run.c")
                exe = os.path.join(d, "run")
                with open(driver, "w") as f:
                    f.write(
                        "#include <stdint.h>\n"
                        "#include <stdio.h>\n"
                        "extern uint64_t arm_all_zero(const uint8_t *p, uint64_t n);\n"
                        "int main(void) {\n"
                        "  uint8_t a[16] = {0};\n"
                        "  if (arm_all_zero(a, 0) != 1) return 1;\n"
                        "  if (arm_all_zero(a, 16) != 1) return 2;\n"
                        "  a[0] = 1; if (arm_all_zero(a, 16) != 0) return 3;\n"
                        "  a[0] = 0; a[15] = 0x80; if (arm_all_zero(a, 16) != 0) return 4;\n"
                        "  if (arm_all_zero(a, 15) != 1) return 5;\n"
                        "  return 0;\n"
                        "}\n"
                    )
                if platform.system() == "Darwin":
                    # Assemble the exact ELF .text words into a Mach-O symbol and run on Apple Silicon
                    ws, _ = aobj.words(obj_p, "arm_all_zero")
                    s_p = os.path.join(d, "zero_macho.s")
                    with open(s_p, "w") as f:
                        f.write(".text\n.globl _arm_all_zero\n.p2align 2\n_arm_all_zero:\n")
                        for w in ws:
                            f.write(f"  .long 0x{int.from_bytes(w, 'little'):08x}\n")
                    subprocess.run(["clang", "-O1", driver, s_p, "-o", exe], check=True)
                    subprocess.run([exe], check=True)
                else:
                    subprocess.run(["clang", "-O1", driver, obj_p, "-o", exe], check=True)
                    subprocess.run([exe], check=True)
        # Negative controls: unknown label and out-of-range ldrb immediate
        with open(z_ode) as f:
            z_src = f.read()
        self.refused(z_src.replace("b.hs @yes", "b.hs @missing"), "all_zero", 31, "has no label")
        self.refused(z_src.replace("ldrb cur, [addr, 0]", "ldrb cur, [addr, 4096]"), "all_zero", 33, "12 bits")

    def test_wirth_diagnostics_and_arm64_ptr_name(self):
        # On AArch64, `ptr`/`word`/`byte` are not operand keywords and work as register names.
        arm_src = """target arm64
fn f as "f_sym" {
  reg ptr = x0
  reg word = x1
  add x0, ptr, word
  ret
}
"""
        with tempfile.TemporaryDirectory() as d:
            p = os.path.join(d, "p.ode")
            with open(p, "w") as f:
                f.write(arm_src)
            info = odec.compile_info(p, "f")
            self.assertEqual(info["code_bytes"], 8)
        # On x86-64, `reg ptr` is refused with an actionable hint naming alternatives.
        x86_src = """target x86_64
fn f as "f_sym" {
  reg ptr = rdi
  ret
}
"""
        self.refused(x86_src, "f", 3, "byte ptr")
        # AArch64 out-of-range immediates include exact fix guidance.
        self.refused("target arm64\nfn f as \"f_sym\" {\n  mov x0, 65536\n  ret\n}\n", "f", 3, "mov + lsl + add")
        self.refused("target arm64\nfn f as \"f_sym\" {\n  cmp x0, 4096\n  ret\n}\n", "f", 3, "scratch register")


if __name__ == "__main__":
    unittest.main()
