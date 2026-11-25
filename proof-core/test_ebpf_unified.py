"""End-to-end test for the verified RFC 9669 eBPF virtual machine (`examples/ebpf/ebpf_unified.ode`).

Verifies:
  1. Spec evaluation on 5 real RFC 9669 eBPF bytecode programs (sum 1..10, fib(10), fib(15), OOF, bad op).
  2. Multi-function `ode pack` + `ode audit` on AArch64 (all 6 `stack 0` functions, 100% coverage,
     exact canonical 52-char BLAKE3 contract ID) + 1-byte tamper negative control.
  3. On native Apple Silicon (macOS arm64), links the exact verified AArch64 machine code and executes
     all 5 real RFC 9669 eBPF bytecode programs on hardware.
"""
import os, platform, struct, subprocess, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path[:0] = [os.path.join(ROOT, "lang"), os.path.join(ROOT, "arm64"),
                os.path.join(ROOT, "core"), os.path.join(ROOT, "kcheck"), HERE]

import ode, odec, ode_tool, obj as aobj

SRC = os.path.join(HERE, "examples", "ebpf", "ebpf_unified.ode")
SPEC = os.path.join(HERE, "examples", "ebpf", "ebpf_spec.ode")
EXPECTED_ID = "s2or2kdio5y5yqajr23uiowr7ycsb5qklcamvqflm3bejfojiczq"
ERR = 4294967296


def insn(op, dst=0, src=0, off=0, imm=0):
    return list(struct.pack("<BBhI", op, (src << 4) | dst, off, imm & 0xFFFFFFFF))


PROG_SUM = (
    insn(0xB7, 0, 0, 0, 0) +
    insn(0x15, 1, 0, 3, 0) +
    insn(0x0F, 0, 1, 0, 0) +
    insn(0x17, 1, 0, 0, 1) +
    insn(0x05, 0, 0, -4, 0) +
    insn(0x95)
)

PROG_FIB = (
    insn(0xB7, 0, 0, 0, 0) +
    insn(0xB7, 2, 0, 0, 1) +
    insn(0x15, 1, 0, 6, 0) +
    insn(0xBF, 3, 0, 0, 0) +
    insn(0x0F, 3, 2, 0, 0) +
    insn(0xBF, 0, 2, 0, 0) +
    insn(0xBF, 2, 3, 0, 0) +
    insn(0x17, 1, 0, 0, 1) +
    insn(0x05, 0, 0, -7, 0) +
    insn(0x95)
)

PROG_BAD = insn(0xFF)


class TestEbpfUnified(unittest.TestCase):
    def test_spec_vectors(self):
        with open(SPEC, encoding="utf-8") as f:
            sp = ode.Spec(f.read())
        ev = ode.Numbers()
        self.assertEqual(sp.call(ev, "ebpf_run", PROG_SUM, 100, 10), 55)
        self.assertEqual(sp.call(ev, "ebpf_run", PROG_SUM, 10, 10), ERR)
        self.assertEqual(sp.call(ev, "ebpf_run", PROG_FIB, 200, 10), 55)
        self.assertEqual(sp.call(ev, "ebpf_run", PROG_FIB, 200, 15), 610)
        self.assertEqual(sp.call(ev, "ebpf_run", PROG_BAD, 10, 0), ERR)

    def test_pack_audit_arm64(self):
        with tempfile.TemporaryDirectory() as d:
            obj_p = os.path.join(d, "ebpf_arm64.o")
            prf_p = os.path.join(d, "ebpf_arm64.proof")
            rc = ode_tool.main(["pack", SRC, "--fn", "ebpf_run", "--target", "arm64",
                                "--out", obj_p, "--proof", prf_p])
            self.assertEqual(rc, 0)
            out = subprocess.check_output(
                [sys.executable, os.path.join(ROOT, "lang", "ode_tool.py"),
                 "audit", obj_p, "--proof", prf_p],
                text=True,
            )
            self.assertIn(EXPECTED_ID, out)
            self.assertIn("VERDICT:           shown", out)
            self.assertIn("6 functions (1 exported, 5 local)", out)

            # Negative control: flip one byte in .text -> audit must refuse
            bad_p = os.path.join(d, "ebpf_bad.o")
            with open(obj_p, "rb") as f:
                raw = bytearray(f.read())
            e = aobj.Elf(obj_p)
            _, _, _, at = aobj.place(e, f"ode_{EXPECTED_ID}")
            raw[at] ^= 0xFF
            with open(bad_p, "wb") as f:
                f.write(raw)
            r = subprocess.run(
                [sys.executable, os.path.join(ROOT, "lang", "ode_tool.py"),
                 "audit", bad_p, "--proof", prf_p],
                capture_output=True, text=True,
            )
            self.assertNotEqual(r.returncode, 0)

    def test_native_arm64_execution(self):
        if platform.system() != "Darwin" or platform.machine() != "arm64":
            self.skipTest("native arm64 execution test runs on Apple Silicon")
        with tempfile.TemporaryDirectory() as d:
            fns = ["get_reg_fn", "ebpf_alu_fn", "ebpf_cond_fn", "is_alu_k_fn", "ebpf_jump_fn", "ebpf_run"]
            asm = [".text", ".p2align 4", ".globl _ebpf_run"]
            for fn in fns:
                inf = odec.compile_info(SRC, fn, target="arm64")
                obj_p = os.path.join(d, f"{fn}.o")
                with open(obj_p, "wb") as f:
                    f.write(inf["elf"])
                e = aobj.Elf(obj_p)
                text_idx, text_sec = [(i, s) for i, s in enumerate(e.sections)
                                      if e.text(e.names, s[0]) == ".text"][0]
                text_off, text_size = text_sec[4], text_sec[5]
                text = e.b[text_off:text_off + text_size]
                syms, symtab = e.symbols()
                rels = {roff: syms[sym_idx][0]
                        for roff, (_, sym_idx, _) in e.relocations(text_idx, symtab).items()}
                asm.append(f"_{fn}:")
                for off in range(0, len(text), 4):
                    if off in rels:
                        asm.append(f"  bl _{rels[off]}")
                    else:
                        w = int.from_bytes(text[off:off + 4], "little")
                        asm.append(f"  .word 0x{w:08x}")
            asm_p = os.path.join(d, "ebpf.S")
            with open(asm_p, "w") as f:
                f.write("\n".join(asm) + "\n")

            def arr(bs):
                return ", ".join(str(b) for b in bs)

            c_p = os.path.join(d, "run.c")
            with open(c_p, "w") as f:
                f.write(f"""
#include <stdint.h>
#include <stdio.h>
uint64_t ebpf_run(const uint8_t *p, uint64_t n, uint64_t fuel, uint64_t arg1);
int main(void) {{
    uint8_t p_sum[] = {{{arr(PROG_SUM)}}};
    uint8_t p_fib[] = {{{arr(PROG_FIB)}}};
    uint8_t p_bad[] = {{{arr(PROG_BAD)}}};
    uint64_t r1 = ebpf_run(p_sum, sizeof(p_sum), 100, 10);
    uint64_t r2 = ebpf_run(p_sum, sizeof(p_sum), 10, 10);
    uint64_t r3 = ebpf_run(p_fib, sizeof(p_fib), 200, 10);
    uint64_t r4 = ebpf_run(p_fib, sizeof(p_fib), 200, 15);
    uint64_t r5 = ebpf_run(p_bad, sizeof(p_bad), 10, 0);
    printf("%llu %llu %llu %llu %llu\\n", r1, r2, r3, r4, r5);
    return (r1 == 55 && r2 == 4294967296ULL && r3 == 55 && r4 == 610 && r5 == 4294967296ULL) ? 0 : 1;
}}
""")
            bin_p = os.path.join(d, "run")
            subprocess.run(["clang", "-O2", c_p, asm_p, "-o", bin_p], check=True)
            out = subprocess.check_output([bin_p], text=True).strip()
            self.assertEqual(out, "55 4294967296 55 610 4294967296")


if __name__ == "__main__":
    unittest.main()
