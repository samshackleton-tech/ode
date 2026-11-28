#!/usr/bin/env pypy3
"""End-to-end verification and negative controls for Phase 1 calling conventions and
AArch64 callee-saved vector register (`v8..v15`) preservation (`paper/CALL-CONV-PROPOSAL.md`).

Tests both x86-64 and AArch64:
  - Positive controls:
    1. x86-64 internal helper with custom `calling { in ... out = ... preserves ... }` called
       from an exported C-ABI function with ZERO callee-saved GPR spills (`odeprove` + `odeverify`,
       plus native execution on x86-64 Linux).
    2. AArch64 internal helper with custom `calling { in ... out = ... preserves ... }` called
       from an exported C-ABI function with ZERO callee-saved GPR spills (`odeprove` + `odeverify`,
       plus native execution on AArch64).
    3. AArch64 internal helper with empty `preserves_vec` (and `preserves_vec none`) freely
       writing `v8`..`v15`.
    4. AArch64 default C-ABI boundary test: writing `v7` and `v16` is allowed (`shown`), while
       writing `v8` and `v15` is refused.
    5. Trace-clean custom `out` register: caller branching on a trace-clean custom `out` register
       is `shown`.
  - Negative controls (every one must be refused):
    6. Default AArch64 C-ABI function modifying `v8` or `v15` -> refused at `ret`.
    7. Default AArch64 C-ABI function modifying `v8` inside a loop -> refused at loop/return.
    8. Exported AArch64 C-ABI caller calling an internal helper whose `preserves_vec` is empty
       -> refused because the call may clobber the caller's own `v8..v15`.
    9. Callee clobbering a register listed in its `preserves` list (x86-64 & AArch64) -> refused.
   10. Caller passing argument in C's `rdi`/`x0` instead of custom `in` register -> refused.
   11. Caller reading return value from C's `rax`/`x0` instead of custom `out` register -> refused.
   12. Trace leak through a custom `out` register (branching on a return value that depends on
       an input kept out of the trace) -> refused (`a jump on a flag that may depend on values
       kept out of the trace`).
   13. Direct malformed `.statement` inputs (bypassing `statement.py`) -> refused by Lean's
       `Contract.callingOk` (duplicate `argregs`, `rsp`/`x30`, `retreg` in `keeps`, `retreg`
       clashing with default C ABI `rbx`, `retreg` with abstract `result`, duplicate `keepsvec`).
   14. `statement.py` rejects cross-arch registers, missing/unknown `in` parameters, duplicates,
       reserved registers, and `out` inside `preserves`.
   15. `lang/ode_canon.py` refuses any `calling { ... }` block in an exported auditor `.ocl`
       contract (register names stay out of `.ocl`).

    pypy3 test_call_conv.py        (Lean tests skipped without `lake`)
"""
import ctypes, os, platform, shutil, subprocess, sys, tempfile, textwrap, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path[:0] = [HERE, os.path.join(ROOT, "lang"), os.path.join(ROOT, "kcheck"), os.path.join(ROOT, "arm64")]
import built, lean_verify, obj as aobj, ode, ode_canon, odec, prove, statement

LAKE = lean_verify.LAKE
X86_LINUX = platform.system() == "Linux" and platform.machine() in ("x86_64", "amd64")
ARM_MACHINE = platform.machine() in ("arm64", "aarch64")


def build_ode_pair(d, ode_src, fn_pairs):
    """Compile one or more functions from `ode_src` into ELF objects inside `d`."""
    src_p = os.path.join(d, "prog.ode")
    with open(src_p, "w") as f:
        f.write(textwrap.dedent(ode_src).lstrip())
    out = []
    for ode_fn, sym in fn_pairs:
        obj_p = os.path.join(d, f"{sym}.o")
        odec.build(src_p, ode_fn, obj_p)
        out.append((obj_p, sym))
    return out


def prove_and_verify(spec_text, fns, arch, places_map=None):
    """Build `.statement`, run `prove.prove`, then verify with `odeverify`. Returns (ok, msg, stmt_lines)."""
    places_map = places_map or {}
    with tempfile.TemporaryDirectory() as d:
        lines = statement.statement(spec_text, fns)
        st_p = os.path.join(d, "s")
        pr_p = os.path.join(d, "p")
        targets = [(obj, sym, places_map.get(sym, "")) for obj, sym in fns]
        try:
            prove.prove(spec_text, targets, st_p, pr_p)
        except BaseException as exc:
            return False, str(exc), lines
        ver_bin = os.path.join(HERE, ".lake", "build", "bin", "odeverify")
        rv = subprocess.run([ver_bin, statement.TABLES[arch], st_p, pr_p], capture_output=True, text=True)
        return rv.returncode == 0, (rv.stdout + rv.stderr).strip(), lines


def emit_arm64_asm(fns):
    """Turn verified AArch64 ELF objects into one `.S` file preserving every instruction word
    and `bl` relocation for native execution on macOS Apple Silicon or Linux AArch64."""
    lines = [
        "#ifdef __APPLE__",
        "#define SYM(x) _##x",
        "#else",
        "#define SYM(x) x",
        "#endif",
        ".text",
    ]
    for obj_p, sym in fns:
        e = aobj.Elf(obj_p)
        symbols, symtab = e.symbols()
        shndx, value, size, at = aobj.place(e, sym)
        relocs = e.relocations(shndx, symtab)
        code = e.b[at:at + size]
        lines += [".p2align 2", f".globl SYM({sym})", f"SYM({sym}):"]
        for off in range(0, size, 4):
            rel = relocs.get(value + off)
            if rel is not None:
                target_sym = symbols[rel[1]][0]
                op = "b" if rel[0] == aobj.R_AARCH64_JUMP26 else "bl"
                lines.append(f"  {op} SYM({target_sym})")
            else:
                w = int.from_bytes(code[off:off + 4], "little")
                lines.append(f"  .word 0x{w:08x}")
    return "\n".join(lines) + "\n"


def run_verify_raw(arch, stmt_text, proof_text=""):
    """Invoke `odeverify` directly on raw `.statement` / `.proof` text."""
    with tempfile.TemporaryDirectory() as d:
        st_p = os.path.join(d, "s")
        pr_p = os.path.join(d, "p")
        with open(st_p, "w") as f:
            f.write(stmt_text)
        with open(pr_p, "w") as f:
            f.write(proof_text)
        ver_bin = os.path.join(HERE, ".lake", "build", "bin", "odeverify")
        r = subprocess.run([ver_bin, statement.TABLES[arch], st_p, pr_p], capture_output=True, text=True)
        return r.returncode == 0, (r.stdout + r.stderr).strip()


# ---------------------------------------------------------------------------
# Fixtures: x86-64 custom calling convention (0 callee-saved GPR spills!)
# ---------------------------------------------------------------------------
X86_SPEC = """
def step_fn(a, b) { a + b + 3 }
def quad_fn(x, y) { step_fn(x, y) + step_fn(y, x) + x + y }

contract ode_step_x86(a: number, b: number) {
    requires a < 1000000
    requires b < 1000000
    returns a + b + 3
    trace depends on a, b
    stack 0
    calling {
        in a = r10, b = r11
        out = r9
        preserves rdi, rsi, rdx, rcx, r8, rbx, rbp, r12, r13, r14, r15
    }
}

contract ode_quad_x86(x: number, y: number) {
    requires x < 100000
    requires y < 100000
    returns quad_fn(x, y)
    trace depends on x, y
    stack 8
}
"""

X86_ODE = """
fn step_x86 as "ode_step_x86" {
  mov r9, r10
  add r9, r11
  add r9, 3
  ret
}

fn quad_x86 as "ode_quad_x86" {
  // Keeps x (rdi), y (rsi), and t1 (r8) live across the second call with ZERO push/pop spills!
  mov r10, rdi
  mov r11, rsi
  call ode_step_x86
  mov r8, r9
  mov r10, rsi
  mov r11, rdi
  call ode_step_x86
  mov rax, r8
  add rax, r9
  add rax, rdi
  add rax, rsi
  ret
}
"""

# ---------------------------------------------------------------------------
# Fixtures: AArch64 custom calling convention (0 callee-saved GPR spills!)
# ---------------------------------------------------------------------------
ARM_SPEC = """
def step_fn(a, b) { a + b + 5 }
def quad_fn(x, y) { step_fn(x, y) + step_fn(y, x) + x + y }

contract ode_step_arm(a: number, b: number) {
    requires a < 1000000
    requires b < 1000000
    returns a + b + 5
    trace depends on a, b
    stack 0
    calling {
        in a = x9, b = x10
        out = x11
        preserves x0, x1, x2, x3, x5, x6, x7, x8, x12, x13, x14, x15, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29
    }
}

contract ode_quad_arm(x: number, y: number) {
    requires x < 100000
    requires y < 100000
    returns quad_fn(x, y)
    trace depends on x, y
    stack 16
}
"""

ARM_ODE = """
target arm64

fn step_arm as "ode_step_arm" {
  add x11, x9, x10
  add x11, x11, 5
  ret
}

fn quad_arm as "ode_quad_arm" {
  // Keeps x (x0), y (x1), and t1 (x8) live across the second call with ZERO x19..x29 spills!
  sub sp, sp, 16
  str x30, [sp, 0]
  mov x9, x0
  mov x10, x1
  bl ode_step_arm
  mov x8, x11
  mov x9, x1
  mov x10, x0
  bl ode_step_arm
  add x8, x8, x11
  add x8, x8, x0
  add x0, x8, x1
  ldr x30, [sp, 0]
  add sp, sp, 16
  ret
}
"""


class FrontEndAndCanon(unittest.TestCase):
    """Tests that do not require Lean (`kcheck/ode.py`, `lang/ode_canon.py`, `statement.py`)."""

    def test_ode_canon_refuses_calling_in_ocl(self):
        spec = """
        def f(x) { x + 1 }
        contract ode_f(x: number) {
            requires x < 100
            returns f(x)
            trace depends on x
            stack 0
            calling {
                in x = r10
                out = r11
                preserves rdi, rsi
            }
        }
        """
        with self.assertRaises(ValueError) as ctx:
            ode_canon.canonicalize(spec, contract_name="ode_f")
        self.assertIn("calling", str(ctx.exception))
        self.assertIn(".ocl", str(ctx.exception))

    def test_parser_calling_variants(self):
        spec = """
        def f(a, b) { a + b }
        contract h1(a: number, b: number) {
            requires a < 10
            requires b < 10
            returns f(a, b)
            stack 0
            calling {
                in a = x9
                in b = x10
                out = x11
                preserves
                preserves_vec
            }
        }
        contract h2(a: number) {
            requires a < 10
            returns a
            stack 0
            calling {
                in a = r10
                out = r11
                preserves none
                preserves_vec none
            }
        }
        """
        sp = ode.Spec(spec)
        self.assertEqual(sp.contracts["h1"]["calling"], {
            "in": {"a": "x9", "b": "x10"},
            "out": "x11",
            "preserves": [],
            "preserves_vec": [],
        })
        self.assertEqual(sp.contracts["h2"]["calling"], {
            "in": {"a": "r10"},
            "out": "r11",
            "preserves": [],
            "preserves_vec": [],
        })

    def test_statement_py_rejects_bad_calling_blocks(self):
        bad_cases = [
            ("wrong arch reg x9 on x86-64", False, "in a = x9, b = r11", "not an x86-64 general register"),
            ("wrong arch reg r10 on AArch64", True, "in a = r10, b = x10", "not an AArch64 general register"),
            ("missing param in", False, "in a = r10", "must assign every parameter"),
            ("unknown param in", False, "in a = r10, b = r11, z = r9", "unknown parameter"),
            ("duplicate reg in", False, "in a = r10, b = r10", "more than once"),
            ("reserved rsp", False, "in a = rsp, b = r11", "reserved register"),
            ("reserved x30 on arm64", True, "in a = x30, b = x10", "reserved register"),
            ("out inside preserves", False, "out = r9\npreserves r9, rbx", "cannot also be in `preserves`"),
            ("out clashes with default C ABI rbx", False, "out = rbx", "cannot also be in `preserves`"),
            ("duplicate preserves_vec", True, "preserves_vec v8, v8", "more than once"),
            ("wrong arch vec on arm64", True, "preserves_vec xmm0", "not an AArch64 vector register"),
        ]
        for label, is_arm, body, expected in bad_cases:
            with self.subTest(label=label):
                spec_txt = f"""
                def f(a, b) {{ a + b }}
                contract c(a: number, b: number) {{
                    requires a < 10
                    requires b < 10
                    returns f(a, b)
                    stack 0
                    calling {{
                        {body}
                    }}
                }}
                """
                sp = ode.Spec(spec_txt)
                with self.assertRaises(SystemExit) as ctx:
                    statement.contract_lines(sp.contracts["c"], "c", {}, sp.consts, sp.layouts, is_arm64=is_arm)
                self.assertIn(expected, str(ctx.exception), f"{label}: got {ctx.exception}")

    def test_statement_py_rejects_out_on_abstract_result(self):
        spec_txt = """
        def bs(x) { [x % 256] }
        contract c(a: number, out: 16 bytes) {
            requires a < 10
            returns r
            ensures out[0 .. r] = bs(a)
            stack 0
            calling { out = r10 }
        }
        """
        sp = ode.Spec(spec_txt)
        with self.assertRaises(SystemExit) as ctx:
            statement.contract_lines(sp.contracts["c"], "c", {}, sp.consts, sp.layouts, is_arm64=False)
        self.assertIn("abstract", str(ctx.exception))


@unittest.skipUnless(LAKE, "Lean's lake is not installed")
class CallingConvVerification(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        built.built("odeprove")

    def test_x86_custom_calling_verified_and_native(self):
        with tempfile.TemporaryDirectory() as d:
            fns = build_ode_pair(d, X86_ODE, [("step_x86", "ode_step_x86"), ("quad_x86", "ode_quad_x86")])
            ok, msg, lines = prove_and_verify(X86_SPEC, fns, "x86-64")
            self.assertTrue(ok, f"expected shown on x86-64 custom calling, got:\n{msg}")
            self.assertIn("shown", msg)
            self.assertIn("argregs r10 r11", lines)
            self.assertIn("retreg r9", lines)
            if X86_LINUX and shutil.which("cc"):
                c_p = os.path.join(d, "drv.c")
                bin_p = os.path.join(d, "drv")
                with open(c_p, "w") as f:
                    f.write("""
                    #include <stdint.h>
                    #include <stdio.h>
                    extern uint64_t ode_quad_x86(uint64_t x, uint64_t y);
                    int main(void) {
                        for (uint64_t x = 0; x < 20; x++) {
                            for (uint64_t y = 0; y < 20; y++) {
                                uint64_t want = (x + y + 3) + (y + x + 3) + x + y;
                                uint64_t got = ode_quad_x86(x, y);
                                if (got != want) { printf("FAIL %lu %lu: %lu != %lu\\n", x, y, got, want); return 1; }
                            }
                        }
                        return 0;
                    }
                    """)
                # Combine both .o files and link with driver (make ode_step_x86 visible across .o files)
                r = subprocess.run(["cc", "-O2", c_p, fns[0][0], fns[1][0], "-o", bin_p], capture_output=True, text=True)
                self.assertEqual(r.returncode, 0, r.stderr)
                r2 = subprocess.run([bin_p], capture_output=True, text=True)
                self.assertEqual(r2.returncode, 0, r2.stdout + r2.stderr)

    def test_arm64_custom_calling_verified_and_native(self):
        with tempfile.TemporaryDirectory() as d:
            fns = build_ode_pair(d, ARM_ODE, [("step_arm", "ode_step_arm"), ("quad_arm", "ode_quad_arm")])
            ok, msg, lines = prove_and_verify(ARM_SPEC, fns, "arm64")
            self.assertTrue(ok, f"expected shown on AArch64 custom calling, got:\n{msg}")
            self.assertIn("shown", msg)
            self.assertIn("argregs x9 x10", lines)
            self.assertIn("retreg x11", lines)
            if ARM_MACHINE and shutil.which("cc"):
                c_p = os.path.join(d, "drv.c")
                s_p = os.path.join(d, "both.S")
                bin_p = os.path.join(d, "drv")
                with open(s_p, "w") as f:
                    f.write(emit_arm64_asm(fns))
                with open(c_p, "w") as f:
                    f.write("""
                    #include <stdint.h>
                    #include <stdio.h>
                    extern uint64_t ode_quad_arm(uint64_t x, uint64_t y);
                    int main(void) {
                        for (uint64_t x = 0; x < 20; x++) {
                            for (uint64_t y = 0; y < 20; y++) {
                                uint64_t want = (x + y + 5) + (y + x + 5) + x + y;
                                uint64_t got = ode_quad_arm(x, y);
                                if (got != want) { printf("FAIL %llu %llu: %llu != %llu\\n", (unsigned long long)x, (unsigned long long)y, (unsigned long long)got, (unsigned long long)want); return 1; }
                            }
                        }
                        return 0;
                    }
                    """)
                r = subprocess.run(["cc", "-O2", c_p, s_p, "-o", bin_p], capture_output=True, text=True)
                self.assertEqual(r.returncode, 0, r.stderr)
                r2 = subprocess.run([bin_p], capture_output=True, text=True)
                self.assertEqual(r2.returncode, 0, r2.stdout + r2.stderr)

    def test_arm64_default_c_abi_v8_to_v15_boundary(self):
        """Default AAPCS64 forbids modifying v8..v15, while v7 and v16 are caller-saved."""
        for reg, expect_ok in [("v7", True), ("v8", False), ("v15", False), ("v16", True)]:
            with self.subTest(reg=reg, expect_ok=expect_ok):
                ode_src = f"""
                target arm64
                fn touch_{reg} as "ode_touch_{reg}" {{
                  ld1 {{{reg}.4s}}, [x0]
                  mov x0, x1
                  ret
                }}
                """
                spec_txt = f"""
                contract ode_touch_{reg}(inp: 16 bytes, x: number) {{
                    requires x < 100
                    returns x
                    trace depends on x
                    stack 0
                }}
                """
                with tempfile.TemporaryDirectory() as d:
                    fns = build_ode_pair(d, ode_src, [(f"touch_{reg}", f"ode_touch_{reg}")])
                    ok, msg, _ = prove_and_verify(spec_txt, fns, "arm64")
                    if expect_ok:
                        self.assertTrue(ok, f"expected {reg} to be caller-saved (shown), got:\n{msg}")
                    else:
                        self.assertFalse(ok, f"expected {reg} clobber to be REFUSED under AAPCS64!")
                        self.assertIn("callee-saved vector register", msg)

    def test_arm64_internal_empty_preserves_vec_and_transitive_c_abi_rejection(self):
        """Internal helper with `preserves_vec` (empty) may write v8, but a default C-ABI caller
        calling it must be REFUSED because the call breaks the caller's own AAPCS64 v8..v15 promise."""
        ode_src = """
        target arm64
        fn copy_v8 as "ode_copy_v8_int" {
          ld1 {v8.4s}, [x1]
          st1 {v8.4s}, [x0]
          add x1, x1, 16
          add x0, x0, 16
          ld1 {v8.4s}, [x1]
          st1 {v8.4s}, [x0]
          ret
        }
        fn caller_c as "ode_caller_c" {
          sub sp, sp, 16
          str x30, [sp, 0]
          bl ode_copy_v8_int
          ldr x30, [sp, 0]
          add sp, sp, 16
          ret
        }
        """
        spec_internal = """
        def copy8(d) { [d[i] for i in 0..8] }
        contract ode_copy_v8_int(out: cv, inp: cv) {
            requires disjoint(out, inp, 1)
            ensures out = copy8(inp)
            stack 0
            calling {
                preserves_vec
            }
        }
        contract ode_caller_c(out: cv, inp: cv) {
            requires disjoint(out, inp, 1)
            ensures out = copy8(inp)
            stack 16
        }
        """
        with tempfile.TemporaryDirectory() as d:
            fns = build_ode_pair(d, ode_src, [("copy_v8", "ode_copy_v8_int"), ("caller_c", "ode_caller_c")])
            # 1. Internal helper alone: SHOWN!
            ok_int, msg_int, _ = prove_and_verify(spec_internal, [fns[0]], "arm64")
            self.assertTrue(ok_int, f"internal helper with empty preserves_vec should be shown:\n{msg_int}")
            # 2. Exported C-ABI caller calling it: REFUSED (v8..v15 lost across the call)!
            ok_call, msg_call, _ = prove_and_verify(spec_internal, fns, "arm64")
            self.assertFalse(ok_call, "default C-ABI caller calling empty-preserves_vec helper must be refused!")
            self.assertIn("callee-saved vector register", msg_call)

    def test_arm64_loop_clobber_v8_refused(self):
        """Modifying v8 inside a loop in a default C-ABI AArch64 function must be refused."""
        ode_src = """
        target arm64
        fn loop_v8 as "ode_loop_v8" {
          mov x2, x1
          place {
            name n = x2
            fact n <= x
            decreases n
          }
        @lp:
          cmp x2, 0
          b.eq @done
          ld1 {v8.4s}, [x0]
          sub x2, x2, 1
          b @lp
        @done:
          mov x0, x1
          ret
        }
        """
        spec_txt = """
        contract ode_loop_v8(inp: 16 bytes, x: number) {
            requires x < 100
            returns x
            trace depends on x
            stack 0
        }
        """
        with tempfile.TemporaryDirectory() as d:
            src_p = os.path.join(d, "loop_v8.ode")
            obj_p = os.path.join(d, "ode_loop_v8.o")
            with open(src_p, "w") as f:
                f.write(textwrap.dedent(ode_src).lstrip())
            odec.build(src_p, "loop_v8", obj_p)
            places_txt = odec.places(src_p, "loop_v8")
            ok, msg, _ = prove_and_verify(spec_txt, [(obj_p, "ode_loop_v8")], "arm64", places_map={"ode_loop_v8": places_txt})
            self.assertFalse(ok, "loop clobbering v8 under default AAPCS64 must be refused!")
            self.assertIn("callee-saved vector register", msg)

    def test_callee_clobber_preserved_gpr_refused(self):
        """Callee overwriting a register listed in `preserves` must be refused on both arches."""
        bad_x86 = X86_ODE.replace("  add r9, 3\n", "  add r9, 3\n  mov rdi, r10\n")
        with tempfile.TemporaryDirectory() as d:
            fns = build_ode_pair(d, bad_x86, [("step_x86", "ode_step_x86")])
            ok, msg, _ = prove_and_verify(X86_SPEC, fns, "x86-64")
            self.assertFalse(ok, "x86-64 callee clobbering preserved rdi must be refused!")
            self.assertIn("a register a callee keeps (rdi) does not hold what it held at entry", msg)

        bad_arm = ARM_ODE.replace("  add x11, x11, 5\n", "  add x11, x11, 5\n  mov x0, x9\n")
        with tempfile.TemporaryDirectory() as d:
            fns = build_ode_pair(d, bad_arm, [("step_arm", "ode_step_arm")])
            ok, msg, _ = prove_and_verify(ARM_SPEC, fns, "arm64")
            self.assertFalse(ok, "AArch64 callee clobbering preserved x0 must be refused!")
            self.assertIn("a register a callee keeps (x0) does not hold what it held at entry", msg)

    def test_caller_wrong_in_or_out_reg_refused(self):
        """Caller putting args in C ABI regs or reading result from C ABI rax/x0 must be refused."""
        # Wrong input reg: omit `mov r10, rdi` so r10 does not hold x
        bad_in_x86 = X86_ODE.replace("  mov r10, rdi\n  mov r11, rsi\n", "  mov r11, rsi\n")
        with tempfile.TemporaryDirectory() as d:
            fns = build_ode_pair(d, bad_in_x86, [("step_x86", "ode_step_x86"), ("quad_x86", "ode_quad_x86")])
            ok, _, _ = prove_and_verify(X86_SPEC, fns, "x86-64")
            self.assertFalse(ok, "caller not setting custom input reg r10 must be refused!")

        # Wrong output reg: read rax instead of custom out r9
        self.assertIn("  mov r8, r9\n", X86_ODE)
        bad_out_x86 = X86_ODE.replace("  mov r8, r9\n", "  mov r8, rax\n", 1)
        with tempfile.TemporaryDirectory() as d:
            fns = build_ode_pair(d, bad_out_x86, [("step_x86", "ode_step_x86"), ("quad_x86", "ode_quad_x86")])
            ok, _, _ = prove_and_verify(X86_SPEC, fns, "x86-64")
            self.assertFalse(ok, "caller reading rax instead of custom out reg r9 must be refused!")

        # Wrong input reg on AArch64: omit `mov x9, x0`
        bad_in_arm = ARM_ODE.replace("  mov x9, x0\n  mov x10, x1\n", "  mov x10, x1\n")
        with tempfile.TemporaryDirectory() as d:
            fns = build_ode_pair(d, bad_in_arm, [("step_arm", "ode_step_arm"), ("quad_arm", "ode_quad_arm")])
            ok, _, _ = prove_and_verify(ARM_SPEC, fns, "arm64")
            self.assertFalse(ok, "AArch64 caller not setting custom input reg x9 must be refused!")

    def test_trace_leak_via_custom_out_reg_refused(self):
        """Branching on a custom `out` register whose value depends on an input kept out of the
        trace must be refused; when that input is in `trace depends on`, it must be shown."""
        ode_src = """
        fn trace_step as "ode_tstep" {
          mov r9, r10
          add r9, r11
          ret
        }
        fn caller as "ode_tcaller" {
          mov r10, rdi
          mov r11, rsi
          call ode_tstep
          cmp r9, 0
          je @zero
          mov rax, 1
          ret
        @zero:
          xor eax, eax
          ret
        }
        """
        spec_leak = """
        def sum2(a, b) { a + b }
        def nz(a, b) { if sum2(a, b) == 0 then 0 else 1 }
        contract ode_tstep(a: number, b: number) {
            requires a < 100
            requires b < 100
            returns sum2(a, b)
            trace depends on b
            stack 0
            calling {
                in a = r10, b = r11
                out = r9
                preserves rdi, rsi, rbx, rbp, r12, r13, r14, r15
            }
        }
        contract ode_tcaller(x: number, y: number) {
            requires x < 100
            requires y < 100
            returns nz(x, y)
            trace depends on y
            stack 8
        }
        """
        spec_clean = spec_leak.replace("trace depends on y", "trace depends on x, y")
        with tempfile.TemporaryDirectory() as d:
            fns = build_ode_pair(d, ode_src, [("trace_step", "ode_tstep"), ("caller", "ode_tcaller")])
            ok_leak, msg_leak, _ = prove_and_verify(spec_leak, fns, "x86-64")
            self.assertFalse(ok_leak, "branching on custom out reg r9 kept out of the trace must be refused!")
            self.assertIn("a jump on a flag that may depend on values kept out of the trace", msg_leak)

            ok_clean, msg_clean, _ = prove_and_verify(spec_clean, fns, "x86-64")
            self.assertTrue(ok_clean, f"branching on trace-clean custom out reg r9 should be shown:\n{msg_clean}")

    def test_malformed_statement_refused_by_lean_callingOk(self):
        """Bypass `statement.py` and verify Lean's `Contract.callingOk` refuses every invalid
        custom calling convention directly inside `odeverify`."""
        base_x86 = (
            "fn f\n"
            "i 0 1 .ret\n"
            "arg a number\n"
            "returns (name a)\n"
            "stack 0\n"
        )
        base_arm = (
            "fn f\n"
            "machine arm64\n"
            "i 0 4 .ret\n"
            "arg a number\n"
            "returns (name a)\n"
            "stack 0\n"
        )
        cases = [
            ("x86-64", base_x86 + "argregs rsp\n"),
            ("x86-64", base_x86 + "arg b number\nargregs r10 r10\n"),
            ("x86-64", base_x86 + "retreg r10\nkeeps r10\n"),
            ("x86-64", base_x86 + "retreg rbx\n"),
            ("x86-64", base_x86.replace("returns (name a)\n", "result r\n") + "retreg r10\n"),
            ("arm64", base_arm + "argregs x30\n"),
            ("arm64", base_arm + "argregs sp\n"),
            ("arm64", base_arm + "keepsvec v8 v8\n"),
        ]
        for arch, stmt in cases:
            with self.subTest(arch=arch, line=stmt.strip().splitlines()[-1]):
                ok, msg = run_verify_raw(arch, stmt)
                self.assertFalse(ok, f"expected Lean callingOk refusal for:\n{stmt}")
                self.assertIn("invalid custom calling convention", msg)


@unittest.skipUnless(LAKE, "Lean 4 (lake) not installed")
class TailCallsAndZeroStackArm64(unittest.TestCase):
    """Phase 2 calling conventions: verified tail calls (`jmp` / `b`) on x86-64 & AArch64,
    zero-stack AArch64 callers keeping `x30` in a custom callee-preserved register, and
    negative controls."""

    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        built.built("odeprove")

    def test_x86_tail_call_positive_and_native_and_bundle_audit(self):
        """x86-64 `stack 0` caller tail-jumps (`jmp`) to a custom-calling helper (and also
        supports a conditional branch where one arm returns directly and the other tail-jumps),
        runs natively on x86-64 Linux, and passes `ode pack` + `ode audit`."""
        ode_src = """
        target x86_64

        fn tail_add as "ode_tail_add" {
            add r10, r11
            mov rax, r10
            ret
        }

        fn dispatch as "ode_tail_dispatch" {
            cmp rdi, 0
            jne @use_tail
            mov rax, rsi
            ret
        @use_tail:
            mov r10, rdi
            mov r11, rsi
            jmp ode_tail_add
        }
        """
        spec = """
        def sum2(a, b) { a + b }

        contract ode_tail_add(a: number, b: number) {
            requires a < 1000
            requires b < 1000
            returns sum2(a, b)
            trace depends on a, b
            stack 0
            calling {
                in a = r10, b = r11
                out = rax
                preserves rbx, rbp, r12, r13, r14, r15
            }
        }

        contract ode_tail_dispatch(x: number, y: number) {
            requires x < 1000
            requires y < 1000
            returns sum2(x, y)
            trace depends on x, y
            stack 0
        }
        """
        with tempfile.TemporaryDirectory() as d:
            fns = build_ode_pair(d, ode_src, [("tail_add", "ode_tail_add"), ("dispatch", "ode_tail_dispatch")])
            ok, msg, _ = prove_and_verify(spec, fns, "x86-64")
            self.assertTrue(ok, f"x86-64 tail call failed:\n{msg}")

            # Verify unified `.ode` multi-function `ode pack` + `ode audit` handles R_X86_64_PLT32 tail jumps!
            import ode_audit, ode_tool
            unified_p = os.path.join(d, "prog_unified.ode")
            with open(unified_p, "w") as f:
                f.write(textwrap.dedent("""
                def sum2(a, b) { a + b }

                fn tail_add(a: number, b: number)
                    requires a < 1000
                    requires b < 1000
                    returns sum2(a, b)
                    trace depends on a, b
                {
                    for x86_64 stack 0 calling {
                        in a = r10, b = r11
                        out = rax
                        preserves rbx, rbp, r12, r13, r14, r15
                    } {
                        add r10, r11
                        mov rax, r10
                        ret
                    }
                }

                fn dispatch(x: number, y: number)
                    requires x < 1000
                    requires y < 1000
                    returns sum2(x, y)
                    trace depends on x, y
                {
                    for x86_64 stack 0 {
                        cmp rdi, 0
                        jne @use_tail
                        mov rax, rsi
                        ret
                    @use_tail:
                        mov r10, rdi
                        mov r11, rsi
                        jmp tail_add
                    }
                }
                """).lstrip())
            bundle_o = os.path.join(d, "bundle.o")
            bundle_p = os.path.join(d, "bundle.proof")
            rc = ode_tool.main([
                "pack", unified_p,
                "--fn", "dispatch", "--out", bundle_o, "--proof", bundle_p,
            ])
            self.assertEqual(rc, 0, "ode pack failed on x86-64 tail-call bundle")
            aud = ode_audit.audit_binary(bundle_o, proof_path=bundle_p)
            self.assertEqual(aud["verdict"], "shown", f"ode audit refused x86-64 tail-call bundle: {aud}")

            if X86_LINUX and shutil.which("cc"):
                so = os.path.join(d, "libt.so")
                r = subprocess.run(["cc", "-shared", "-o", so, fns[0][0], fns[1][0]], capture_output=True, text=True)
                self.assertEqual(r.returncode, 0, r.stderr)
                lib = ctypes.CDLL(so)
                fn = lib.ode_tail_dispatch
                fn.argtypes = [ctypes.c_uint64, ctypes.c_uint64]
                fn.restype = ctypes.c_uint64
                for x, y in [(0, 42), (1, 2), (500, 499), (999, 999)]:
                    self.assertEqual(fn(x, y), x + y)

    def test_arm64_tail_call_positive_and_native_and_bundle_audit(self):
        """AArch64 `stack 0` caller tail-branches (`b`) to a custom-calling helper, runs
        natively on Apple Silicon / Linux AArch64, and passes `ode pack` + `ode audit`."""
        ode_src = """
        target arm64

        fn tail_add as "ode_tail_add_arm" {
            add x10, x10, x11
            mov x0, x10
            ret
        }

        fn dispatch as "ode_tail_dispatch_arm" {
            cmp x0, 0
            b.ne @use_tail
            mov x0, x1
            ret
        @use_tail:
            mov x10, x0
            mov x11, x1
            b ode_tail_add_arm
        }
        """
        spec = """
        def sum2(a, b) { a + b }

        contract ode_tail_add_arm(a: number, b: number) {
            requires a < 1000
            requires b < 1000
            returns sum2(a, b)
            trace depends on a, b
            stack 0
            calling {
                in a = x10, b = x11
                out = x0
                preserves x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29
                preserves_vec v8, v9, v10, v11, v12, v13, v14, v15
            }
        }

        contract ode_tail_dispatch_arm(x: number, y: number) {
            requires x < 1000
            requires y < 1000
            returns sum2(x, y)
            trace depends on x, y
            stack 0
        }
        """
        with tempfile.TemporaryDirectory() as d:
            fns = build_ode_pair(d, ode_src, [("tail_add", "ode_tail_add_arm"), ("dispatch", "ode_tail_dispatch_arm")])
            ok, msg, _ = prove_and_verify(spec, fns, "arm64")
            self.assertTrue(ok, f"AArch64 tail call failed:\n{msg}")

            import ode_audit, ode_tool
            unified_p = os.path.join(d, "prog_unified.ode")
            with open(unified_p, "w") as f:
                f.write(textwrap.dedent("""
                def sum2(a, b) { a + b }

                fn tail_add(a: number, b: number)
                    requires a < 1000
                    requires b < 1000
                    returns sum2(a, b)
                    trace depends on a, b
                {
                    for arm64 stack 0 calling {
                        in a = x10, b = x11
                        out = x0
                        preserves x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29
                        preserves_vec v8, v9, v10, v11, v12, v13, v14, v15
                    } {
                        add x10, x10, x11
                        mov x0, x10
                        ret
                    }
                }

                fn dispatch(x: number, y: number)
                    requires x < 1000
                    requires y < 1000
                    returns sum2(x, y)
                    trace depends on x, y
                {
                    for arm64 stack 0 {
                        cmp x0, 0
                        b.ne @use_tail
                        mov x0, x1
                        ret
                    @use_tail:
                        mov x10, x0
                        mov x11, x1
                        b tail_add
                    }
                }
                """).lstrip())
            bundle_o = os.path.join(d, "bundle.o")
            bundle_p = os.path.join(d, "bundle.proof")
            rc = ode_tool.main([
                "pack", unified_p,
                "--fn", "dispatch", "--out", bundle_o, "--proof", bundle_p,
            ])
            self.assertEqual(rc, 0, "ode pack failed on AArch64 tail-call bundle")
            aud = ode_audit.audit_binary(bundle_o, proof_path=bundle_p)
            self.assertEqual(aud["verdict"], "shown", f"ode audit refused AArch64 tail-call bundle: {aud}")

            if ARM_MACHINE and shutil.which("cc"):
                asm_p = os.path.join(d, "both.S")
                so_p = os.path.join(d, "libt.dylib" if platform.system() == "Darwin" else "libt.so")
                with open(asm_p, "w") as f:
                    f.write(emit_arm64_asm(fns))
                r = subprocess.run(["cc", "-shared", "-o", so_p, asm_p], capture_output=True, text=True)
                self.assertEqual(r.returncode, 0, r.stderr)
                lib = ctypes.CDLL(so_p)
                fn = lib.ode_tail_dispatch_arm
                fn.argtypes = [ctypes.c_uint64, ctypes.c_uint64]
                fn.restype = ctypes.c_uint64
                for x, y in [(0, 42), (1, 2), (500, 499), (999, 999)]:
                    self.assertEqual(fn(x, y), x + y)

    def test_arm64_zero_stack_caller_link_in_x15(self):
        """AArch64 non-leaf caller with `stack 0`: saves `x30` in caller-saved scratch `x15`,
        calls a custom-calling helper that lists `x15` in `preserves`, restores `x30`, and
        returns — zero stack writes on AArch64, proved sound and executed natively."""
        ode_src = """
        target arm64

        fn leaf_step as "ode_leaf_x15" {
            add x10, x10, x11
            ret
        }

        fn caller as "ode_zero_stack_arm" {
            mov x15, x30
            mov x10, x0
            mov x11, x1
            bl ode_leaf_x15
            add x0, x10, x2
            mov x30, x15
            ret
        }
        """
        spec = """
        contract ode_leaf_x15(a: number, b: number) {
            requires a < 1000
            requires b < 1000
            returns a + b
            trace depends on a, b
            stack 0
            calling {
                in a = x10, b = x11
                out = x10
                preserves x2, x15, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29
                preserves_vec v8, v9, v10, v11, v12, v13, v14, v15
            }
        }

        contract ode_zero_stack_arm(a: number, b: number, c: number) {
            requires a < 1000
            requires b < 1000
            requires c < 1000
            returns a + b + c
            trace depends on a, b, c
            stack 0
        }
        """
        with tempfile.TemporaryDirectory() as d:
            fns = build_ode_pair(d, ode_src, [("leaf_step", "ode_leaf_x15"), ("caller", "ode_zero_stack_arm")])
            ok, msg, _ = prove_and_verify(spec, fns, "arm64")
            self.assertTrue(ok, f"AArch64 stack-0 x15 link save failed:\n{msg}")

            if ARM_MACHINE and shutil.which("cc"):
                asm_p = os.path.join(d, "both.S")
                so_p = os.path.join(d, "libz.dylib" if platform.system() == "Darwin" else "libz.so")
                with open(asm_p, "w") as f:
                    f.write(emit_arm64_asm(fns))
                r = subprocess.run(["cc", "-shared", "-o", so_p, asm_p], capture_output=True, text=True)
                self.assertEqual(r.returncode, 0, r.stderr)
                lib = ctypes.CDLL(so_p)
                fn = lib.ode_zero_stack_arm
                fn.argtypes = [ctypes.c_uint64, ctypes.c_uint64, ctypes.c_uint64]
                fn.restype = ctypes.c_uint64
                for a, b, c in [(0, 0, 0), (10, 20, 30), (999, 999, 999)]:
                    self.assertEqual(fn(a, b, c), a + b + c)

    def test_tail_call_negative_controls_x86(self):
        """Every invalid x86-64 tail call must be refused by the Lean verifier:
        (1) sp != 0, (2) callee does not preserve caller's keeps, (3) caller clobbered its own
        keeps before jmp, (4) callee stack > caller stack, (5) trace leak, (6) self tail call."""
        base_spec = """
        def sum2(a, b) { a + b }

        contract ode_tcallee(a: number, b: number) {
            requires a < 1000
            requires b < 1000
            returns sum2(a, b)
            trace depends on a, b
            stack 0
            calling {
                in a = rdi, b = rsi
                out = rax
                preserves rbx, rbp, r12, r13, r14, r15
            }
        }

        contract ode_tcaller(x: number, y: number) {
            requires x < 1000
            requires y < 1000
            returns sum2(x, y)
            trace depends on x, y
            stack 0
        }
        """
        # 1. sp != 0 at tail jump
        ode_sp = """
        target x86_64
        fn callee as "ode_tcallee" {
            mov rax, rdi
            add rax, rsi
            ret
        }
        fn caller as "ode_tcaller" {
            sub rsp, 16
            jmp ode_tcallee
        }
        """
        with tempfile.TemporaryDirectory() as d:
            fns = build_ode_pair(d, ode_sp, [("callee", "ode_tcallee"), ("caller", "ode_tcaller")])
            ok, msg, _ = prove_and_verify(base_spec.replace("stack 0\n        }", "stack 16\n        }"), fns, "x86-64")
            self.assertFalse(ok, "tail call with sp != 0 must be refused!")

        # 2. callee omits r12 from preserves (caller promises to preserve r12)
        ode_ok = """
        target x86_64
        fn callee as "ode_tcallee" {
            mov rax, rdi
            add rax, rsi
            ret
        }
        fn caller as "ode_tcaller" {
            jmp ode_tcallee
        }
        """
        spec_no_r12 = base_spec.replace("preserves rbx, rbp, r12, r13, r14, r15", "preserves rbx, rbp, r13, r14, r15")
        with tempfile.TemporaryDirectory() as d:
            fns = build_ode_pair(d, ode_ok, [("callee", "ode_tcallee"), ("caller", "ode_tcaller")])
            ok, msg, _ = prove_and_verify(spec_no_r12, fns, "x86-64")
            self.assertFalse(ok, "tail call whose callee does not preserve caller keeps must be refused!")

        # 3. caller clobbers rbx and forgets to restore it before tail jump
        ode_clobber = """
        target x86_64
        fn callee as "ode_tcallee" {
            mov rax, rdi
            add rax, rsi
            ret
        }
        fn caller as "ode_tcaller" {
            mov rbx, 7
            jmp ode_tcallee
        }
        """
        with tempfile.TemporaryDirectory() as d:
            fns = build_ode_pair(d, ode_clobber, [("callee", "ode_tcallee"), ("caller", "ode_tcaller")])
            ok, msg, _ = prove_and_verify(base_spec, fns, "x86-64")
            self.assertFalse(ok, "tail call with changed caller callee-saved reg must be refused!")

        # 4. callee stack (64) exceeds caller stack (32)
        spec_big_stack = base_spec.replace("stack 0\n            calling", "stack 64\n            calling").replace("stack 0\n        }", "stack 32\n        }")
        with tempfile.TemporaryDirectory() as d:
            fns = build_ode_pair(d, ode_ok, [("callee", "ode_tcallee"), ("caller", "ode_tcaller")])
            ok, msg, _ = prove_and_verify(spec_big_stack, fns, "x86-64")
            self.assertFalse(ok, "tail call whose callee stack exceeds caller stack must be refused!")

        # 5. trace leak: caller keeps x out of trace, tail-jumps to callee whose trace depends on a (= x)
        spec_leak = base_spec.replace("trace depends on x, y", "trace depends on y")
        with tempfile.TemporaryDirectory() as d:
            fns = build_ode_pair(d, ode_ok, [("callee", "ode_tcallee"), ("caller", "ode_tcaller")])
            ok, msg, _ = prove_and_verify(spec_leak, fns, "x86-64")
            self.assertFalse(ok, "tail call leaking value kept out of trace must be refused!")

        # 6. self tail call (bypassing decreases)
        ode_self = """
        target x86_64
        fn self_tail as "ode_tself" {
            jmp ode_tself
        }
        """
        spec_self = """
        contract ode_tself(x: number) {
            requires x < 100
            returns x
            trace depends on x
            stack 0
        }
        """
        with tempfile.TemporaryDirectory() as d:
            fns = build_ode_pair(d, ode_self, [("self_tail", "ode_tself")])
            ok, msg, _ = prove_and_verify(spec_self, fns, "x86-64")
            self.assertFalse(ok, "self tail call must be refused!")

    def test_tail_call_negative_controls_arm64(self):
        """AArch64 negative controls: clobbered `x30` before `b callee`, `sp != 0`, and
        callee omitting `v8` from `preserves_vec` must all be refused."""
        base_spec = """
        def sum2(a, b) { a + b }

        contract ode_arm_tc(a: number, b: number) {
            requires a < 1000
            requires b < 1000
            returns sum2(a, b)
            trace depends on a, b
            stack 0
            calling {
                in a = x0, b = x1
                out = x0
                preserves x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29
                preserves_vec v8, v9, v10, v11, v12, v13, v14, v15
            }
        }

        contract ode_arm_tcaller(x: number, y: number) {
            requires x < 1000
            requires y < 1000
            returns sum2(x, y)
            trace depends on x, y
            stack 16
        }
        """
        # 1. clobbered x30 before b
        ode_lr = """
        target arm64
        fn callee as "ode_arm_tc" {
            add x0, x0, x1
            ret
        }
        fn caller as "ode_arm_tcaller" {
            mov x30, x0
            b ode_arm_tc
        }
        """
        with tempfile.TemporaryDirectory() as d:
            fns = build_ode_pair(d, ode_lr, [("callee", "ode_arm_tc"), ("caller", "ode_arm_tcaller")])
            ok, msg, _ = prove_and_verify(base_spec, fns, "arm64")
            self.assertFalse(ok, "AArch64 tail call with clobbered x30 must be refused!")

        # 2. sp != 0 before b
        ode_sp = """
        target arm64
        fn callee as "ode_arm_tc" {
            add x0, x0, x1
            ret
        }
        fn caller as "ode_arm_tcaller" {
            sub sp, sp, 16
            b ode_arm_tc
        }
        """
        with tempfile.TemporaryDirectory() as d:
            fns = build_ode_pair(d, ode_sp, [("callee", "ode_arm_tc"), ("caller", "ode_arm_tcaller")])
            ok, msg, _ = prove_and_verify(base_spec, fns, "arm64")
            self.assertFalse(ok, "AArch64 tail call with sp != 0 must be refused!")

        # 3. callee omits v8 from preserves_vec while caller promises default C ABI v8..v15
        ode_ok = """
        target arm64
        fn callee as "ode_arm_tc" {
            add x0, x0, x1
            ret
        }
        fn caller as "ode_arm_tcaller" {
            b ode_arm_tc
        }
        """
        spec_nov8 = base_spec.replace("preserves_vec v8, v9", "preserves_vec v9")
        with tempfile.TemporaryDirectory() as d:
            fns = build_ode_pair(d, ode_ok, [("callee", "ode_arm_tc"), ("caller", "ode_arm_tcaller")])
            ok, msg, _ = prove_and_verify(spec_nov8, fns, "arm64")
            self.assertFalse(ok, "AArch64 tail call whose callee drops v8 from preserves_vec must be refused!")


if __name__ == "__main__":
    unittest.main()
