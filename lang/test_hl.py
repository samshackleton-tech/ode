#!/usr/bin/env python3
"""End-to-end tests for Unified Structured Wirth High-Level Ode (`lang/ode_hl.py`)."""
import os, subprocess, sys, tempfile, time, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for p in (HERE, os.path.join(ROOT, "proof-core"), os.path.join(ROOT, "kcheck")):
    if p not in sys.path:
        sys.path.insert(0, p)

import ode_audit
import ode_tool


STD_STORES = (os.path.join(ROOT, "std"),)


def _dual_verify(testcase, src_text, fn_name, targets=("x86_64", "arm64"), check_verify2=True):
    odeverify = os.path.join(ROOT, "proof-core", ".lake", "build", "bin", "odeverify")
    if not os.path.exists(odeverify):
        testcase.skipTest("odeverify binary not built")
    for target in targets:
        with tempfile.TemporaryDirectory() as d:
            src_p = os.path.join(d, f"{fn_name}.ode")
            with open(src_p, "w", encoding="utf-8") as f:
                f.write(src_text)
            out_o = os.path.join(d, "out.o")
            out_p = os.path.join(d, "out.proof")
            res = ode_audit.pack_verified(src_p, None, out_o, out_p, fn_name=fn_name, target=target, stores=STD_STORES)
            testcase.assertEqual(res["verdict"], "shown", f"{fn_name}/{target}: {res}")
            if check_verify2:
                dump = os.path.join(d, "dump.sh")
                st_p, pf_p = os.path.join(d, "st.txt"), os.path.join(d, "pf.txt")
                with open(dump, "w", encoding="utf-8") as f:
                    f.write(f"#!/bin/sh\ncp \"$2\" {st_p}\ncp \"$3\" {pf_p}\necho shown\n")
                os.chmod(dump, 0o755)
                ode_audit.audit_binary(out_o, out_p, verify_bin=dump)
                tab = os.path.join(ROOT, "arm64", "arm64.tab") if target == "arm64" else os.path.join(ROOT, "core", "x86.tab")
                r2 = subprocess.run(
                    [sys.executable, os.path.join(ROOT, "proof-core", "verify2.py"), tab, st_p, pf_p],
                    capture_output=True, text=True,
                )
                testcase.assertEqual(r2.returncode, 0, f"{fn_name}/{target} verify2: {r2.stdout}{r2.stderr}")
                testcase.assertIn("shown (", r2.stdout)


class TestHighLevelOde(unittest.TestCase):
    def test_01_portable_ct_b64_dec_select_and_wrap(self):
        """One portable High-Level Ode `b64_dec` with `select` + `-%` dual-verifies on both x86_64 and arm64."""
        src = """
def b64_dec(c) {
    if 65 <= c && c <= 90 then c - 1
    else if 97 <= c && c <= 122 then c - 7
    else if 48 <= c && c <= 57 then c + 68
    else if c == 43 then 126
    else if c == 47 then 127
    else 0
}

fn hl_b64_dec(c: u8) -> u64
    returns b64_dec(c)
    trace depends on nothing
{
    var r: u64 := 0
    r := select(65 <= c && c <= 90,  c -% 1,  r)
    r := select(97 <= c && c <= 122, c -% 7,  r)
    r := select(48 <= c && c <= 57,  c + 68,  r)
    r := select(c == 43, 126, r)
    r := select(c == 47, 127, r)
    return r
}
"""
        _dual_verify(self, src, "hl_b64_dec")

    def test_02_wrap_range_check_passes_and_exact_refuses(self):
        """Single-compare `(c -% 65) <= 25` dual-verifies via `t wrap` + `t split`; exact `c - 65` is refused."""
        src_wrap = """
def cap_val_spec(c) {
    if 65 <= c && c <= 90 then c - 65 else 255
}

fn hl_cap_val(c: u8) -> u64
    returns cap_val_spec(c)
    trace depends on nothing
{
    let d := c -% 65
    return select(d <= 25, d, 255)
}
"""
        _dual_verify(self, src_wrap, "hl_cap_val")

        src_exact = src_wrap.replace("c -% 65", "c - 65")
        with tempfile.TemporaryDirectory() as d:
            p = os.path.join(d, "exact_bad.ode")
            with open(p, "w", encoding="utf-8") as f:
                f.write(src_exact)
            with self.assertRaises(BaseException):
                ode_audit.pack_verified(p, None, os.path.join(d, "b.o"), os.path.join(d, "b.proof"),
                                        fn_name="hl_cap_val", target="x86_64")

    def test_03_auto_outer_context_inheritance_and_for_loop(self):
        """Early-exit guards (`if n < 1`, `if lim > n`) auto-inherit into `for i in 0..lim` with zero manual `place`."""
        src = """
def sum_prefix(a, i, lim, acc) {
    if i >= lim then acc
    else sum_prefix(a, i + 1, lim, acc + a[i])
}

def checked_sum(a, n) {
    if n < 1 then 0
    else if a[0] > n then 0
    else sum_prefix(a, 0, a[0], 0)
}

fn hl_checked_sum(a: n bytes, n: u64) -> u64
    requires 0 <= n, n <= 4096
    returns checked_sum(a, n)
    trace depends on a, n
{
    if n < 1 { return 0 }
    let lim := a[0]
    if lim > n { return 0 }
    var acc: u64 := 0
    for i in 0..lim
        maintains acc <= i * 255
        maintains checked_sum(a, n) == sum_prefix(a, i, lim, acc)
    {
        acc += a[i]
    }
    return acc
}
"""
        _dual_verify(self, src, "hl_checked_sum")

    def test_04_portable_output_buffer_loop(self):
        """Portable `for i in 0..64 writes out[.. i] = ...` with `out[i] := ...` dual-verifies on both arches."""
        src = """
def inc_bytes(src) {
    [ (src[j] + 1) % 256 for j in 0..64 ]
}

fn hl_inc_copy(out: 64 bytes, src: n bytes, n: u64) -> u64
    requires no_overlap(out, src)
    requires 64 <= n, n <= 64
    ensures out = inc_bytes(src)
    returns 1
    trace depends on n
{
    for i in 0..64
        writes out[.. i] = inc_bytes(src)
    {
        let b := src[i]
        out[i] := (b + 1) & 255
    }
    return 1
}
"""
        _dual_verify(self, src, "hl_inc_copy")

    def test_05_recursive_linear_stack_and_tail_call(self):
        """Portable recursive `stack 32 + 32 * d` (no manual prologue/epilogue) and tail-call helper both verify."""
        src_rec = """
def all_zero(a, n, d) {
    if d == 0 then 1
    else if a[d - 1] != 0 then 0
    else all_zero(a, n, d - 1)
}

fn hl_rec_zero(a: n bytes, n: u64, d: u64) -> u64
    requires 0 <= d, d <= n, n <= 64
    returns all_zero(a, n, d)
    decreases d
    trace depends on a, n, d
    stack 32 + 32 * d
{
    if d == 0 { return 1 }
    let idx := d - 1
    if a[idx] != 0 { return 0 }
    return hl_rec_zero(a, n, idx)
}
"""
        # Note: `return hl_rec_zero(...)` lowers to a verified tail call (`jmp`/`b`) when leaf/tail!
        _dual_verify(self, src_rec, "hl_rec_zero", check_verify2=True)

        src_tail = """
def add3(x) { x + 3 }
def wrap_add3(x) { add3(x) }

fn hl_add3(x: u64) -> u64
    requires 0 <= x, x <= 1000
    returns add3(x)
    trace depends on x
{
    return x + 3
}

fn hl_wrap_add3(x: u64) -> u64
    requires 0 <= x, x <= 1000
    returns wrap_add3(x)
    trace depends on x
{
    return hl_add3(x)
}
"""
        _dual_verify(self, src_tail, "hl_wrap_add3")

    def test_06_instant_advise_asm_under_50ms(self):
        """`ode advise --asm` returns var->reg map, 1-to-1 lowering, and pipeline estimate in < 50 ms."""
        src = """
def b64_dec(c) {
    if 65 <= c && c <= 90 then c - 1 else 0
}

fn hl_fast(c: u8) -> u64
    returns b64_dec(c)
    trace depends on nothing
{
    var r: u64 := 0
    r := select(65 <= c && c <= 90, c -% 1, r)
    return r
}
"""
        with tempfile.TemporaryDirectory() as d:
            p = os.path.join(d, "fast.ode")
            with open(p, "w", encoding="utf-8") as f:
                f.write(src)
            # Warm import once, then time both x86_64 and arm64
            ode_tool.run_advise(p, fn_name="hl_fast", target="x86_64", show_asm=True)
            for target in ("x86_64", "arm64"):
                t0 = time.monotonic()
                res = ode_tool.run_advise(p, fn_name="hl_fast", target=target, show_asm=True)
                dt_ms = (time.monotonic() - t0) * 1000.0
                self.assertIn("High-Level Ode lowering (hl_fast,", res["advice_text"])
                self.assertIn("spills: 0", res["advice_text"])
                self.assertIn("variables:", res["advice_text"])
                self.assertIn("lowering (source -> exact instructions):", res["advice_text"])
                self.assertLess(dt_ms, 150.0, f"advise --asm on {target} took {dt_ms:.1f} ms")

    def test_07_option2_default_fast_calling_and_c_abi_boundary(self):
        """Plain `fn` stays C-free: Ode->Ode calls (incl. across `use` modules) get Ode fast calling; `--c-abi` exports C ABI."""
        import ode_unified
        helper_src = """
fn inc2_fn(x: u64) -> u64
    requires 0 <= x, x <= 2000
    returns x + 2
    trace depends on x
{
    return x + 2
}
"""
        with tempfile.TemporaryDirectory() as d:
            hp = os.path.join(d, "helper.ode")
            mp = os.path.join(d, "main.ode")
            tp = os.path.join(d, "top.ode")
            with open(hp, "w", encoding="utf-8") as f:
                f.write(helper_src)
            h_helper = ode_unified.module_hash_file(hp)
            main_src = f"""
use h = "{h_helper}"

fn entry_inc4(x: u64) -> u64
    requires 0 <= x, x <= 1500
    returns x + 4
    trace depends on x
{{
    let a := h.inc2_fn(x)
    return h.inc2_fn(a)
}}
"""
            with open(mp, "w", encoding="utf-8") as f:
                f.write(main_src)
            h_main = ode_unified.module_hash_file(mp)
            top_src = f"""
use m = "{h_main}"

fn top_inc8(x: u64) -> u64
    requires 0 <= x, x <= 1000
    returns x + 8
    trace depends on x
{{
    let a := m.entry_inc4(x)
    return m.entry_inc4(a)
}}
"""
            with open(tp, "w", encoding="utf-8") as f:
                f.write(top_src)
            # When `main.ode` is imported by `top.ode`, BOTH `inc2_fn` AND `entry_inc4` get Ode fast calling automatically!
            p_top = ode_unified.parse_unified(top_src, tp, c_abi_fn="top_inc8")
            self.assertIsNone(p_top["fns_by_name"]["top_inc8"]["impls"]["x86_64"]["calling_text"])
            for fn in p_top["fns"]:
                if fn["name"] != "top_inc8":
                    ct = fn["impls"]["x86_64"]["calling_text"]
                    self.assertIsNotNone(ct, f"imported fn {fn['name']} must get Ode fast calling")
                    self.assertIn("preserves", ct)
            # End-to-end `pack_verified` with `--c-abi` on both `main.ode` (2-file) and `top.ode` (3-file) on both arches
            for target in ("x86_64", "arm64"):
                out_o = os.path.join(d, f"inc8_{target}.o")
                out_p = os.path.join(d, f"inc8_{target}.proof")
                res = ode_audit.pack_verified(tp, None, out_o, out_p, fn_name="top_inc8", target=target, c_abi=True)
                self.assertEqual(res["verdict"], "shown", f"{target}: {res}")

    def test_08_parallel_move_call_marshaling_and_arg_swap(self):
        """Calling a helper with swapped/aliased register arguments never clobbers an unread argument."""
        src = """
def sub_ord(a, b) { a + 2 * b }

fn helper_ord(a: u64, b: u64) -> u64
    requires 0 <= a, a <= 1000, 0 <= b, b <= 1000
    returns sub_ord(a, b)
    trace depends on a, b
{
    return a + b + b
}

fn call_swapped(x: u64, y: u64) -> u64
    requires 0 <= x, x <= 1000, 0 <= y, y <= 1000
    returns sub_ord(y, x)
    trace depends on x, y
{
    return helper_ord(y, x)
}
"""
        _dual_verify(self, src, "call_swapped", check_verify2=True)

    def test_09_simd_u32x4_unroll_vprord_and_ext(self):
        """Typed `u32x4` + `unroll` + `std/vec.ode`'s `vec.rotl32` (`vprord` on avx512, `rev32.8h` on arm64) + `ext4` verify with 0 spills."""
        src = """
use vec = "7zjhuvtcpskuqp5hojlblzp4sohvyncst5we3ol4ohbhk43ujbxa"  // std/vec.ode

def arx1(w) {
    let s0 = ((w[0] + w[4]) ^ w[4]) >>> 16
    let s1 = ((w[1] + w[5]) ^ w[5]) >>> 16
    let s2 = ((w[2] + w[6]) ^ w[6]) >>> 16
    let s3 = ((w[3] + w[7]) ^ w[7]) >>> 16
    [ s1, s2, s3, s0 ]
}

fn hl_vec_add(out: 16 bytes, inp: 32 bytes)
    requires no_overlap(out, inp)
    ensures out = bytes_of(arx1(words(inp)))
    stack 0
{
    for x86_64 needs avx needs avx512 {
        var a: u32x4 := inp.u32x4(0)
        var b: u32x4 := inp.u32x4(16)
        a +%= b
        a ^= b
        a := vec.rotl32(a, 16)
        a := ext4(a, a)
        out.u32x4(0) := a
    }
    for arm64 {
        var a: u32x4 := inp.u32x4(0)
        var b: u32x4 := inp.u32x4(16)
        a +%= b
        a ^= b
        a := vec.rotl32(a, 16)
        a := ext4(a, a)
        out.u32x4(0) := a
    }
}
"""
        _dual_verify(self, src, "hl_vec_add", check_verify2=False)

    def test_10_nested_rotl_non_avx512_and_u8_var_name(self):
        """2-reg vector scratch handles `vec.rotl32(u8 + b, 12)` on both arm64 and non-avx512 x86_64, and `u8` as var name."""
        src = """
use vec = "7zjhuvtcpskuqp5hojlblzp4sohvyncst5we3ol4ohbhk43ujbxa"  // std/vec.ode

def arx12(w) {
    let s0 = (w[0] + w[4]) >>> 20
    let s1 = (w[1] + w[5]) >>> 20
    let s2 = (w[2] + w[6]) >>> 20
    let s3 = (w[3] + w[7]) >>> 20
    [ s0, s1, s2, s3 ]
}

fn hl_rotl_nested(out: 16 bytes, inp: 32 bytes)
    requires no_overlap(out, inp)
    ensures out = bytes_of(arx12(words(inp)))
{
    for x86_64 needs avx {
        let u8: u32x4 := inp.u32x4(0)
        var b: u32x4 := inp.u32x4(16)
        b := vec.rotl32(u8 + b, 12)
        out.u32x4(0) := b
    }
    for arm64 {
        let u8: u32x4 := inp.u32x4(0)
        var b: u32x4 := inp.u32x4(16)
        b := vec.rotl32(u8 + b, 12)
        out.u32x4(0) := b
    }
}
"""
        _dual_verify(self, src, "hl_rotl_nested", check_verify2=False)

    def test_11_disjoint_or_select_wrap_div_mod_and_large_arm_imm(self):
        """Proved `disjointOr`, auto-wrapped `select(c >= 97, c - 97, 0)`, `/`/`%` by powers of 2, and >16-bit arm64 imm."""
        src = """
def pack_bits(a, b) {
    (a % 4) * 262144 + (if 97 <= b && b <= 122 then b - 97 else 0)
}

fn hl_pack_bits(a: u64, b: u8) -> u64
    requires 0 <= a, a <= 1000
    returns pack_bits(a, b)
    trace depends on
{
    let hi := (a % 4) << 18
    let m := 131071
    let lo := select(b >= 97 && b <= 122, b - 97, 0) & m
    let half := (hi | lo) / 1
    return half
}
"""
        _dual_verify(self, src, "hl_pack_bits")

    def test_12_congruence_t_same_alias_inheritance_and_step2(self):
        """Pure-function congruence (`t same`), dead `let` alias inheritance, and `for ... step 2` parity."""
        src = """
def pair_sum(p, k, lim, acc) {
    if k >= lim then acc
    else pair_sum(p, k + 1, lim, acc + p[k])
}

fn hl_step2_sum(p: n bytes, n: number, m: number) -> u64
    requires 0 <= m, m <= 32
    requires n == 2 * m
    returns pair_sum(p, 0, n, 0)
    trace depends on n, m
{
    let lim := m << 1
    var acc: u64 := 0
    for k in 0..lim step 2
        maintains acc <= k * 255
        maintains pair_sum(p, 0, lim, 0) == pair_sum(p, k, lim, acc)
    {
        let b0 := p[k]
        let b1 := p[k + 1]
        acc += b0 + b1
    }
    return acc
}
"""
        _dual_verify(self, src, "hl_step2_sum")

    def test_13_concrete_prefilter_fast_refusal(self):
        """Buggy scalar function is caught immediately by the concrete pre-filter with a counterexample."""
        src = """
fn hl_bad_add(x: u64) -> u64
    requires 0 <= x, x <= 100
    returns x + 1
    trace depends on x
{
    return x + 2
}
"""
        with tempfile.TemporaryDirectory() as d:
            p = os.path.join(d, "bad.ode")
            with open(p, "w", encoding="utf-8") as f:
                f.write(src)
            with self.assertRaises(ode_audit.PackProofError) as ctx:
                ode_audit.pack_verified(
                    p, None, os.path.join(d, "o.o"), os.path.join(d, "o.p"),
                    fn_name="hl_bad_add", target="x86_64", c_abi=True,
                )
            self.assertIn("refused with a proof", str(ctx.exception))
            self.assertIn("counterexample", ctx.exception.extra_note)

    def test_14_direct_fn_for_arch_and_arm64_neon_zip(self):
        """Direct `fn ... for x86_64 { ... } for arm64 { ... }` without outer braces + NEON `zip1`/`zip2`."""
        src = """
def zip32_words(w) {
    [ w[0], w[4], w[1], w[5], w[2], w[6], w[3], w[7] ]
}

fn hl_zip_demo(out: 32 bytes, src: 32 bytes)
    requires no_overlap(out, src)
    ensures out = bytes_of(zip32_words(words(src)))
    stack 0
for x86_64 needs avx {
    let a: u32x4 := src.u32x4(0)
    let b: u32x4 := src.u32x4(16)
    let lo: u32x4 := unpacklo32(a, b)
    let hi: u32x4 := unpackhi32(a, b)
    out.u32x4(0) := lo
    out.u32x4(16) := hi
}
for arm64 {
    let a: u32x4 := src.u32x4(0)
    let b: u32x4 := src.u32x4(16)
    let lo: u32x4 := unpacklo32(a, b)
    let hi: u32x4 := unpackhi32(a, b)
    out.u32x4(0) := lo
    out.u32x4(16) := hi
}
"""
        _dual_verify(self, src, "hl_zip_demo", check_verify2=False)

    def test_15_zero_stack_x86_fixed_scratch_and_const_fold(self):
        """4 live locals + const `let mask := 255` + `return select(s == 100, 1, 0)` fits in `stack 0` on x86-64."""
        src = """
fn hl_zero_stack_sel(p: n bytes, n: number) -> u64
    requires 8 <= n, n <= 64
    returns if p[0] + p[1] + p[2] + p[3] == 100 then 1 else 0
    trace depends on n
    stack 0
{
    let mask := 255
    let a := p[0] & mask
    let b := p[1] & mask
    let c := p[2] & mask
    let d := p[3] & mask
    var s: u64 := a + b
    s += c
    s += d
    return select(s == 100, 1, 0)
}
"""
        _dual_verify(self, src, "hl_zero_stack_sel")

    def test_16_place_join_alias_and_scalar_xor_diagnostic(self):
        """`place { ... }` works as a mid-function join in High-Level Ode; scalar `^` gives a clear error."""
        src = """
def step_fn(x) {
    if x < 50 then x + 10 else x + 20
}

fn hl_place_join(x: u64) -> u64
    requires 0 <= x, x <= 100
    returns step_fn(x)
    trace depends on x
{
    var r: u64 := 0
    if x < 50 {
        r := x + 10
    } else {
        r := x + 20
    }
    place {
        r == step_fn(x)
    }
    return r
}
"""
        _dual_verify(self, src, "hl_place_join")

        bad_xor = """
fn hl_bad_xor(a: u64, b: u64) -> u64
    requires 0 <= a, a <= 10, 0 <= b, b <= 10
    returns a
    trace depends on
{
    return a ^ b
}
"""
        with tempfile.TemporaryDirectory() as d:
            p = os.path.join(d, "bad_xor.ode")
            with open(p, "w", encoding="utf-8") as f:
                f.write(bad_xor)
            with self.assertRaises(Exception) as ctx:
                ode_audit.pack_verified(
                    p, None, os.path.join(d, "o.o"), os.path.join(d, "o.p"),
                    fn_name="hl_bad_xor", target="x86_64", c_abi=True,
                )
            self.assertIn("vector types", str(ctx.exception))

    def test_17_prefilter_fixed_len_out_buffer(self):
        """Concrete pre-filter handles fixed-size `requires n >= 16, n <= 16` + `ensures out = ...`."""
        src = """
def copy_inc(src) {
    [ (src[j] + 1) % 256 for j in 0..16 ]
}

fn hl_bad_copy(src: n bytes, out: 16 bytes, n: number) -> u64
    requires n >= 16, n <= 16
    requires no_overlap(src, out)
    returns 0
    ensures out = copy_inc(src)
    trace depends on n
{
    for i in 0..16 {
        out[i] := src[i]
    }
    return 0
}
"""
        with tempfile.TemporaryDirectory() as d:
            p = os.path.join(d, "bad_copy.ode")
            with open(p, "w", encoding="utf-8") as f:
                f.write(src)
            with self.assertRaises(ode_audit.PackProofError) as ctx:
                ode_audit.pack_verified(
                    p, None, os.path.join(d, "o.o"), os.path.join(d, "o.p"),
                    fn_name="hl_bad_copy", target="x86_64", c_abi=True,
                )
            self.assertIn("refused with a proof", str(ctx.exception))
            self.assertIn("counterexample", ctx.exception.extra_note)

    def test_18_deterministic_branch_fuel_max_lives(self):
        """Deterministic `ODE_PROVE_MAX_LIVES` stops exponential sequential branch explosion cleanly."""
        sum_terms = " + ".join(f"(if p[{i}] == 65 then 1 else 0)" for i in range(10))
        lines = [
            f"def count65(p) {{ {sum_terms} }}",
            "fn hl_branch_bomb(p: n bytes, n: number) -> u64",
            "    requires n >= 16, n <= 16",
            "    returns count65(p)",
            "    trace depends on n",
            "{",
            "    var s: u64 := 0",
        ]
        for i in range(10):
            lines.append(f"    let c{i} := p[{i}]")
            lines.append(f"    s := select(c{i} == 65, s + 1, s)")
        lines.append("    return s")
        lines.append("}")
        src = "\n".join(lines) + "\n"
        old = os.environ.get("ODE_PROVE_MAX_LIVES")
        os.environ["ODE_PROVE_MAX_LIVES"] = "40"
        try:
            with tempfile.TemporaryDirectory() as d:
                p = os.path.join(d, "bomb.ode")
                with open(p, "w", encoding="utf-8") as f:
                    f.write(src)
                with self.assertRaises(ode_audit.PackProofError) as ctx:
                    ode_audit.pack_verified(
                        p, None, os.path.join(d, "o.o"), os.path.join(d, "o.p"),
                        fn_name="hl_branch_bomb", target="x86_64", c_abi=True,
                    )
                self.assertIn("search budget exceeded", str(ctx.exception))
                self.assertIn("helper `fn`", ctx.exception.extra_note)
        finally:
            if old is None:
                os.environ.pop("ODE_PROVE_MAX_LIVES", None)
            else:
                os.environ["ODE_PROVE_MAX_LIVES"] = old

    def test_19_wirth_inline_fn_var_and_sha256_big_sigma(self):
        """Wirth `inline fn (var ...)` by-reference expansion + portable 9-line `sha256_big_sigma_4x` on both arches."""
        src = """
use vec = "7zjhuvtcpskuqp5hojlblzp4sohvyncst5we3ol4ohbhk43ujbxa"  // std/vec.ode

def sig0(x) { (x >>> 2) ^ (x >>> 13) ^ (x >>> 22) }
def sig1(x) { (x >>> 6) ^ (x >>> 11) ^ (x >>> 25) }
def big_sigma_4x(a, e) {
    [ sig0(a[0]) + sig1(e[0]),
      sig0(a[1]) + sig1(e[1]),
      sig0(a[2]) + sig1(e[2]),
      sig0(a[3]) + sig1(e[3]) ]
}

inline fn add_sig1(var acc: u32x4, e: u32x4) {
    let s1: u32x4 := vec.rotr32(e, 6) ^ vec.rotr32(e, 11) ^ vec.rotr32(e, 25)
    acc +%= s1
}

fn hl_sha256_big_sigma_4x(out: 16 bytes, a: 16 bytes, e: 16 bytes)
    requires no_overlap(out, a, e)
    ensures out = bytes_of(big_sigma_4x(words(a), words(e)))
    stack 0
for x86_64 needs avx {
    let va: u32x4 := a.u32x4(0)
    let ve: u32x4 := e.u32x4(0)
    var acc: u32x4 := vec.rotr32(va, 2) ^ vec.rotr32(va, 13) ^ vec.rotr32(va, 22)
    add_sig1(acc, ve)
    out.u32x4(0) := acc
}
for arm64 {
    let va: u32x4 := a.u32x4(0)
    let ve: u32x4 := e.u32x4(0)
    var acc: u32x4 := vec.rotr32(va, 2) ^ vec.rotr32(va, 13) ^ vec.rotr32(va, 22)
    add_sig1(acc, ve)
    out.u32x4(0) := acc
}
"""
        _dual_verify(self, src, "hl_sha256_big_sigma_4x", check_verify2=False)

    def test_20_blake3_compress1_pure_hl_both_arches(self):
        """Full 7-round BLAKE3 1-block compression in 100% pure High-Level Ode verifies on both x86_64 and arm64."""
        import ode_unified
        spec_src = os.path.join(HERE, "..", "proof-core", "examples", "hashr_arm64_fast", "blake3_spec.ode")
        h_b3 = ode_unified.module_hash_file(spec_src)
        src = ("""
use b3 = "__H_B3__"  // blake3_spec.ode
use vec = "7zjhuvtcpskuqp5hojlblzp4sohvyncst5we3ol4ohbhk43ujbxa"  // std/vec.ode

data one_iv = 0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A

inline fn g_half(var a: u32x4, var b: u32x4, var c: u32x4, var d: u32x4, mx: u32x4, my: u32x4) {
    a +%= mx
    a +%= b
    d := vec.rotr32(d ^ a, 16)
    c +%= d
    b := vec.rotr32(b ^ c, 12)
    a +%= my
    a +%= b
    d := vec.rotr32(d ^ a, 8)
    c +%= d
    b := vec.rotr32(b ^ c, 7)
}

inline fn perm_x86(var m0: u32x4, var m1: u32x4, var m2: u32x4, var m3: u32x4) {
    let t0: u32x4 := shufps(m0, m1, 214)
    let nm1_a: u32x4 := shuf32(m0, 0x0F)
    let nm0: u32x4 := shuf32(t0, 0x39)
    let t1: u32x4 := shufps(m2, m3, 250)
    let nm1: u32x4 := blend32(nm1_a, t1, 0xAA)
    let t2: u32x4 := unpacklo64(m3, m1)
    let t3: u32x4 := blend32(t2, m2, 0x88)
    let nm2: u32x4 := shuf32(t3, 0x78)
    let t4: u32x4 := unpackhi32(m1, m3)
    let t5: u32x4 := unpacklo32(m2, t4)
    let nm3: u32x4 := shuf32(t5, 0x1E)
    m0 := nm0
    m1 := nm1
    m2 := nm2
    m3 := nm3
}

inline fn perm_arm(var m0: u32x4, var m1: u32x4, var m2: u32x4, var m3: u32x4) {
    let t0: u32x4 := uzp2_32(m1, m0)
    let t1: u32x4 := unpacklo64(m0, t0)
    let t2: u32x4 := ext8(m0, m0)
    let t3: u32x4 := ext4(m2, m0)
    let t4: u32x4 := uzp2_32(m0, t3)
    let t5: u32x4 := ext12(m3, m0)
    let nm0: u32x4 := ext4(t1, t2)
    let u0: u32x4 := uzp1_32(m3, m1)
    let u1: u32x4 := ext12(m2, m3)
    let u2: u32x4 := unpackhi32(m1, m3)
    let u3: u32x4 := unpacklo64(m2, u2)
    let u6: u32x4 := ext4(m1, m2)
    let nm1: u32x4 := ext4(t4, t5)
    let nm2: u32x4 := uzp1_32(u0, u1)
    let nm3: u32x4 := uzp2_32(u3, u6)
    m0 := nm0
    m1 := nm1
    m2 := nm2
    m3 := nm3
}

fn hl_b3_compress1(h: cv, m: block, length: word, t: counter, flags: low word)
    requires no_overlap(h, m)
    ensures h = b3.compress(h, m, t, length, flags)
    stack 0
for x86_64 needs avx needs avx512 {
    var v0: u32x4 := h.u32x4(0)
    var v1: u32x4 := h.u32x4(16)
    var v2: u32x4 := const_u32x4(one_iv)
    var v3: u32x4 := vec.pack_u64x2(t, length + (flags << 32))
    let b0: u32x4 := m.u32x4(0)
    let b1: u32x4 := m.u32x4(16)
    var m0: u32x4 := uzp1_32(b0, b1)
    var m1: u32x4 := uzp2_32(b0, b1)
    let b2: u32x4 := m.u32x4(32)
    let b3: u32x4 := m.u32x4(48)
    var m2: u32x4 := shuf32(uzp1_32(b2, b3), 0x93)
    var m3: u32x4 := shuf32(uzp2_32(b2, b3), 0x93)
    for r in 0..6 unroll {
        g_half(v0, v1, v2, v3, m0, m1)
        v0 := shuf32(v0, 0x93)
        v3 := shuf32(v3, 0x4E)
        v2 := shuf32(v2, 0x39)
        g_half(v0, v1, v2, v3, m2, m3)
        v0 := shuf32(v0, 0x39)
        v3 := shuf32(v3, 0x4E)
        v2 := shuf32(v2, 0x93)
        perm_x86(m0, m1, m2, m3)
    }
    g_half(v0, v1, v2, v3, m0, m1)
    v0 := shuf32(v0, 0x93)
    v3 := shuf32(v3, 0x4E)
    v2 := shuf32(v2, 0x39)
    g_half(v0, v1, v2, v3, m2, m3)
    v0 := shuf32(v0, 0x39)
    v3 := shuf32(v3, 0x4E)
    v2 := shuf32(v2, 0x93)
    h.u32x4(0) := v0 ^ v2
    h.u32x4(16) := v1 ^ v3
}
for arm64 {
    var v0: u32x4 := h.u32x4(0)
    var v1: u32x4 := h.u32x4(16)
    var v2: u32x4 := vec.const_u32x4(0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A)
    var v3: u32x4 := vec.pack_u64x2(t, length + (flags << 32))
    let b0: u32x4 := m.u32x4(0)
    let b1: u32x4 := m.u32x4(16)
    var m0: u32x4 := uzp1_32(b0, b1)
    var m1: u32x4 := uzp2_32(b0, b1)
    let b2: u32x4 := m.u32x4(32)
    let b3: u32x4 := m.u32x4(48)
    let p2: u32x4 := uzp1_32(b2, b3)
    let p3: u32x4 := uzp2_32(b2, b3)
    var m2: u32x4 := ext12(p2, p2)
    var m3: u32x4 := ext12(p3, p3)
    for r in 0..6 unroll {
        g_half(v0, v1, v2, v3, m0, m1)
        v0 := ext12(v0, v0)
        v3 := ext8(v3, v3)
        v2 := ext4(v2, v2)
        g_half(v0, v1, v2, v3, m2, m3)
        v0 := ext4(v0, v0)
        v3 := ext8(v3, v3)
        v2 := ext12(v2, v2)
        perm_arm(m0, m1, m2, m3)
    }
    g_half(v0, v1, v2, v3, m0, m1)
    v0 := ext12(v0, v0)
    v3 := ext8(v3, v3)
    v2 := ext4(v2, v2)
    g_half(v0, v1, v2, v3, m2, m3)
    v0 := ext4(v0, v0)
    v3 := ext8(v3, v3)
    v2 := ext12(v2, v2)
    h.u32x4(0) := v0 ^ v2
    h.u32x4(16) := v1 ^ v3
}
""").replace("__H_B3__", h_b3)
        import shutil
        with tempfile.TemporaryDirectory() as d:
            shutil.copy2(spec_src, os.path.join(d, "blake3_spec.ode"))
            src_p = os.path.join(d, "b3_c1.ode")
            with open(src_p, "w", encoding="utf-8") as f:
                f.write(src)
            for tgt in ("x86_64", "arm64"):
                out_o = os.path.join(d, f"c1_{tgt}.o")
                out_p = os.path.join(d, f"c1_{tgt}.proof")
                res = ode_audit.pack_verified(src_p, None, out_o, out_p, fn_name="hl_b3_compress1", target=tgt, c_abi=True, stores=STD_STORES)
                self.assertEqual(res["verdict"], "shown")

    def test_21_nested_select_no_scratch_clobber(self):
        """Nested `select(c1, t1, select(c2, t2, select(c3, t3, d)))` preserves outer `then_e` across inner selects."""
        src = """\
def classify(c) {
    if c == 1 then 10
    else if c == 2 then 20
    else if c == 3 then 30
    else 99
}

fn classify_fn(c: u8) -> u64
    returns classify(c)
    trace depends on nothing
{
    return select(c == 1, 10, select(c == 2, 20, select(c == 3, 30, 99)))
}
"""
        _dual_verify(self, src, "classify_fn")

    def test_22_store_compound_3x_index_no_val_clobber(self):
        """`out[3 * g] := expr` with non-power-of-2 index never clobbers the value register before storing."""
        src = """\
def pack_triples_spec(inp) {
    [ if j % 3 == 0 then ((inp[(j / 3) * 4] % 64) * 4 + (inp[(j / 3) * 4 + 1] % 64) / 16)
      else if j % 3 == 1 then inp[(j / 3) * 4 + 2]
      else inp[(j / 3) * 4 + 3]
      for j in 0..12 ]
}

fn pack_triples(inp: n bytes, n: u64, out: 12 bytes) -> u64
    requires n == 16
    requires no_overlap(inp, out)
    ensures out = pack_triples_spec(inp)
    returns 1
    trace depends on n
{
    for g in 0..4
        writes out[.. 3 * g] = pack_triples_spec(inp)
    {
        let a := inp[4 * g] & 63
        let b := inp[4 * g + 1] & 63
        out[3 * g] := (a << 2) + (b >> 4)
        out[3 * g + 1] := inp[4 * g + 2]
        out[3 * g + 2] := inp[4 * g + 3]
    }
    return 1
}
"""
        _dual_verify(self, src, "pack_triples")

    def test_23_return_binop_preserves_param_x0_arm64(self):
        """`return 256 * buf[pos + 2] + buf[pos + 3]` must not clobber `buf` (`x0` on arm64) while evaluating LHS."""
        src = """\
def read_be16(buf, pos) { 256 * buf[pos + 2] + buf[pos + 3] }

fn get_be16(buf: n bytes, n: u64, pos: u64) -> u64
    requires pos + 4 <= n, n <= 1024
    returns read_be16(buf, pos)
    trace depends on buf, n, pos
{
    return 256 * buf[pos + 2] + buf[pos + 3]
}
"""
        _dual_verify(self, src, "get_be16")

    def test_24_symbolic_stack_propagation_and_auto_needs_avx(self):
        """Caller omitting `stack` inherits callee's symbolic `stack`; `u32x4` on x86_64 auto-adds `needs avx`."""
        src_stk = """\
def all_zero(buf, i, rem) {
    if rem == 0 then 1
    else if buf[i] != 0 then 0
    else all_zero(buf, i + 1, rem - 1)
}

fn check_rec(buf: n bytes, n: u64, i: u64, rem: u64) -> u64
    requires i + rem <= n, n <= 64
    returns all_zero(buf, i, rem)
    decreases rem
    stack 64 + 64 * rem
    trace depends on buf, n, i, rem
{
    if rem == 0 { return 1 }
    if buf[i] != 0 { return 0 }
    return check_rec(buf, n, i + 1, rem - 1)
}

fn check_entry(buf: n bytes, n: u64) -> u64
    requires n <= 64
    returns all_zero(buf, 0, n)
    trace depends on buf, n
{
    return check_rec(buf, n, 0, n)
}
"""
        _dual_verify(self, src_stk, "check_entry")

        src_avx = """\
def add4_w(a, b) {
    [ a[0] + b[0], a[1] + b[1], a[2] + b[2], a[3] + b[3] ]
}

fn add_vec4(out: 16 bytes, a: 16 bytes, b: 16 bytes)
    requires no_overlap(out, a, b)
    ensures out = bytes_of(add4_w(words(a), words(b)))
    trace depends on nothing
{
    let va: u32x4 := a.u32x4(0)
    let vb: u32x4 := b.u32x4(0)
    out.u32x4(0) := va +% vb
}
"""
        _dual_verify(self, src_avx, "add_vec4", check_verify2=False)

    def test_25_select_compound_cond_no_trailing_ret_and_maintains_diag(self):
        """Regression tests for `select(b & 1 == 0, ...)`, `if/else` return without dead `ret`, `maintains` `&&`/`||`, and 3-range `t split`."""
        src = """\
def low_zero_spec(b, u) {
    if u == 0 then 1
    else if u == 1 then (if b % 2 == 0 then 1 else 0)
    else if b % 4 == 0 then 1 else 0
}

fn hl_low_zero(b: u64, u: u64) -> u64
    requires u <= 2
    returns low_zero_spec(b, u)
    trace depends on b, u
    stack 0
{
    if u == 0 { return 1 }
    if u == 1 { return select(b & 1 == 0, 1, 0) }
    if (b & 3) == 0 {
        return 1
    } else {
        return 0
    }
}
"""
        _dual_verify(self, src, "hl_low_zero")

        # 3-range branchless `t split` (A-Z, a-z, 0-9) + `maintains a && b`
        src_3r = """\
def is_alnum(c) {
    if 65 <= c && c <= 90 then 1
    else if 97 <= c && c <= 122 then 1
    else if 48 <= c && c <= 57 then 1
    else 0
}

fn hl_is_alnum(c: u8) -> u64
    returns is_alnum(c)
    trace depends on nothing
    stack 0
{
    let t65 := c -% 65
    let t97 := c -% 97
    let t48 := c -% 48
    let a := select(t65 <= 25, 1, 0)
    let b := select(t97 <= 25, 1, 0)
    let d := select(t48 <= 9, 1, 0)
    return a + b + d
}
"""
        _dual_verify(self, src_3r, "hl_is_alnum")

        # `maintains` with `||` produces a clear compile diagnostic (not an opaque verifier refusal)
        src_bad = """\
fn bad_or(a: n bytes, n: u64) -> u64
    requires n <= 16
    returns 0
    trace depends on n
{
    var x: u64 := 0
    for i in 0..n
        maintains x == 0 || x == 1
    {
        x := 0
    }
    return x
}
"""
        with tempfile.TemporaryDirectory() as d:
            p = os.path.join(d, "bad_or.ode")
            with open(p, "w", encoding="utf-8") as f:
                f.write(src_bad)
            with self.assertRaises(BaseException) as ctx:
                ode_audit.pack_verified(p, None, os.path.join(d, "a.o"), os.path.join(d, "a.p"),
                                        fn_name="bad_or", target="x86_64", c_abi=True)
            self.assertIn("`maintains` cannot use `||`", str(ctx.exception))

    def test_26_spec_meta_and_fast_fail_interactive_diagnostics(self):
        """High-Level Ode source lines + `odeprove` `need spec` metadata + `ODE_PROVE_FAST_FAIL=1`."""
        import ode_tool
        # 1. Source line mapping + `vars:` + High-Level Ode hint on a refusal
        src_bad = """\
def sum_bytes(a, n) {
    if n == 0 then 0 else sum_bytes(a, n - 1) + a[n - 1]
}
fn hl_missing_maintains(a: n bytes, n: u64) -> u64
    requires n <= 64
    returns sum_bytes(a, n)
    trace depends on n
{
    var acc: u64 := 0
    for i in 0..n
        maintains acc <= 255 * i
    {
        acc += a[i]
    }
    return acc
}
"""
        with tempfile.TemporaryDirectory() as d:
            p = os.path.join(d, "bad.ode")
            with open(p, "w", encoding="utf-8") as f:
                f.write(src_bad)
            with self.assertRaises(ode_audit.PackProofError) as ctx:
                ode_audit.pack_verified(p, None, os.path.join(d, "a.o"), os.path.join(d, "a.p"),
                                        fn_name="hl_missing_maintains", target="x86_64")
            exc = ctx.exception
            by_sym = {exc.fn_sym: exc.info} if (exc.fn_sym and exc.info) else {}
            diag, _ = ode_tool.format_source_diagnostic(
                by_sym, exc.pc, exc.fn_sym, exc.reason,
                target=exc.target, contract=exc.contract, spec_text=exc.spec_text,
            )
            self.assertIn("return acc", diag)
            self.assertIn("vars:", diag)
            self.assertIn("maintains", diag)

        # 2. `parse_spec_need` renders `odeprove` `m goal` + `d` metadata cleanly
        spec_reason = (
            "need spec\nc 3\no 0\nh 1\ny 0\n"
            "m goal value ipv4_sum 2\n"
            "d 0 ipv4_sum 0 1 0 1\n"
            "d 1 ipv4_valid 1 0 1 0\n"
            "d 2 ipv4_sum 1 0 1 1\n"
        )
        diag2, _ = ode_tool.format_source_diagnostic({}, None, "ipv4_valid", spec_reason, target="arm64")
        self.assertIn("unproved specification goal: `ipv4_sum(...) == <computed value>`", diag2)
        self.assertIn("`ipv4_sum` (1 open, 1 resolved)", diag2)
        self.assertIn("`ipv4_valid` (1 open)", diag2)

        # 3. `ODE_PROVE_FAST_FAIL=1` stops promptly on churn and asks interactive question
        src_churn = """\
def f_many(x) {
    if x == 0 then 0 else if x == 1 then 1 else if x == 2 then 2 else if x == 3 then 3
    else if x == 4 then 4 else if x == 5 then 5 else if x == 6 then 6 else 7
}
fn hl_fast_fail_demo(x: u8) -> u64
    returns f_many(x)
    trace depends on nothing
{
    var r: u64 := 7
    r := select(x == 0, 0, r)
    r := select(x == 1, 1, r)
    r := select(x == 2, 2, r)
    r := select(x == 3, 3, r)
    r := select(x == 4, 4, r)
    r := select(x == 5, 5, r)
    r := select(x == 6, 6, r)
    r := select(x == 7, 99, r)
    return r
}
"""
        old_ef = os.environ.get("ODE_PROVE_EFFORT")
        old_ff = os.environ.get("ODE_PROVE_FAST_FAIL")
        old_ch = os.environ.get("ODE_PROVE_MAX_CHURN")
        old_pf = os.environ.get("ODE_PREFILTER")
        try:
            os.environ["ODE_PROVE_EFFORT"] = "fast"
            os.environ["ODE_PROVE_FAST_FAIL"] = "1"
            os.environ["ODE_PROVE_MAX_CHURN"] = "8"
            os.environ["ODE_PREFILTER"] = "0"
            with tempfile.TemporaryDirectory() as d:
                p = os.path.join(d, "ff.ode")
                with open(p, "w", encoding="utf-8") as f:
                    f.write(src_churn)
                with self.assertRaises(ode_audit.PackProofError) as ctx:
                    ode_audit.pack_verified(p, None, os.path.join(d, "a.o"), os.path.join(d, "a.p"),
                                            fn_name="hl_fast_fail_demo", target="x86_64")
                self.assertIn("fast-fail prover stopped early", ctx.exception.extra_note)
                self.assertIn("What did you mean here", ctx.exception.extra_note)
        finally:
            for k, v in (("ODE_PROVE_EFFORT", old_ef), ("ODE_PROVE_FAST_FAIL", old_ff), ("ODE_PROVE_MAX_CHURN", old_ch), ("ODE_PREFILTER", old_pf)):
                if v is None:
                    os.environ.pop(k, None)
                else:
                    os.environ[k] = v

    def test_27_select_calls_nested_and_recursive_helpers(self):
        """Option 3: functions using `select` (`cmov`/`csel`) can call and tail-call
        arbitrary helpers (including helpers that call other helpers and helpers with
        `result depends on` / hidden results) on both x86_64 and arm64."""
        src = """\
fn leaf_add(x: u64) -> u64
    requires x < 100
    returns x + 1
    trace depends on nothing
{
    return x + 1
}

fn mid_add(x: u64) -> u64
    requires x < 100
    returns x + 2
    trace depends on nothing
{
    let t: u64 := leaf_add(x)
    return t + 1
}

fn select_calls_nested(x: u64, flag: u64) -> u64
    requires x < 100
    returns if flag == 0 then x + 2 else x + 3
    trace depends on nothing
{
    let a: u64 := mid_add(x)
    let b: u64 := a + 1
    return select(flag == 0, a, b)
}

fn select_tail_nested(x: u64, flag: u64) -> u64
    requires x < 50
    returns if flag == 0 then x + 2 else x + 3
    trace depends on nothing
{
    let y: u64 := select(flag == 0, x, x + 1)
    return mid_add(y)
}
"""
        for arch in ("x86_64", "arm64"):
            with tempfile.TemporaryDirectory() as d:
                p = os.path.join(d, "sel_call.ode")
                with open(p, "w", encoding="utf-8") as f:
                    f.write(src)
                for fn in ("select_calls_nested", "select_tail_nested"):
                    o_path = os.path.join(d, f"{fn}.o")
                    pr_path = os.path.join(d, f"{fn}.proof")
                    res = ode_audit.pack_verified(p, None, o_path, pr_path, fn_name=fn, target=arch)
                    self.assertEqual(res["verdict"], "shown", f"{fn} on {arch}: {res}")
                    aud = ode_audit.audit_binary(o_path, pr_path)
                    self.assertEqual(aud["verdict"], "shown", f"audit {fn} on {arch}: {aud}")

    def test_28_ode_regalloc_stack_var_arm64_u32_dedup_place_and_try_harder(self):
        """Verify bottom-up exact keeps + pass-through params, dead param reclamation,
        explicit `stack var` with `ODE_HL_NO_SPILL=1`, arm64 `buf.u32`/`buf[i]` stores,
        merged consecutive `place`s, and `--effort fast` -> `--try-harder` rescue."""
        import ode_unified
        # 1. Pass-through params (`buf`, `n`) + bottom-up exact `keeps` + dead param reclamation
        src_pt = """\
fn helper_sum(buf: n bytes, n: number, idx: u64) -> u64
    requires idx < n
    returns buf[idx] + 1
    trace depends on buf, n, idx
{
    let b: u64 := buf[idx]
    return b + 1
}

fn caller_pt(buf: n bytes, n: number, a: u64, b: u64) -> u64
    requires n >= 2
    requires a < 100
    requires b < 100
    returns buf[0] + buf[1] + a + b + 2
    trace depends on buf, n, a, b
{
    let ab: u64 := a + b
    let x0: u64 := helper_sum(buf, n, 0)
    let x1: u64 := helper_sum(buf, n, 1)
    return x0 + x1 + ab
}
"""
        old_env = {k: os.environ.get(k) for k in ("ODE_HL_NO_SPILL", "ODE_HL_AUTO_KEEPS", "ODE_HL_RECLAIM_PARAMS")}
        try:
            os.environ["ODE_HL_NO_SPILL"] = "1"
            os.environ["ODE_HL_AUTO_KEEPS"] = "1"
            os.environ["ODE_HL_RECLAIM_PARAMS"] = "1"
            parsed = ode_unified.parse_unified(src_pt, src="pt.ode")
            caller_rec = [f for f in parsed["fns"] if f["name"] == "caller_pt"][0]
            # On x86_64: `buf` (rdi) and `n` (rsi) stay in-place across `helper_sum(buf, n, ...)` -> ZERO copied copies for buf/n!
            vm_x86 = {nm: (loc, note) for nm, _, loc, note in caller_rec["impls"]["x86_64"]["hl_meta"]["var_map"]}
            self.assertEqual(vm_x86["buf"], ("rdi", ""))
            self.assertEqual(vm_x86["n"], ("rsi", ""))
            # Dead param reclamation: on x86_64, `a`/`b` die on line 1; `caller_pt` needs <= 1 callee-saved reg (only `ab` or `x0`!)
            self.assertLessEqual(len(caller_rec["impls"]["x86_64"]["hl_meta"]["callee_saved"]), 2)
            for arch in ("x86_64", "arm64"):
                with tempfile.TemporaryDirectory() as d:
                    p = os.path.join(d, "pt.ode")
                    with open(p, "w", encoding="utf-8") as f:
                        f.write(src_pt)
                    res = ode_audit.pack_verified(p, None, os.path.join(d, "a.o"), os.path.join(d, "a.p"),
                                                  fn_name="caller_pt", target=arch)
                    self.assertEqual(res["verdict"], "shown", f"caller_pt on {arch}: {res}")

            # 2. Explicit `stack var` + `buf.u64` + merged consecutive `join` + `while` places
            src_all = """\
fn stack_u64_and_join(x: u64, y: u64) -> u64
    requires x <= 100
    requires y <= 50
    returns x + y + 10
    trace depends on x, y
{
    buf tmp[16] align 16
    stack var saved: u64 := x + 3
    tmp.u64(0) := y
    tmp.u64(8) := 7
    let t0: u64 := tmp.u64(0)
    let t1: u64 := tmp.u64(8)
    var acc: u64 := saved + t0
    var k: u64 := 0
    join maintains k == 0, acc == x + y + 3
    while k < t1
        maintains 0 <= k, k <= 7, acc == x + y + 3 + k, t1 == 7
        decreases 7 - k
    {
        acc += 1
        k += 1
    }
    return acc
}
"""
            parsed2 = ode_unified.parse_unified(src_all, src="all.ode")
            meta_a = parsed2["fns"][0]["impls"]["arm64"]["hl_meta"]
            self.assertEqual(meta_a["spills"], 0)
            self.assertTrue(any(nm == "saved" and note == "stack var" for nm, _, _, note in meta_a["var_map"]))
            for arch in ("x86_64", "arm64"):
                with tempfile.TemporaryDirectory() as d:
                    p = os.path.join(d, "all.ode")
                    with open(p, "w", encoding="utf-8") as f:
                        f.write(src_all)
                    res = ode_audit.pack_verified(p, None, os.path.join(d, "a.o"), os.path.join(d, "a.p"),
                                                  fn_name="stack_u64_and_join", target=arch)
                    self.assertEqual(res["verdict"], "shown", f"stack_u64_and_join on {arch}: {res}")

            # 2b. `buf.u32(off) := ...` gives crisp immediate compile-time error (no broken `str w12, [sp, 0]`)
            src_bad_u32 = """\
fn bad_u32(x: u64) -> u64
    requires x <= 10
    returns x
    trace depends on x
{
    buf tmp[16] align 16
    tmp.u32(0) := x
    return x
}
"""
            p_bad = ode_unified.parse_unified(src_bad_u32, src="bad.ode")
            for arch in ("x86_64", "arm64"):
                err_s = p_bad["fns"][0]["impls"][arch].get("hl_err", "")
                self.assertIn("32-bit scalar store", err_s)
                self.assertIn(".u32x4(off)", err_s)
        finally:
            for k, v in old_env.items():
                if v is None:
                    os.environ.pop(k, None)
                else:
                    os.environ[k] = v

        # 3. `--effort fast` early stop reports `--effort deep` / `TRY_HARDER`, and `--try-harder` rescues the same source!
        src_rescue = """\
def in_r(v) { if 10 <= v && v <= 20 then 1 else 0 }

fn rescue_demo(a: u64, b: u64, c: u64) -> u64
    requires a <= 255
    requires b <= 255
    requires c <= 255
    returns in_r(a) + in_r(b) + in_r(c)
    trace depends on a, b, c
{
    let r0: u64 := select((a -% 10) <= 10, 1, 0)
    let r1: u64 := select((b -% 10) <= 10, 1, 0)
    let r2: u64 := select((c -% 10) <= 10, 1, 0)
    return r0 + r1 + r2
}
"""
        import subprocess
        ode_cli = os.path.join(os.path.dirname(__file__), "ode_tool.py")
        with tempfile.TemporaryDirectory() as d:
            p = os.path.join(d, "rescue.ode")
            with open(p, "w", encoding="utf-8") as f:
                f.write(src_rescue)
            r_fast = subprocess.run(
                [sys.executable, ode_cli, "pack", p, "--fn", "rescue_demo", "--target", "x86_64",
                 "--effort", "fast", "--out", os.path.join(d, "f.o"), "--proof", os.path.join(d, "f.p")],
                capture_output=True, text=True,
            )
            self.assertNotEqual(r_fast.returncode, 0, f"expected fast effort to stop at spec limit 8: {r_fast.stdout}")
            self.assertIn("--effort deep", r_fast.stdout + r_fast.stderr)
            self.assertIn("TRY_HARDER", r_fast.stdout + r_fast.stderr)
            r_deep = subprocess.run(
                [sys.executable, ode_cli, "pack", p, "--fn", "rescue_demo", "--target", "x86_64",
                 "--try-harder", "--out", os.path.join(d, "d.o"), "--proof", os.path.join(d, "d.p")],
                capture_output=True, text=True,
            )
            self.assertEqual(r_deep.returncode, 0, f"--try-harder should prove same source: {r_deep.stdout}\n{r_deep.stderr}")
            self.assertIn("shown", r_deep.stdout)

    def test_29_x86_large_imm_arm64_no_v8_and_stack_var_maintains_diag(self):
        """Verify >2^31 x86-64 immediate synthesis, arm64 v8..v15 exclusion, and stack-var-in-maintains error."""
        import ode_unified
        # 1. > 2^31 immediate (`4294967296`) synthesizes cleanly on x86_64 & arm64 and verifies `shown`
        src_imm = """\
fn big_const(x: u64) -> u64
    requires x < 4294967296
    returns x + 4294967296
    trace depends on x
{
    return x + 4294967296
}
"""
        for arch in ("x86_64", "arm64"):
            with tempfile.TemporaryDirectory() as d:
                p = os.path.join(d, "imm.ode")
                with open(p, "w", encoding="utf-8") as f:
                    f.write(src_imm)
                res = ode_audit.pack_verified(p, None, os.path.join(d, "a.o"), os.path.join(d, "a.p"),
                                              fn_name="big_const", target=arch)
                self.assertEqual(res["verdict"], "shown", f"big_const on {arch}: {res}")

        # 2. `stack var` named in `maintains` gives crisp compile-time error
        src_sv_m = """\
fn bad_sv_m(n: u64) -> u64
    requires n <= 10
    returns n
    trace depends on n
{
    stack var i: u64 := 0
    while i < n
        maintains 0 <= i, i <= n
        decreases n - i
    {
        i += 1
    }
    return i
}
"""
        p_bad = ode_unified.parse_unified(src_sv_m, src="svm.ode")
        for arch in ("x86_64", "arm64"):
            self.assertIn("cannot be named directly in `maintains`", p_bad["fns"][0]["impls"][arch].get("hl_err", ""))

        # 3. 23 simultaneously live `u32x4` vars on arm64 refuse cleanly instead of allocating v8..v15
        vlines = [f"    let a{i}: u32x4 := load_u32x4(buf, {(i % 4) * 16})" for i in range(23)]
        vsum = " + ".join(f"a{i}" for i in range(23))
        src_v23 = (
            "fn vec23(out: 16 bytes, buf: 64 bytes)\n"
            "    ensures out = out\n"
            "    trace depends on nothing\n"
            "{\n"
            "    for arm64 {\n"
            + "\n".join("    " + l for l in vlines) + "\n"
            f"        store_u32x4(out, 0, {vsum})\n"
            "    }\n"
            "}\n"
        )
        with self.assertRaises(ode_unified.UnifiedErr) as cm:
            ode_unified.parse_unified(src_v23, src="v23.ode")
        self.assertIn("all 22 eligible registers are occupied", str(cm.exception))
        self.assertNotIn("= v8", str(cm.exception))


if __name__ == "__main__":
    unittest.main()
