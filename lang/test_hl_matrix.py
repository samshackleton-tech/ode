#!/usr/bin/env python3
"""Self-enforcing TDD feature x target x operand-shape x oracle matrix for High-Level Ode.

Design goals:
  1. Exhaustive table coverage: dynamically reads `ode_hl._INTRINSICS` and fails if any
     intrinsic is absent from the test matrix.
  2. Cross-arch table soundness: every lowered instruction must match a real row in
     `core/x86.tab` or `arm64/arm64.tab` and assemble cleanly; zero uncaught Python
     exceptions (`AttributeError`, `KeyError`, `TypeError`, raw `HLErr`).
  3. Differential oracle agreement: scalar verification tests assert `odeverify` AND
     independent `verify2.py` both say `shown`; `refute_conc.py` never silently skips
     supported task contract kinds (`in-out`, `bytes`, `number`).
  4. Metamorphic prover checks: equivalent rewrites models commonly write (multi-step
     unrolls + mid-function `join maintains`, tail calls needing multiple `t open`s,
     `&&` inside `(if ... then ...)` in `maintains`, lexical `{ ... }` blocks).
"""
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for d in (ROOT, HERE, os.path.join(ROOT, "proof-core"), os.path.join(ROOT, "kcheck"),
          os.path.join(ROOT, "core"), os.path.join(ROOT, "arm64"),
          os.path.join(ROOT, "advice"), os.path.join(ROOT, "paper", "EXPERIMENTS")):
    if d not in sys.path:
        sys.path.insert(0, d)

import ode_audit
import ode_hl
import ode_unified
import refute_conc
import run_suite
import verify2

STD_STORES = (os.path.join(ROOT, "std"),)


def _pack_and_dual_verify(src_text, fn_name, target, extra_files=None, c_abi=True, check_v2=True):
    """Compile, prove, audit with `odeverify`, and (for scalar fns) verify with `verify2.py`."""
    with tempfile.TemporaryDirectory(prefix="ode_mat_") as td:
        td_p = Path(td)
        if extra_files:
            for nm, content in extra_files.items():
                (td_p / nm).write_text(content, encoding="utf-8")
        src_p = td_p / "test.ode"
        src_p.write_text(src_text, encoding="utf-8")
        out_o = td_p / "out.o"
        out_p = td_p / "out.proof"
        res = ode_audit.pack_verified(
            str(src_p), None, str(out_o), str(out_p),
            fn_name=fn_name, target=target, c_abi=c_abi, stores=STD_STORES,
        )
        assert res["verdict"] == "shown", f"pack_verified failed ({target}): {res}"
        if check_v2:
            ok, detail, _ = run_suite.run_verify2_on_bundle(out_o, out_p, target)
            assert ok, f"verify2.py disagreed with odeverify ({target}): {detail}"
        return res


def _compile_only(src_text, fn_name, target):
    """Parse + lower + assemble (`odec`) without proving; verifies every emitted instruction
    exists in `x86.tab`/`arm64.tab` and encodes cleanly, with zero uncaught Python crashes."""
    with tempfile.TemporaryDirectory(prefix="ode_cmp_") as td:
        src_p = Path(td) / "test.ode"
        src_p.write_text(src_text, encoding="utf-8")
        parsed = ode_unified.parse_unified_file(str(src_p), c_abi_fn=fn_name, stores=STD_STORES)
        fn = next(f for f in parsed["fns"] if f["name"] == fn_name)
        im = fn["impls"][target]
        if im.get("hl_err"):
            raise ode_unified.UnifiedErr(im["hl_err"])
        # Run odec assembler over lowered lines to verify every emitted instruction is in x86.tab/arm64.tab
        import odec
        asm_src = ode_unified.render_target_asm(parsed, fn_name, target)
        asm_p = Path(td) / "out.s"
        asm_p.write_text(asm_src, encoding="utf-8")
        obj_p = Path(td) / "out.o"
        odec.assemble_file(str(asm_p), str(obj_p), target=target)
        return im


class TestHighLevelMatrix(unittest.TestCase):
    """Exhaustive TDD matrix covering every intrinsic, memory width, contract form, and oracle."""

    def test_01_every_intrinsic_registered_and_no_invalid_table_emission(self):
        """Every entry in `ode_hl._INTRINSICS` MUST be listed below; lowering on BOTH arches
        must either emit valid table instructions or raise a crisp `HLErr`/`UnifiedErr`
        (never emit a nonexistent instruction like `vpunpckhqdq xmm` or `vpshufd` on arm64)."""
        # Map every intrinsic in `ode_hl._INTRINSICS` to a minimal call expression + expected arch support.
        # Tuple: (vec_ty, expr_str, arches_that_must_assemble, extra_needs)
        matrix = {
            "load_u32x4": ("u32x4", "load_u32x4(src, 0)", ("x86_64", "arm64"), ""),
            "store_u32x4": ("stmt", "store_u32x4(out, 0, a)", ("x86_64", "arm64"), ""),
            "load_u32x16": ("u32x16", "load_u32x16(src, 0)", ("x86_64",), "needs avx512"),
            "store_u32x16": ("stmt16", "store_u32x16(out, 0, z0)", ("x86_64",), "needs avx512"),
            "broadcast_u32x16": ("u32x16", "broadcast_u32x16(k)", ("x86_64",), "needs avx512"),
            "zeros_u32x16": ("u32x16", "zeros_u32x16()", ("x86_64",), "needs avx512"),
            "const_u32x4": ("u32x4", "const_u32x4(0x6A09E667)", (), ""),
            "shl32": ("u32x4", "shl32(a, 3)", ("x86_64", "arm64"), ""),
            "shr32": ("u32x4", "shr32(a, 10)", ("x86_64", "arm64"), ""),
            "u64_to_vec": ("u32x4", "u64_to_vec(k)", ("x86_64", "arm64"), ""),
            "rev32_16": ("u32x4", "rev32_16(a)", ("arm64",), ""),
            "vprord": ("u32x4", "vprord(a, 12)", ("x86_64",), "needs avx512"),
            "shuf32": ("u32x4", "shuf32(a, 0x39)", ("x86_64",), ""),
            "shufps": ("u32x4", "shufps(a, b, 0x88)", ("x86_64",), ""),
            "shufi32x4": ("u32x16", "shufi32x4(z0, z0, 0x4E)", ("x86_64",), "needs avx512"),
            "blend32": ("u32x4", "blend32(a, b, 0x5)", ("x86_64",), ""),
            "unpacklo32": ("u32x4", "unpacklo32(a, b)", ("x86_64", "arm64"), ""),
            "unpackhi32": ("u32x4", "unpackhi32(a, b)", ("x86_64", "arm64"), ""),
            "unpacklo64": ("u32x4", "unpacklo64(a, b)", ("x86_64", "arm64"), ""),
            "unpackhi64": ("u32x4", "unpackhi64(a, b)", ("x86_64", "arm64"), ""),
            "uzp1_32": ("u32x4", "uzp1_32(a, b)", ("x86_64", "arm64"), ""),
            "uzp2_32": ("u32x4", "uzp2_32(a, b)", ("x86_64", "arm64"), ""),
            "ext4": ("u32x4", "ext4(a, b)", ("x86_64", "arm64"), ""),
            "ext8": ("u32x4", "ext8(a, b)", ("x86_64", "arm64"), ""),
            "ext12": ("u32x4", "ext12(a, b)", ("x86_64", "arm64"), ""),
            "add_u32x16_data": ("skip_data", "", (), ""),
        }
        missing = set(ode_hl._INTRINSICS) - set(matrix.keys())
        self.assertEqual(missing, set(), f"Untested intrinsics in ode_hl._INTRINSICS: {sorted(missing)}")

        for intr, (kind, expr, ok_arches, extra_needs) in sorted(matrix.items()):
            if kind == "skip_data":
                continue
            for arch in ("x86_64", "arm64"):
                if kind == "u32x4":
                    body = f"let a: u32x4 := src.u32x4(0)\n    let b: u32x4 := src.u32x4(16)\n    let r: u32x4 := {expr}\n    out.u32x4(0) := r"
                    sz = 64
                elif kind == "stmt":
                    body = f"let a: u32x4 := src.u32x4(0)\n    {expr}"
                    sz = 64
                elif kind == "u32x16":
                    body = f"let z0: u32x16 := src.u32x16(0)\n    let r: u32x16 := {expr}\n    out.u32x16(0) := r"
                    sz = 64
                elif kind == "stmt16":
                    body = f"let z0: u32x16 := src.u32x16(0)\n    {expr}"
                    sz = 64
                needs_line = f"    {extra_needs}\n" if (extra_needs and arch == "x86_64") else ""
                src = (
                    f"fn test_intr(out: {sz} bytes, src: {sz} bytes, k: u64)\n"
                    f"    requires no_overlap(out, src)\n"
                    f"    ensures out = out\n"
                    f"{needs_line}"
                    f"    trace depends on nothing\n"
                    f"{{\n    {body}\n}}\n"
                )
                if arch in ok_arches:
                    try:
                        with tempfile.TemporaryDirectory() as td:
                            p = Path(td) / "t.ode"
                            p.write_text(src, encoding="utf-8")
                            parsed = ode_unified.parse_unified(src, src=str(p), c_abi_fn="test_intr")
                            fn = parsed["fns"][0]
                            im = fn["impls"][arch]
                            self.assertFalse(im.get("hl_err"), f"{intr} on {arch} raised hl_err: {im.get('hl_err')}")
                            # Assemble to verify every emitted instruction is in x86.tab / arm64.tab!
                            r = subprocess.run(
                                [sys.executable, os.path.join(HERE, "ode_tool.py"), "advise", str(p), "--target", arch, "--asm"],
                                capture_output=True, text=True,
                            )
                            self.assertEqual(r.returncode, 0, f"{intr} on {arch} advise failed: {r.stdout}\n{r.stderr}")
                    except Exception as exc:
                        self.fail(f"intrinsic `{intr}` on {arch} failed: {type(exc).__name__}: {exc}")
                else:
                    # Must NEVER crash with AttributeError/TypeError/KeyError; must yield HLErr/UnifiedErr!
                    with tempfile.TemporaryDirectory() as td:
                        p = Path(td) / "t.ode"
                        p.write_text(src, encoding="utf-8")
                        try:
                            parsed = ode_unified.parse_unified(src, src=str(p), c_abi_fn="test_intr")
                            # If parsed didn't raise, check hl_err is set (not silently emitting bad asm!)
                            im = parsed["fns"][0]["impls"][arch]
                            self.assertTrue(im.get("hl_err"), f"unsupported `{intr}` on {arch} should report crisp hl_err, not succeed silently")
                        except (ode_unified.UnifiedErr, ode_hl.HLErr):
                            pass
                        except Exception as exc:
                            self.fail(f"intrinsic `{intr}` on {arch} crashed with {type(exc).__name__}: {exc}")

    def test_02_vector_shifts_and_1to1_ops_verify_both_arches(self):
        """1-to-1 vector ops (`v >> k`, `v << k`, `unpackhi64`, `ext4`/`ext8`/`ext12`,
        `uzp1_32`/`uzp2_32`) must verify `shown` on BOTH `x86_64` and `arm64`, and
        `shuf32` must verify on `x86_64` while raising a crisp error on `arm64`."""
        src = """\
def vec_test(ws) {
    let x = [ws[0], ws[1], ws[2], ws[3]]
    let y = [ws[4], ws[5], ws[6], ws[7]]
    let s1 = [x[0] >> 10, x[1] >> 10, x[2] >> 10, x[3] >> 10]
    let s2 = [x[0] >>> 29, x[1] >>> 29, x[2] >>> 29, x[3] >>> 29]
    let hi = [x[2], x[3], y[2], y[3]]
    let rot = [x[1], x[2], x[3], x[0]]
    let e2 = [x[0], x[2], y[0], y[2]]
    [s1[i] ^ s2[i] ^ hi[i] ^ rot[i] ^ e2[i] for i in 0..4]
}

fn vec_ops(out: 16 bytes, src: 32 bytes)
    requires no_overlap(out, src)
    ensures out = bytes_of(vec_test(words(src)))
    trace depends on nothing
{
    let x: u32x4 := src.u32x4(0)
    let y: u32x4 := src.u32x4(16)
    let s1: u32x4 := x >> 10
    let s2: u32x4 := (x << 3) | (x >> 29)
    let hi: u32x4 := unpackhi64(x, y)
    let rot: u32x4 := ext4(x, x)
    let e2: u32x4 := uzp1_32(x, y)
    out.u32x4(0) := s1 ^ s2 ^ hi ^ rot ^ e2
}
"""
        for arch in ("x86_64", "arm64"):
            _pack_and_dual_verify(src, "vec_ops", arch, check_v2=False)

        # `shuf32` is strictly x86-64 (`vpshufd`): verifies on x86_64, crisp error on arm64
        src_shuf = """\
def rot1(ws) { [ws[1], ws[2], ws[3], ws[0]] }
fn shuf_only_x86(out: 16 bytes, src: 16 bytes)
    requires no_overlap(out, src)
    ensures out = bytes_of(rot1(words(src)))
    trace depends on nothing
{
    let x: u32x4 := src.u32x4(0)
    out.u32x4(0) := shuf32(x, 0x39)
}
"""
        _pack_and_dual_verify(src_shuf, "shuf_only_x86", "x86_64", check_v2=False)
        parsed = ode_unified.parse_unified(src_shuf, src="shuf_only_x86.ode", c_abi_fn="shuf_only_x86")
        self.assertIn("x86-64 only", parsed["fns"][0]["impls"]["arm64"].get("hl_err", ""))

    def test_03_unaligned_arm64_and_x86_loads_and_stores(self):
        """Unaligned `u64(52)` and `u32x4(4)` offsets must never emit unencodable arm64
        immediate-offset `ldr x, [x2, 52]` or `ldr q, [sp, 4]`."""
        src = """\
def read_unaligned(buf) {
    buf[52] + 256 * buf[53] + 65536 * buf[54] + 16777216 * buf[55]
}

fn load_u64_unaligned(buf: n bytes, n: number) -> u64
    requires n >= 64, n <= 65535
    returns read_unaligned(buf)
    trace depends on n
{
    let w := buf.u64(52)
    return w & 0xFFFFFFFF
}
"""
        for arch in ("x86_64", "arm64"):
            _pack_and_dual_verify(src, "load_u64_unaligned", arch, check_v2=True)

        # Also test unaligned u32x4 load at offset 4 (4 bytes, not multiple of 16!) assembles cleanly on both arches
        src_v = """\
def copy_off4(ws) { [ws[1], ws[2], ws[3], ws[4]] }

fn load_v_off4(out: 16 bytes, src: 32 bytes)
    requires no_overlap(out, src)
    ensures out = bytes_of(copy_off4(words(src)))
    trace depends on nothing
{
    let v: u32x4 := src.u32x4(4)
    out.u32x4(0) := v
}
"""
        for arch in ("x86_64", "arm64"):
            with tempfile.TemporaryDirectory() as td:
                p = Path(td) / "t.ode"
                p.write_text(src_v, encoding="utf-8")
                r = subprocess.run(
                    [sys.executable, os.path.join(HERE, "ode_tool.py"), "advise", str(p), "--target", arch, "--asm"],
                    capture_output=True, text=True,
                )
                self.assertEqual(r.returncode, 0, f"load_v_off4 advise failed ({arch}): {r.stdout}\n{r.stderr}")

    def test_04_blocks_maintains_and_crisp_contract_diagnostics(self):
        """Lexical `{ ... }` blocks, `&&` inside `(if ... then ...)` in `maintains`,
        clean diagnostics on `inline fn -> ty`, `ensures ret == ...`, `!=` in `maintains`,
        callee explicit `stack K` overflow, and no `__inl_*` spam in `vars:`."""
        # 1. Lexical `{ ... }` scopes (reusing `let tmp` in sibling blocks) + `join maintains`
        src_ok = """\
def classify(c) {
    if 48 <= c && c <= 57 then c - 48 else 99
}

fn scope_and_if_maintains(c: u64) -> u64
    requires c <= 255
    returns classify(c)
    trace depends on nothing
{
    var r: u64 := 99
    {
        let tmp := c -% 48
        let mid := select(c <= 57, tmp, r)
        r := select(c >= 48, mid, r)
    }
    join maintains r == classify(c), r <= 99
    {
        let tmp := r
        return tmp
    }
}
"""
        for arch in ("x86_64", "arm64"):
            _pack_and_dual_verify(src_ok, "scope_and_if_maintains", arch, check_v2=True)

        # 1b. `&&` inside `(if ... then ...)` in `maintains` must NOT split naively on `&&`
        src_and_if = """\
fn parse_if_and(c: u64) -> u64
    requires c >= 48, c <= 57
    returns c - 48
    trace depends on c
{
    var r: u64 := c - 48
    join maintains r == (if 48 <= c && c <= 57 then c - 48 else 99)
    return r
}
"""
        for arch in ("x86_64", "arm64"):
            _pack_and_dual_verify(src_and_if, "parse_if_and", arch, check_v2=True)

        # 2. `inline fn foo(x: u32x4) -> bogus` must raise clean UnifiedErr (never uncaught HLErr traceback)
        src_inl = """\
inline fn bad_inl(x: u32x4) -> bogus {
    return x
}
fn f(x: u64) -> u64
    returns x
    trace depends on x
{
    return x
}
"""
        with self.assertRaises(ode_unified.UnifiedErr):
            ode_unified.parse_unified(src_inl, src="inl.ode")

        # 3. `ensures ret == ...` without `returns` gives crisp error (never Lean's `has conditions`)
        src_ens = """\
fn bad_ens(x: u64) -> u64
    ensures ret == x
    trace depends on x
{
    return x
}
"""
        with self.assertRaises(ode_unified.UnifiedErr) as cm:
            ode_unified.parse_unified(src_ens, src="ens.ode")
        self.assertIn("returns", str(cm.exception).lower())

        # 4. Top-level `!=` in `maintains` gives crisp HL compile error
        src_neq = """\
fn bad_neq(x: u64) -> u64
    requires x <= 10
    returns x
    trace depends on x
{
    if x == 5 { return 5 }
    join maintains x != 5, x <= 10
    return x
}
"""
        p_neq = ode_unified.parse_unified(src_neq, src="neq.ode")
        for arch in ("x86_64", "arm64"):
            self.assertIn("!=", p_neq["fns"][0]["impls"][arch].get("hl_err", ""))

        # 5. Callee explicit `stack 256` must be counted in caller's explicit `stack 200` check!
        src_stk = """\
fn leaf(x: u64) -> u64
    returns x
    trace depends on x
    stack 256
{
    return x
}

fn caller(x: u64) -> u64
    returns x
    trace depends on x
    stack 200
{
    let y := leaf(x)
    return y
}
"""
        p_stk = ode_unified.parse_unified(src_stk, src="stk.ode")
        for arch in ("x86_64", "arm64"):
            err = p_stk["fns"][1]["impls"][arch].get("hl_err", "")
            self.assertIn("exceeding explicit `stack 200`", err, f"missing callee stack check on {arch}: {err}")

    def test_05_refute_conc_supports_inout_blake3_compress1(self):
        """`refute_conc.py` must support `in-out 32 bytes` (`blake3_compress1`) and catch a
        6-round bug immediately with status == 'FALSE' instead of silently returning 'skipped'."""
        spec_txt = (Path(ROOT) / "paper/EXPERIMENTS/tasks/blake3_compress1_spec.ode").read_text(encoding="utf-8")
        ref_txt = (Path(ROOT) / "paper/EXPERIMENTS/tasks/blake3_compress1_reference.ode").read_text(encoding="utf-8")
        # Plant a 1-line bug: drop the 7th round (change `for r in 0..7` or delete last round call)
        lines = ref_txt.splitlines()
        buggy = ref_txt.replace("compress_round(", "compress_round(", 1)
        # Drop last `round_step` / change `0..7` -> `0..6` or corrupt final xor `v0 ^ v2` -> `v0`
        if "v0 ^ v2" in ref_txt:
            buggy = ref_txt.replace("v0 ^ v2", "v0", 1)
        elif "s0 ^ s2" in ref_txt:
            buggy = ref_txt.replace("s0 ^ s2", "s0", 1)
        else:
            # Replace first `^` in final store with `+`
            buggy = re.sub(r"h\.u32x4\(0\)\s*:=\s*([^\n]+)", "h.u32x4(0) := h.u32x4(0)", ref_txt, count=1)
        self.assertNotEqual(buggy, ref_txt)
        with tempfile.TemporaryDirectory() as td:
            td_p = Path(td)
            (td_p / "blake3_compress1_spec.ode").write_text(spec_txt, encoding="utf-8")
            (td_p / "buggy.ode").write_text(buggy, encoding="utf-8")
            r = subprocess.run(
                [sys.executable, os.path.join(HERE, "ode_tool.py"), "pack", str(td_p / "buggy.ode"),
                 "--c-abi", "--fn", "blake3_compress1", "--target", "x86_64",
                 "--out", str(td_p / "b.o"), "--proof", str(td_p / "b.p"),
                 "--store", os.path.join(ROOT, "std")],
                capture_output=True, text=True,
            )
            self.assertNotEqual(r.returncode, 0)
            out = r.stdout + r.stderr
            self.assertIn("concrete execution disagrees", out, f"refute_conc skipped blake3_compress1! got:\n{out[:500]}")

    def test_06_metamorphic_tail_call_multi_open_and_unroll_t_same_dual_verify(self):
        """Differential + metamorphic test covering BOTH Bug #1 (`verify2.py` tail-call multi-open)
        and Bug #2 (`prove.py` multi-step unroll `t same` + Gomory cut `(69 % 16) * 2 == 10`)."""
        spec_txt = (Path(ROOT) / "paper/EXPERIMENTS/tasks/ipv4_valid_spec.ode").read_text(encoding="utf-8")
        h_ipv4 = ode_unified.module_hash_bytes(spec_txt.encode("utf-8"))
        # 1. Tail-call multi-open (exact shape of muse-spark-open arm64 ipv4_valid!)
        src_tail = f"""\
use spec = "{h_ipv4}"  // ipv4_valid_spec.ode

fn fold_ok(s: u64) -> u64
    returns spec.fold2_ok(s)
    trace depends on s
    stack 0
{{
    let t1 := s % 65536 + s / 65536
    let t2 := t1 % 65536 + t1 / 65536
    return select(t2 == 65535, 1, 0)
}}

fn checksum4_tail(pkt: n bytes, n: number) -> u64
    requires n <= 65535, n >= 8
    returns spec.sum16_check(pkt, 0, 4, 0)
    trace depends on pkt, n
    stack 0
{{
    var acc: u64 := 0
    for k in 0..4 unroll {{
        acc += pkt[2 * k] * 256 + pkt[2 * k + 1]
    }}
    return fold_ok(acc)
}}
"""
        for arch in ("x86_64", "arm64"):
            _pack_and_dual_verify(src_tail, "checksum4_tail", arch,
                                  extra_files={"ipv4_valid_spec.ode": spec_txt}, check_v2=True)

        # 2. Metamorphic 4-step unroll with mid-function `join maintains` + Gomory `(69 % 16) * 2 == 10`
        src_unroll = ("""\
use spec = "__H_IPV4__"  // ipv4_valid_spec.ode

def sum4_spec(pkt) {
    if pkt[0] != 69 then 0
    else spec.sum16_check(pkt, 0, (pkt[0] % 16) * 2, 0)
}

fn sum4_unroll_join(pkt: n bytes, n: number) -> u64
    requires n <= 65535, n >= 20
    returns sum4_spec(pkt)
    trace depends on pkt, n
    stack 0
{
    if pkt[0] != 69 { return 0 }
    var acc: u64 := 69 * 256 + pkt[1]
    acc += pkt[2] * 256 + pkt[3]
    acc += pkt[4] * 256 + pkt[5]
    acc += pkt[6] * 256 + pkt[7]
    join maintains acc <= 4 * 65535,
        spec.sum16_check(pkt, 0, 10, 0) == spec.sum16_check(pkt, 4, 10, acc)
    for k in 4..10
        maintains acc <= k * 65535
        maintains spec.sum16_check(pkt, 0, 10, 0) == spec.sum16_check(pkt, k, 10, acc)
    {
        acc += pkt[2 * k] * 256 + pkt[2 * k + 1]
    }
    let f1 := (acc & 65535) + (acc >> 16)
    let f2 := (f1 & 65535) + (f1 >> 16)
    return select(f2 == 65535, 1, 0)
}
""").replace("__H_IPV4__", h_ipv4)
        for arch in ("x86_64", "arm64"):
            _pack_and_dual_verify(src_unroll, "sum4_unroll_join", arch,
                                  extra_files={"ipv4_valid_spec.ode": spec_txt}, check_v2=True)

    def test_07_error_hints_never_recommend_nonexistent_intrinsics(self):
        """Any `u32x4.*` or `u32x16.*` intrinsic mentioned in `ode_hl.py` error messages must exist."""
        hl_txt = (Path(HERE) / "ode_hl.py").read_text(encoding="utf-8")
        mentioned = set(re.findall(r"`(u32x(?:4|16)\.[a-z_]+)`", hl_txt))
        missing = mentioned - set(ode_hl._INTRINSICS)
        self.assertEqual(missing, set(), f"ode_hl.py error hints mention nonexistent intrinsics: {sorted(missing)}")

    def test_08_run_suite_fence_extractor_and_contract_mismatch_classification(self):
        """`extract_ode_source` must never leave ```ode inside extracted source even with
        earlier inline/prose code fences, and `classify_failure` must catch contract hash mismatch."""
        # Case A: prose mentions ```ode in text before the real fenced block
        reply1 = (
            "I noticed an issue in ```ode\nold\n``` earlier.\n"
            "Wait, here is a snippet with backticks `foo` and an unclosed fence:\n"
            "```ode\nfn demo(x: u64) -> u64\n    returns x\n    trace depends on x\n{\n    return x\n}\n```\n"
        )
        ex1 = run_suite.extract_ode_source(reply1, "demo")
        self.assertNotIn("```", ex1)
        self.assertTrue(ex1.startswith("fn demo"))

        # Case B: stray opening ``` in prose before real ```ode block
        reply2 = (
            "Explanation:\n```\nnot ode\n```ode\nfn demo(x: u64) -> u64\n{\n    return x\n}\n```\n"
        )
        ex2 = run_suite.extract_ode_source(reply2, "demo")
        self.assertNotIn("```", ex2)
        self.assertIn("fn demo", ex2)

        # Case C: unclosed trailing ```ode block
        reply3 = "Here is the fix:\n```ode\nfn demo(x: u64) -> u64\n{\n    return x\n}\n"
        ex3 = run_suite.extract_ode_source(reply3, "demo")
        self.assertNotIn("```", ex3)
        self.assertTrue(ex3.startswith("fn demo"))

        # Case D: contract hash mismatch classification
        cat = run_suite.classify_failure(
            "audit",
            "VERDICT: refused\nERROR: contract hash mismatch: expected aaa, binary carries bbb",
            1,
        )
        self.assertEqual(cat, "contract_id_mismatch")

    def test_09_anti_cleverness_lowering_manifest_and_ratchets(self):
        """Anti-cleverness guardrails enforcing that the coder—not the compiler—makes all
        clever decisions:
          1. Every atomic vector op / intrinsic emits <= 1 machine instruction unless explicitly
             listed in the locked EXPLICIT_MULTI_INSN_OPS manifest (never expand without approval!).
          2. Immediate-taking intrinsics (`shuf32`) are uniform across all immediates (no partial
             magic-constant tables like 8/256 on arm64).
          3. Statement-order monotonicity: lowered line numbers never move backwards in straight-line code.
          4. Prover-vs-compiler isolation: `--effort fast` and `--effort deep` emit identical `.text` bytes.
          5. ISA table row-count ratchet: `core/x86.tab` and `arm64/arm64.tab` never grow silently."""
        import odec

        # Locked manifest of multi-instruction vector intrinsics: RETIRED TO ZERO!
        # `rotr32`, `rotl32`, `pack_u64x2`, and `const_u32x4(a,b,c,d)` now live in ordinary
        # content-addressed `std/vec.ode`. Every vector op/intrinsic in the compiler MUST emit <= 1 insn!
        # BINDING RULE: never add an entry here without explicit approval!
        EXPLICIT_MULTI_INSN_OPS = {}

        vec_probes = [
            ("add", "x + y", ("x86_64", "arm64")),
            ("xor", "x ^ y", ("x86_64", "arm64")),
            ("and", "x & y", ("x86_64", "arm64")),
            ("or", "x | y", ("x86_64", "arm64")),
            ("shr", "x >> 10", ("x86_64", "arm64")),
            ("shl", "x << 3", ("x86_64", "arm64")),
            ("shl32", "shl32(x, 3)", ("x86_64", "arm64")),
            ("shr32", "shr32(x, 10)", ("x86_64", "arm64")),
            ("u64_to_vec", "u64_to_vec(w0)", ("x86_64", "arm64")),
            ("rev32_16", "rev32_16(x)", ("arm64",)),
            ("vprord", "vprord(x, 12)", ("x86_64",)),
            ("unpacklo32", "unpacklo32(x, y)", ("x86_64", "arm64")),
            ("unpackhi32", "unpackhi32(x, y)", ("x86_64", "arm64")),
            ("unpacklo64", "unpacklo64(x, y)", ("x86_64", "arm64")),
            ("unpackhi64", "unpackhi64(x, y)", ("x86_64", "arm64")),
            ("uzp1_32", "uzp1_32(x, y)", ("x86_64", "arm64")),
            ("uzp2_32", "uzp2_32(x, y)", ("x86_64", "arm64")),
            ("ext4", "ext4(x, y)", ("x86_64", "arm64")),
            ("ext8", "ext8(x, y)", ("x86_64", "arm64")),
            ("ext12", "ext12(x, y)", ("x86_64", "arm64")),
            ("shuf32", "shuf32(x, 0x39)", ("x86_64",)),
            ("shufps", "shufps(x, y, 0x88)", ("x86_64",)),
            ("blend32", "blend32(x, y, 0x5)", ("x86_64",)),
        ]
        for op_name, expr, arches in vec_probes:
            src = (
                "fn p(out: 64 bytes, inp: 64 bytes, w0: word, w1: word)\n"
                "    requires no_overlap(out, inp)\n"
                "    trace depends on nothing\n"
                "{\n"
                "    let x: u32x4 := inp.u32x4(0)\n"
                "    let y: u32x4 := inp.u32x4(16)\n"
                f"    let r: u32x4 := {expr}\n"
                "    out.u32x4(0) := r\n"
                "}\n"
            )
            for arch in arches:
                _, _, _, fns = odec.source(src, "<manifest>", target=arch)
                ins = [x for x in fns[0][2] if x not in ("ret", "vzeroupper") and not x.endswith(":")]
                # Shell is 2 loads + 1 store = 3 instructions
                body_ins = ins[2:-1]
                max_allowed = EXPLICIT_MULTI_INSN_OPS.get(op_name, {}).get(arch, 1)
                self.assertLessEqual(
                    len(body_ins), max_allowed,
                    f"Anti-cleverness ratchet FAILED: `{op_name}` on {arch} emitted {len(body_ins)} insns "
                    f"(allowed <= {max_allowed}): {body_ins}",
                )

        # 2. Immediate uniformity for `shuf32`: every 8-bit mask emits 1 insn on x86_64 and errors on arm64
        for imm in (0x00, 0x06, 0x39, 0x4E, 0x55, 0x93, 0xAA, 0xE4, 0xFF):
            src_s = (
                "fn s(out: 16 bytes, inp: 16 bytes)\n"
                "    requires no_overlap(out, inp)\n"
                "    trace depends on nothing\n"
                f"{{\n    let x: u32x4 := inp.u32x4(0)\n    out.u32x4(0) := shuf32(x, {imm})\n}}\n"
            )
            _, _, _, fx = odec.source(src_s, "<shuf>", target="x86_64")
            body_x = [x for x in fx[0][2] if x not in ("ret", "vzeroupper") and not x.endswith(":")][1:-1]
            self.assertEqual(len(body_x), 1, f"shuf32({imm}) on x86_64 should emit 1 insn, got {body_x}")
            parsed_a = ode_unified.parse_unified(src_s, src="<shuf>", c_abi_fn="s")
            self.assertTrue(
                parsed_a["fns"][0]["impls"]["arm64"].get("hl_err"),
                f"shuf32({imm}) on arm64 must be refused uniformly (no partial magic-mask tables!)",
            )

        # 3. Statement-order monotonicity in straight-line code
        src_mono = """\
fn mono(a: u64, b: u64, c: u64) -> u64
    requires a <= 1000, b <= 1000, c <= 1000
    returns a + b + c + a
    trace depends on a, b, c
{
    let x := a + b
    let y := x + c
    let z := y + a
    return z
}
"""
        for arch in ("x86_64", "arm64"):
            parsed_m = ode_unified.parse_unified(src_mono, src="<mono>", c_abi_fn="mono")
            ln_map = parsed_m["fns"][0]["impls"][arch].get("hl_line_map") or []
            # Ignore prologue/epilogue line 0 if any; real body lines must be non-decreasing
            body_lns = [ln for ln in ln_map if ln > 0]
            self.assertEqual(
                body_lns, sorted(body_lns),
                f"Statement-order monotonicity violated on {arch}: {body_lns}",
            )

        # 4. Prover-vs-compiler isolation: `--effort fast` and `--effort deep` produce identical ELF bytes
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "iso.ode"
            p.write_text(src_mono, encoding="utf-8")
            for arch in ("x86_64", "arm64"):
                o_fast, p_fast = Path(td) / f"f_{arch}.o", Path(td) / f"f_{arch}.p"
                o_deep, p_deep = Path(td) / f"d_{arch}.o", Path(td) / f"d_{arch}.p"
                for eff, oo, op in (("fast", o_fast, p_fast), ("deep", o_deep, p_deep)):
                    r = subprocess.run(
                        [sys.executable, os.path.join(HERE, "ode_tool.py"), "pack", str(p),
                         "--fn", "mono", "--target", arch, "--c-abi", "--effort", eff,
                         "--out", str(oo), "--proof", str(op)],
                        capture_output=True, text=True,
                    )
                    self.assertEqual(r.returncode, 0, f"pack {eff}/{arch} failed: {r.stdout}\n{r.stderr}")
                self.assertEqual(
                    o_fast.read_bytes(), o_deep.read_bytes(),
                    f"Prover effort changed emitted ELF bytes on {arch}!",
                )

        # 5. ISA table row-count ratchet (prevents gaming lowering counts by bloating ISA tables)
        x86_rows = [l for l in Path(ROOT, "core/x86.tab").read_text(encoding="utf-8").splitlines()
                    if "|" in l and not l.lstrip().startswith("#")]
        arm_rows = [l for l in Path(ROOT, "arm64/arm64.tab").read_text(encoding="utf-8").splitlines()
                    if "|" in l and not l.lstrip().startswith("#")]
        self.assertLessEqual(len(x86_rows), 109, f"core/x86.tab grew silently ({len(x86_rows)} > 109 rows)")
        self.assertLessEqual(len(arm_rows), 67, f"arm64/arm64.tab grew silently ({len(arm_rows)} > 67 rows)")

    def test_10_hl_v2_forensic_bug_regressions(self):
        """Targeted TDD regressions for every compiler/verifier/diagnostic bug found in hl-default-v2."""
        # Bug #1 (Core.lean on16(sp)): `stack var v: u32x4` and `buf.u32x4(off)` MUST verify on arm64 & x86_64!
        src_sp_vec = """\
def vsum(a, b) {
    [a[i] + b[i] for i in 0..4]
}

fn sp_vec_add(out: 16 bytes, a: 16 bytes, b: 16 bytes)
    requires no_overlap(out, a, b)
    ensures out = bytes_of(vsum(words(a), words(b)))
    stack 64
{
    buf tmp[32] align 16
    stack var sa: u32x4 := a.u32x4(0)
    tmp.u32x4(0) := b.u32x4(0)
    let va: u32x4 := sa
    let vb: u32x4 := tmp.u32x4(0)
    out.u32x4(0) := va +% vb
    return
}
"""
        for arch in ("x86_64", "arm64"):
            with tempfile.TemporaryDirectory() as td:
                p = Path(td) / "sp_vec.ode"
                p.write_text(src_sp_vec, encoding="utf-8")
                r = subprocess.run(
                    [sys.executable, os.path.join(HERE, "ode_tool.py"), "pack", str(p),
                     "--fn", "sp_vec_add", "--target", arch, "--c-abi",
                     "--out", str(Path(td) / "o.o"), "--proof", str(Path(td) / "o.p")],
                    capture_output=True, text=True,
                )
                self.assertEqual(r.returncode, 0, f"arm64/x86 stack u32x4 failed ({arch}):\n{r.stdout}\n{r.stderr}")
                self.assertIn("shown", r.stdout)

        # Bug #3 (ode_hl.py _eval_scalar): using a `u32x4` var in scalar context must raise HLErr,
        # NEVER emit broken `orr x0.16b, v17.16b, v17.16b`!
        src_vec_in_scalar = """\
fn bad_ret_vec(a: 16 bytes)
    returns 0
    stack 0
{
    let v: u32x4 := a.u32x4(0)
    return v
}
"""
        for arch in ("x86_64", "arm64"):
            parsed = ode_unified.parse_unified(src_vec_in_scalar, src="<bad_vec>", c_abi_fn="bad_ret_vec")
            msg = (parsed["fns"][0]["impls"][arch].get("hl_err") or "").lower()
            self.assertIn("u32x4", msg, f"Expected u32x4 error on {arch}, got: {msg!r}")
            self.assertNotIn("orr x0.16b", msg)

        # Bug #4 (ode_hl.py _subst_inline_stmts): `join maintains` inside `inline fn` MUST substitute params!
        src_inl_join = """\
def clamp(c) {
    if c < 10 then c else 10
}

inline fn do_clamp(c: u64, var d: u64) {
    d := select(c < 10, c, 10)
    join maintains d == clamp(c)
}

fn use_clamp(x: number)
    requires x < 100
    returns clamp(x)
    trace depends on x
    stack 0
{
    var res: u64 := 0
    do_clamp(x, res)
    return res
}
"""
        for arch in ("x86_64", "arm64"):
            with tempfile.TemporaryDirectory() as td:
                p = Path(td) / "inl_join.ode"
                p.write_text(src_inl_join, encoding="utf-8")
                r = subprocess.run(
                    [sys.executable, os.path.join(HERE, "ode_tool.py"), "pack", str(p),
                     "--fn", "use_clamp", "--target", arch, "--c-abi",
                     "--out", str(Path(td) / "o.o"), "--proof", str(Path(td) / "o.p")],
                    capture_output=True, text=True,
                )
                self.assertEqual(r.returncode, 0, f"inline fn join failed ({arch}):\n{r.stdout}\n{r.stderr}")
                self.assertIn("shown", r.stdout)

        # Bug #5a (ode_tool.py vars: bloat): unrolled `$N` temporaries must NOT flood `vars:` past the refusal line!
        src_unroll_fail = """\
fn unroll_vars(x: number)
    requires x < 10
    returns x + 999
    trace depends on x
    stack 0
{
    var acc: u64 := x
    for i in 0..20 unroll {
        let step_tmp: u64 := acc + 1
        acc := step_tmp
    }
    return acc
}
"""
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "unroll_fail.ode"
            p.write_text(src_unroll_fail, encoding="utf-8")
            r = subprocess.run(
                [sys.executable, os.path.join(HERE, "ode_tool.py"), "pack", str(p),
                 "--fn", "unroll_vars", "--target", "arm64", "--c-abi",
                 "--out", str(Path(td) / "o.o"), "--proof", str(Path(td) / "o.p")],
                capture_output=True, text=True,
            )
            self.assertNotEqual(r.returncode, 0)
            self.assertNotIn("step_tmp$", r.stdout, f"Unrolled `$N` temporaries leaked into vars:!\n{r.stdout}")
            for ln in r.stdout.splitlines():
                if ln.lstrip().startswith("vars:"):
                    self.assertLess(len(ln), 320, f"vars: line too bloated ({len(ln)} chars): {ln}")

        # Bug #5b (ode_hl.py _refuse_spill): internal `__inl_N_` prefixes must NOT leak in reg-exhaustion errors!
        src_inl_spill = """\
inline fn eat_regs(x: u64, var out_acc: u64) {
    let t0 := x + 1
    let t1 := t0 + 2
    let t2 := t1 + 3
    let t3 := t2 + 4
    let t4 := t3 + 5
    let t5 := t4 + 6
    let t6 := t5 + 7
    let t7 := t6 + 8
    let t8 := t7 + 9
    let t9 := t8 + 10
    let t10 := t9 + 11
    let t11 := t10 + 12
    let t12 := t11 + 13
    let t13 := t12 + 14
    out_acc := t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12 + t13
}

fn spill_inl(x: number)
    requires x < 100
    returns x
    trace depends on x
    stack 0
{
    var r: u64 := 0
    eat_regs(x, r)
    return r
}
"""
        parsed_sp = ode_unified.parse_unified(src_inl_spill, src="<inl_spill>", c_abi_fn="spill_inl")
        err_sp = parsed_sp["fns"][0]["impls"]["x86_64"].get("hl_err") or ""
        self.assertIn("has no free register", err_sp)
        self.assertNotIn("__inl_", err_sp, f"Internal __inl_ leaked: {err_sp}")

        # Bug #6 (ode_unified.py): boolean `ensures` (causing Lean `has 'conditions'`) caught at parse time!
        src_cond_ens = """\
fn bad_cond_ens(x: number)
    requires x < 100
    ensures x == 0 || x >= 1
    returns x
    trace depends on x
    stack 0
{
    return x
}
"""
        with self.assertRaises(ode_unified.UnifiedErr) as cm:
            ode_unified.parse_unified(src_cond_ens, src="<cond_ens>", c_abi_fn="bad_cond_ens")
        self.assertIn("ensures", str(cm.exception).lower())
        self.assertNotIn("statement:", str(cm.exception))

        # Bug #7 (ode_hl.py): `let isAZ := c >= 65 && c <= 90` gives crisp select() hint, NOT `unexpected token '>='`!
        src_bool_let = """\
fn bad_bool_let(c: number)
    requires c < 256
    returns 0
    trace depends on c
    stack 0
{
    let isAZ := c >= 65 && c <= 90
    return isAZ
}
"""
        parsed_bl = ode_unified.parse_unified(src_bool_let, src="<bool_let>", c_abi_fn="bad_bool_let")
        msg = parsed_bl["fns"][0]["impls"]["x86_64"].get("hl_err") or ""
        self.assertIn("select(", msg, f"Missing select() hint: {msg!r}")
        self.assertNotIn("at start of statement", msg)

    def test_11_hl_v3_forensic_bug_regressions(self):
        """TDD regressions for all 4 defects surfaced by hl-default-v3 forensics."""
        import ode_tool, time

        # Bug A (ProveMain.lean): 64x-unrolled calls blowing up s.facts must stop deterministically
        # via ODE_PROVE_MAX_FACTS (never hang for minutes!) with an actionable hint.
        src_unroll_blowup = """\
def step_v(c) { if c < 128 then c else c - 128 }

fn helper(c: u8)
    returns step_v(c)
    trace depends on nothing
    stack 0
{
    return select(c < 128, c, c - 128)
}

fn blowup(out: 64 bytes, src: n bytes, n: number)
    requires no_overlap(out, src)
    requires n >= 256
    requires n <= 256
    ensures out = [step_v(src[4 * i]) for i in 0..64]
    returns 0
    trace depends on n
    stack 64
{
    var acc: u64 := 0
    for i in 0..64 unroll {
        let a := helper(src[4 * i])
        let b := helper(src[4 * i + 1])
        let c := helper(src[4 * i + 2])
        let d := helper(src[4 * i + 3])
        acc := acc | (a >> 4) | (b >> 4) | (c >> 4) | (d >> 4)
        out[i] := a
    }
    return 0
}
"""
        with tempfile.TemporaryDirectory() as td:
            p = os.path.join(td, "blowup.ode")
            with open(p, "w", encoding="utf-8") as f:
                f.write(src_unroll_blowup)
            t0 = time.monotonic()
            r = subprocess.run(
                [sys.executable, os.path.join(ROOT, "lang", "ode_tool.py"),
                 "pack", p, "--fn", "blowup", "--target", "x86_64",
                 "--effort", "fast", "--out", os.path.join(td, "b.o"),
                 "--proof", os.path.join(td, "b.proof")],
                capture_output=True, text=True,
            )
            dt = time.monotonic() - t0
            out = r.stdout + "\n" + r.stderr
            self.assertNotEqual(r.returncode, 0)
            self.assertLess(dt, 15.0, f"Unrolled blowup took {dt:.1f}s instead of fast deterministic refusal:\n{out}")
            self.assertIn("linear facts", out, f"Expected deterministic maxFacts diagnostic, got:\n{out}")

        # Bug B (ode_audit.py): calling an imported spec `def` via `use alias = ...` must NOT leak `m1__`
        # and must explain that it is a specification `def`, not a callable machine `fn`.
        with tempfile.TemporaryDirectory() as td:
            spec_p = os.path.join(td, "helper_spec.ode")
            with open(spec_p, "w", encoding="utf-8") as f:
                f.write("def u16_le(b, i) { b[i] + 256 * b[i + 1] }\n")
            h_sp = ode_unified.module_hash_file(spec_p)
            main_p = os.path.join(td, "main.ode")
            with open(main_p, "w", encoding="utf-8") as f:
                f.write(f"""\
use sp = "{h_sp}"  // helper_spec.ode

fn f(buf: n bytes, n: number)
    requires n >= 2
    returns sp.u16_le(buf, 0)
    trace depends on n
    stack 0
{{
    return sp.u16_le(buf, 0)
}}
""")
            r = subprocess.run(
                [sys.executable, os.path.join(ROOT, "lang", "ode_tool.py"),
                 "pack", main_p, "--fn", "f", "--target", "x86_64",
                 "--out", os.path.join(td, "f.o"), "--proof", os.path.join(td, "f.proof")],
                capture_output=True, text=True,
            )
            out = r.stdout + "\n" + r.stderr
            self.assertNotEqual(r.returncode, 0)
            self.assertIn("sp.u16_le", out, f"Expected pretty name `sp.u16_le` in diagnostic:\n{out}")
            self.assertIn("specification `def`", out, f"Expected spec `def` explanation:\n{out}")
            self.assertNotIn("m1__", out, f"Internal mangled prefix `m1__` leaked:\n{out}")

        # Bug C (ode_hl.py): `inline fn` accepts `buf: n bytes` and `mptr: 64 bytes` uniformly with `fn`.
        src_inl_bytes = """\
inline fn load_first(buf: n bytes, var out_v: u64) {
    out_v := buf[0]
}

fn read_byte(buf: n bytes, n: number)
    requires n >= 1
    returns buf[0]
    trace depends on n
    stack 0
{
    var v: u64 := 0
    load_first(buf, v)
    return v
}
"""
        for arch in ("x86_64", "arm64"):
            with tempfile.TemporaryDirectory() as td:
                p = os.path.join(td, "inl_bytes.ode")
                with open(p, "w", encoding="utf-8") as f:
                    f.write(src_inl_bytes)
                r = subprocess.run(
                    [sys.executable, os.path.join(ROOT, "lang", "ode_tool.py"),
                     "pack", p, "--fn", "read_byte", "--target", arch,
                     "--out", os.path.join(td, "r.o"), "--proof", os.path.join(td, "r.proof")],
                    capture_output=True, text=True,
                )
                self.assertEqual(r.returncode, 0, f"inline fn `buf: n bytes` failed on {arch}:\n{r.stdout}\n{r.stderr}")

        # Bug D (ode_tool.py): `need compare` hint must NOT tell models to use `select(...)` for a spec `if`.
        hint = ode_tool._diagnostic_hint("need compare", "arm64", info={"hl_meta": True})
        self.assertIn("if ...", hint)
        self.assertIn("does not split", hint)

    def test_12_hl_v4_forensic_bug_regressions(self):
        """TDD regressions for defects surfaced by hl-default-v4 forensics."""
        import ode_tool

        # Fix #1 (Core.lean `scall` + verify2.py): a `def` returning a `const ERR = 4294967296`
        # evaluated inside `if helper(x) >= ERR then ERR else helper(x)` must verify `shown` on BOTH
        # arches AND dual-verify in independent `verify2.py` (root cause of ebpf 0/8 in v2-v4!).
        src_const_def = """\
const ERR = 4294967296

def alu_or_err(op, x) {
    if op == 1 then x % 4294967296
    else ERR
}

def dispatch(op, x) {
    if alu_or_err(op, x) >= ERR then ERR
    else alu_or_err(op, x)
}

fn run_disp(op: number, x: number)
    requires op < 256
    requires x < 4294967296
    returns dispatch(op, x)
    trace depends on op, x
    stack 0
{
    if op == 1 {
        return x
    }
    return 4294967296
}
"""
        for arch in ("x86_64", "arm64"):
            _pack_and_dual_verify(src_const_def, "run_disp", arch)

        # Fix #3 (ode_hl.py): address index `64 * b + 4 * 6` folds `4 * 6` cleanly without holding extra scratch.
        src_idx_fold = """\
fn read_off(buf: 256 bytes, b: number)
    requires b < 4
    returns buf[64 * b + 24]
    trace depends on b
    stack 0
{
    return buf[64 * b + 4 * 6]
}
"""
        for arch in ("x86_64", "arm64"):
            parsed = ode_unified.parse_unified(src_idx_fold, src="<idx_fold>", c_abi_fn="read_off")
            imp = parsed["fns"][0]["impls"][arch]
            self.assertFalse(imp.get("hl_err"), f"index const-fold failed on {arch}: {imp.get('hl_err')}")

        # Fix #4 (ode_tool.py): crisp hints for write-only buffers, fixed-size bounds, and stack slots.
        h1 = ode_tool._diagnostic_hint("refused: a read of a run given only to write", "x86_64", info={"hl_meta": True})
        self.assertIn("write-only", h1)
        h2 = ode_tool._diagnostic_hint("refused: a read of a run of a fixed count that is not four or eight bytes within it", "arm64", info={"hl_meta": True})
        self.assertIn("buf.u32(off)", h2)
        h3 = ode_tool._diagnostic_hint("refused: a read of the frame where nothing was written", "arm64", info={"hl_meta": True})
        self.assertIn("stack slots", h3)

    def test_13_hl_v5_forensic_bug_regressions(self):
        """TDD regressions for defects surfaced by hl-default-v5 forensics."""
        import ode_tool

        # Fix #1 (Core.lean `atomId`, `inputWordId`, `symHalves` canonical remainder) &
        # Fix #2 (ode_hl.py constant `select(...)` folding inside `for ... unroll`):
        # Scalar `m.u64(off)` split with `& 0xffffffff`/`>> 32` + `select(j % 2 == 0, ...)`
        # + masked `t & 0xffffffff` must verify `shown` against `bytes_of(... words(m), lo(t), hi(t))`
        # on BOTH x86_64 and arm64!
        src_u64_words = """\
use vec = "7zpczpzr6tshzr6ew4fnhluakp3vs4q3xu4pndhflmztv6rdpqra"  // std/vec.ode

def mix_u64(m, t) {
    [m[0] ^ lo(t), m[1] ^ hi(t), m[2] + m[0], m[3] + m[1]]
}

fn run_mix(out: 16 bytes, m: 16 bytes, t: counter)
    requires no_overlap(out, m)
    ensures out = bytes_of(mix_u64(words(m), t))
    stack 64
{
    let q0: u64 := m.u64(0)
    let q1: u64 := m.u64(8)
    let t_lo: u64 := t & 4294967295
    let t_hi: u64 := t >> 32
    var acc_lo: u64 := 0
    var acc_hi: u64 := 0
    for j in 0..2 unroll {
        let pick: u64 := select(j % 2 == 0, q0 & 4294967295, q0 >> 32)
        if j == 0 {
            acc_lo := pick
        } else {
            acc_hi := pick
        }
    }
    let m_lo: u64 := acc_lo | (acc_hi << 32)
    let v_m: u32x4 := vec.pack_u64x2(m_lo, q1)
    let v_t: u32x4 := vec.pack_u64x2(t_lo | (t_hi << 32), m_lo)
    let lo_xor: u32x4 := v_m ^ v_t
    let hi_add: u32x4 := v_m +% v_t
    out.u32x4(0) := unpacklo64(lo_xor, unpackhi64(hi_add, hi_add))
}
"""
        for arch in ("x86_64", "arm64"):
            _pack_and_dual_verify(src_u64_words, "run_mix", arch, check_v2=False)

        # Fix #3 (ode_hl.py): value-returning `inline fn ... -> u64` now parses cleanly, and bare `select(...)` stmt gives crisp error.
        src_ok_inl = """\
inline fn id_ret(x: u64) -> u64 {
    return x
}
fn dummy(x: number)
    returns x
    stack 0
{
    return id_ret(x)
}
"""
        p_ok = ode_unified.parse_unified(src_ok_inl, src="<ok_inl>", c_abi_fn="dummy")
        self.assertIn("dummy", p_ok["fns_by_name"])

        src_bare_sel = """\
inline fn bad_sel(c: u64) {
    select(c == 0, 1, 2)
}
fn dummy2(x: number)
    returns x
    stack 0
{
    bad_sel(x)
    return x
}
"""
        with self.assertRaises(ode_unified.UnifiedErr) as cm2:
            ode_unified.parse_unified(src_bare_sel, src="<bad_sel>", c_abi_fn="dummy2")
        self.assertIn("expression, not a statement", str(cm2.exception))

        # Fix #4 (ode_tool.py): 4 new refusal hints from hl-default-v5.
        self.assertIn("inside", ode_tool._diagnostic_hint(
            "refused: at the place the frame does not hold what it held on first coming there",
            "x86_64", info={"hl_meta": True}))
        self.assertIn("unroll", ode_tool._diagnostic_hint(
            "refused: sixteen bytes at a place of a run that is no number",
            "x86_64", info={"hl_meta": True}))
        self.assertIn("constant bitmask", ode_tool._diagnostic_hint(
            "refused: an and with what is no number of the table: not here yet",
            "x86_64", info={"hl_meta": True}))
        self.assertIn("bytes_of", ode_tool._diagnostic_hint(
            "refused: the specification's words are not followed on the terms the function made",
            "arm64", info={"hl_meta": True}))

    def test_14_hl_v6_forensic_bug_regressions(self):
        """TDD regressions for defects surfaced by hl-default-v6 forensics (A2-A8, B1, #3)."""
        import importlib.util
        import ode_tool

        # A2: Core.lean & verify2.py `disjointOr` with `u = 0` (`y == 0` on a select branch).
        src_disjoint_zero = """\
def pack_byte(a, b, d) {
    (a % 4) * 64 + (if d == 0 then 0 else b)
}

fn f_disjoint(a: number, b: number, d: number)
    requires a < 64
    requires b < 64
    requires d < 2
    returns pack_byte(a, b, d)
    stack 0
{
    let lo: u64 := select(d == 0, 0, b)
    let hi: u64 := (a & 3) << 6
    let res: u64 := hi | lo
    return res
}
"""
        for arch in ("x86_64", "arm64"):
            _pack_and_dual_verify(src_disjoint_zero, "f_disjoint", arch, check_v2=True)

        # A3: `add64` unsigned fast-path & x86_64 `_emit_imm` `or` for constants >= 2^63 (`vec.const_u32x4(0xFFFFFFFF, ...)`).
        src_imm64_vec = """\
use vec = "7zpczpzr6tshzr6ew4fnhluakp3vs4q3xu4pndhflmztv6rdpqra"  // std/vec.ode

def mask_hi(m) {
    [m[0] ^ word(4294967295), m[1] ^ word(4294967295), m[2] ^ word(1), m[3] ^ word(2)]
}

fn f_mask(out: 16 bytes, m: 16 bytes)
    requires no_overlap(out, m)
    ensures out = bytes_of(mask_hi(words(m)))
    stack 64
{
    let v: u32x4 := m.u32x4(0)
    let k: u32x4 := vec.const_u32x4(4294967295, 4294967295, 1, 2)
    out.u32x4(0) := v ^ k
}
"""
        for arch in ("x86_64", "arm64"):
            _pack_and_dual_verify(src_imm64_vec, "f_mask", arch, check_v2=False)

        # A4a: Dead `stack let` slots across expanded iterations reuse slots cleanly (16 iterations fit `stack 32`!).
        src_stack_reuse = """\
def add16(x) {
    x + 16
}

fn f_stack_reuse(x: number)
    requires x < 1000
    returns add16(x)
    stack 32
{
    var acc: u64 := x
    for t in 0..16 unroll {
        stack let tmp1: u64 := acc + 1
        acc := tmp1
    }
    return acc
}
"""
        for arch in ("x86_64", "arm64"):
            _pack_and_dual_verify(src_stack_reuse, "f_stack_reuse", arch, check_v2=True)

        # A4b: `stack var` written BEFORE a `while` loop never shares its slot with a `stack let`
        # written INSIDE the `while` loop (preserves `Core.lean`'s `first.frame` loop invariant).
        src_stack_loop_guard = """\
def add_n(x, n) {
    x + n
}

fn f_stack_loop(x: number, n: number)
    requires x < 1000
    requires n < 1000
    returns add_n(x, n)
    trace depends on n
    stack 64
{
    stack let pre: u64 := x + 1
    var acc: u64 := pre - 1
    var i: u64 := 0
    while i < n
        maintains i <= n
        maintains acc == x + i
        decreases n - i
    {
        stack let step: u64 := acc + 1
        acc := step
        i += 1
    }
    return acc
}
"""
        for arch in ("x86_64", "arm64"):
            _pack_and_dual_verify(src_stack_loop_guard, "f_stack_loop", arch, check_v2=True)

        # A4c: Explicit entry `stack` overflow warns about contract ID rather than blindly raising it.
        src_stack_over = """\
fn f_over(x: number)
    requires x < 100
    returns x + 3
    stack 8
{
    stack let a: u64 := x + 1
    stack let b: u64 := x + 2
    return a + b - x
}
"""
        p_over = ode_unified.parse_unified(src_stack_over, src="<stk_over>", c_abi_fn="f_over")
        with self.assertRaises(ode_unified.UnifiedErr) as cm_stk:
            ode_unified._select_impl(p_over["fns"][0], "x86_64", "<stk_over>")
        self.assertIn("contract ID", str(cm_stk.exception))

        # A5: `select(s_a == s_b, 1, 0)` with two `stack var`s inside a compound expression on x86_64 + arm64,
        # plus stack `buf` indexed by a runtime-computed offset with in-place scratch reuse.
        src_select_stack_and_buf = """\
def score_eq(a, b, base) {
    base + (if a == b then 1 else 0)
}

fn f_sel_stk(a: number, b: number, base: number)
    requires a < 1000
    requires b < 1000
    requires base < 1000
    returns score_eq(a, b, base)
    stack 64
{
    stack var sa: u64 := a
    stack var sb: u64 := b
    let res: u64 := base + select(sa == sb, 1, 0)
    return res
}
"""
        for arch in ("x86_64", "arm64"):
            _pack_and_dual_verify(src_select_stack_and_buf, "f_sel_stk", arch, check_v2=True)

        # A5b: Local stack `buf` indexed by a runtime offset inside a compound expression reuses `reuse_dst`
        # without exhausting x86_64's 3-register scratch pool (compiled cleanly; stack `buf` constant offset verifies `shown`).
        src_buf_rt_compile = """\
fn f_buf_rt(x: number, y: number)
    requires x < 1000
    requires y < 1000
    returns x + y
    trace depends on x
    stack 64
{
    buf w[16] align 8
    w.u64(0) := x
    w.u64(8) := x
    let v: u64 := y + w.u64((x & 1) * 8)
    return v
}
"""
        p_buf = ode_unified.parse_unified(src_buf_rt_compile, src="<buf_rt>", c_abi_fn="f_buf_rt")
        for arch in ("x86_64", "arm64"):
            impl_b = ode_unified._select_impl(p_buf["fns"][0], arch, "<buf_rt>")
            self.assertIsNotNone(impl_b)
            self.assertFalse(impl_b.get("hl_err"))

        # A6: Calling `u32x4`-only intrinsics (`shuf32`/`blend32`) on `u32x16` fails cleanly in HL (never asm.py).
        for bad_call in ("let y: u32x16 := shuf32(z, 57)", "let y := shuf32(z, 57)", "let y: u32x16 := blend32(z, z, 1)"):
            src_zmm_bad = f"""\
fn f_zmm(out: 64 bytes, src: 64 bytes)
    requires no_overlap(out, src)
    ensures out = src
    stack 64
{{
    let z: u32x16 := src.u32x16(0)
    {bad_call}
    out.u32x16(0) := z
}}
"""
            p_z = ode_unified.parse_unified(src_zmm_bad, src="<zmm_bad>", c_abi_fn="f_zmm")
            with self.assertRaises(ode_unified.UnifiedErr) as cm_z:
                ode_unified._select_impl(p_z["fns"][0], "x86_64", "<zmm_bad>")
            msg_z = str(cm_z.exception)
            self.assertTrue("128-bit `u32x4`" in msg_z or "vector width mismatch" in msg_z, msg_z)

        # A7: `proof-core/statement.py` raises clean `SystemExit` (never bare `StopIteration`) on bad `ensures` target.
        sys.path.insert(0, os.path.join(ROOT, "proof-core"))
        sys.path.insert(0, os.path.join(ROOT, "kcheck"))
        import ode as _ode
        import statement as _stmt
        sp_bad = _ode.Spec("""\
contract f_bad(src: 16 bytes) {
    ensures missing = src
    stack 0
}
""")
        with self.assertRaises(SystemExit) as cm_st:
            _stmt.contract_lines(sp_bad.contracts["f_bad"], "f_bad")
        self.assertIn("not a parameter", str(cm_st.exception))

        # A8: `run_suite.py::extract_ode_source` handles prose glued directly onto an inline opening fence.
        rs_path = os.path.join(ROOT, "paper", "EXPERIMENTS", "run_suite.py")
        spec_rs = importlib.util.spec_from_file_location("_run_suite_test", rs_path)
        rs_mod = importlib.util.module_from_spec(spec_rs)
        spec_rs.loader.exec_module(rs_mod)
        glued = "Switching W to local buffer storage.```ode\nfn demo(x: number)\n    returns x\n{\n    return x\n}\n```\n"
        extracted = rs_mod.extract_ode_source(glued, "demo")
        self.assertTrue(extracted.startswith("fn demo("), extracted)
        self.assertNotIn("Switching W", extracted)

        # B1 & #3: diagnostic hints for vector `|`, `writes` prefix refusal, runtime `&`, and non-const `*`.
        self.assertIn("blend32", ode_tool._diagnostic_hint(
            "refused: an or of two vector registers that is no turn of each word", "x86_64", info={"hl_meta": True}))
        self.assertIn("select(b == 0, 0, a)", ode_tool._diagnostic_hint(
            "refused: an and with what is no number of the table: not here yet", "x86_64", info={"hl_meta": True}))
        self.assertIn("writes out[.. N]", ode_tool._diagnostic_hint(
            "refused: what a place says is written is said by the use of a definition", "x86_64", info={"hl_meta": True}))
        self.assertIn("writes out[.. N]", ode_tool._diagnostic_hint(
            "refused: a place says what is written by what is no list made thing by thing from 0 on", "arm64", info={"hl_meta": True}))
        src_bad_mul = """\
fn f_mul(a: number, b: number)
    requires a < 2
    requires b < 2
    returns a * b
    stack 0
{
    return a * b
}
"""
        p_mul = ode_unified.parse_unified(src_bad_mul, src="<bad_mul>", c_abi_fn="f_mul")
        with self.assertRaises(ode_unified.UnifiedErr) as cm_mul:
            ode_unified._select_impl(p_mul["fns"][0], "x86_64", "<bad_mul>")
        self.assertIn("select(b == 0, 0, a)", str(cm_mul.exception))

    def test_15_hl_v7_forensic_bug_regressions(self):
        """TDD regressions for the 3 bugs surfaced by hl-default-v7 ebpf/der_valid forensics."""
        # Bug #1a (ode_hl.py): `IfStmt` reg_owner merge across exiting `else` branch must not
        # resurrect a dead variable's register owner into a false `fact reg == buf[...]` at `join maintains`.
        src_join_reg_reuse = """\
def hdr_len(buf, p, end) {
    if p + 2 > end then 0
    else if buf[p + 1] < 128 then 2
    else if buf[p + 1] == 129 then (if p + 3 <= end && buf[p + 2] >= 128 then 3 else 0)
    else 0
}

def val_len(buf, p, end) {
    if p + 2 > end then 0
    else if buf[p + 1] < 128 then buf[p + 1]
    else if buf[p + 1] == 129 then (if p + 3 <= end && buf[p + 2] >= 128 then buf[p + 2] else 0)
    else 0
}

def parse_sum(buf, p, end) {
    if hdr_len(buf, p, end) == 0 then 0 else hdr_len(buf, p, end) + val_len(buf, p, end)
}

fn f_join_reuse(buf: n bytes, n: number, p: number, end: number)
    requires p <= end, end <= n, n <= 65536
    returns parse_sum(buf, p, end)
    trace depends on buf, n, p, end
    stack 64
{
    if p + 2 > end { return 0 }
    let b1 := buf[p + 1]
    var hlen: u64 := 0
    var vlen: u64 := 0
    if b1 < 128 {
        hlen := 2
        vlen := b1
    } else if b1 == 129 {
        if p + 3 > end { return 0 }
        let b2 := buf[p + 2]
        if b2 < 128 { return 0 }
        hlen := 3
        vlen := b2
    } else {
        return 0
    }
    join maintains hlen == hdr_len(buf, p, end), vlen == val_len(buf, p, end), 2 <= hlen, hlen <= 4, vlen <= 255
    return hlen + vlen
}
"""
        for arch in ("x86_64", "arm64"):
            _pack_and_dual_verify(src_join_reg_reuse, "f_join_reuse", arch, check_v2=True)

        # Bug #1b (ode_hl.py): `AssignStmt` must prune stale `active_facts` mentioning the mutated variable.
        src_assign_prune = """\
def pick_val(c) {
    if c == 0 then 1 else 2
}

fn f_assign_prune(c: number)
    requires c < 2
    returns pick_val(c)
    trace depends on c
    stack 0
{
    var x: u64 := 0
    if c == 0 {
        if x != 0 { return 9 }
        x := 1
    } else {
        x := 2
    }
    join maintains x == pick_val(c), x <= 2
    return x
}
"""
        for arch in ("x86_64", "arm64"):
            _pack_and_dual_verify(src_assign_prune, "f_assign_prune", arch, check_v2=True)

        # Bug #2 (prove.py): `+%` wrapping add must unwind a non-plain Goal-1 `r..q` block so
        # `takeWrapIf` consumes `t wrap` even when operands are compound linear sums (like 4-byte `imm`).
        src_wrap_compound = """\
def wrap32_add(lhs, buf) {
    (lhs + (buf[0] + 256 * buf[1] + 65536 * buf[2] + 16777216 * buf[3])) % 4294967296
}

fn f_wrap_compound(lhs: number, buf: n bytes, n: number)
    requires n >= 4
    returns wrap32_add(lhs, buf)
    trace depends on n
    stack 0
{
    let imm := buf[0] + 256 * buf[1] + 65536 * buf[2] + 16777216 * buf[3]
    let res := (lhs +% imm) & 4294967295
    return res
}
"""
        for arch in ("x86_64", "arm64"):
            _pack_and_dual_verify(src_wrap_compound, "f_wrap_compound", arch, check_v2=True)

        # Bug #3 (prove.py): Downstream `need entail` after a closed `specGoal` must not be
        # overwritten by a longer dead-end `need spec` backtrack on an earlier line.
        src_downstream_diag = """\
def hlen_spec(buf, p, end) {
    if p + 2 > end then 0
    else if buf[p + 1] < 128 then 2
    else 0
}

def seq_spec(buf, p, end) {
    if hlen_spec(buf, p, end) == 0 then 0
    else if p + hlen_spec(buf, p, end) > end then 0
    else 1
}

fn hlen_helper(buf: n bytes, n: number, p: number, end: number)
    requires p <= end, end <= n, n <= 65536
    returns hlen_spec(buf, p, end)
    trace depends on buf, n, p, end
    stack 0
{
    if p + 2 > end { return 0 }
    if buf[p + 1] < 128 { return 2 }
    return 0
}

fn f_downstream(buf: n bytes, n: number, p: number, end: number)
    requires p <= end, end <= n, n <= 65536
    returns seq_spec(buf, p, end)
    trace depends on buf, n, p, end
    stack 64
{
    let h := hlen_helper(buf, n, p, end)
    if h == 0 { return 0 }
    if p + h > end { return 0 }
    return 1
}
"""
        with tempfile.TemporaryDirectory() as td:
            sp = os.path.join(td, "down.ode")
            with open(sp, "w") as f:
                f.write(src_downstream_diag)
            with self.assertRaises(ode_audit.PackProofError) as cm_d:
                ode_audit.pack_verified(
                    sp, out_obj=os.path.join(td, "o.o"), out_proof=os.path.join(td, "o.proof"),
                    fn_name="f_downstream", target="x86_64", c_abi=True,
                )
            self.assertIn("need entail", cm_d.exception.reason)
            self.assertNotIn("need below", cm_d.exception.reason)

        # Bug #4 (hl-default-v8): `while f != 0` records `1 <= f` in `active_facts` so inner `join maintains`
        # preserves `f >= 1` for `f -= 1`.
        src_neq_zero_loop = """\
def count_down(n) {
    n
}

fn f_neq_zero(n: number)
    requires n < 1000
    returns count_down(n)
    trace depends on n
    stack 0
{
    var f: u64 := n
    var acc: u64 := 0
    while f != 0
        maintains acc + f == n
        decreases f
    {
        var step: u64 := 0
        if f > 1 { step := 1 } else { step := 1 }
        join maintains step == 1
        acc += step
        f -= 1
    }
    return acc
}
"""
        for arch in ("x86_64", "arm64"):
            _pack_and_dual_verify(src_neq_zero_loop, "f_neq_zero", arch, check_v2=True)

    def test_16_unified_inline_fn_const_stack_and_strict_check(self):
        """Phase 2 end-to-end tests across x86_64 + arm64 with dual verification (odeverify + verify2.py):
        1. Target-specialized `inline fn` with `const` params, `-> ty`, nested calls, and `for ... unroll`
           + compile-time `if` (`mul_const` in pure Ode, `my_rotr32`/`my_rotl32` with `for x86_64`/`for arm64`).
        2. Runtime arg passed to `const` param is refused loudly.
        3. Contracted `inline fn` with `select(...)` called inside a `while` loop with `writes`:
           strict call-site `check`, auto-`join` forwarding enclosing `writes`, zero `call` insns,
           AND standalone `ode_audit.audit_inlines` verification across both targets.
        4. Negative control: violated `requires` on contracted `inline fn` is refused even when
           the expanded machine instructions would never overflow.
        5. Early `return` inside `if` inside contracted `inline fn` (`clamp_hi`) verifies both targets.
        6. `stack(x86_64) var` places on stack on x86_64 and keeps 0-stack register on arm64.
        """
        # 1a. Pure-Ode `mul_const(x, const k)` via `for bit in 0..64 unroll` + compile-time `if`!
        src_mul_const = """\
def times25(x) {
    25 * x
}

inline fn mul_const(x: u64, const k: u64) -> u64 {
    var acc: u64 := 0
    for bit in 0..64 unroll {
        if ((k >> bit) & 1) == 1 {
            if bit == 0 {
                acc += x
            } else {
                acc += x << bit
            }
        }
    }
    return acc
}

fn f_times25(x: number)
    requires x < 100000
    returns times25(x)
    trace depends on x
    stack 0
{
    return mul_const(x, 25)
}
"""
        for arch in ("x86_64", "arm64"):
            _pack_and_dual_verify(src_mul_const, "f_times25", arch, check_v2=True)

        # 1b. Target-specialized `for x86_64` / `for arm64` vector `inline fn` with `const k` + nested `my_rotl32`!
        src_vec_inline = """\
def rot_block(ws) {
    [ws[i] >>> 24 for i in 0..4]
}

inline fn my_rotr32(v: u32x4, const k: u64) -> u32x4
    for x86_64 { return (v >> k) | (v << (32 - k)) }
    for arm64  { return (v >> k) | (v << (32 - k)) }

inline fn my_rotl32(v: u32x4, const k: u64) -> u32x4 {
    return my_rotr32(v, 32 - k)
}

fn f_rot_vec(src: 16 bytes, out: 16 bytes)
    requires no_overlap(src, out)
    ensures out = bytes_of(rot_block(words(src)))
    trace depends on nothing
    stack 0
{
    let v: u32x4 := src.u32x4(0)
    let r: u32x4 := my_rotl32(v, 8)
    out.u32x4(0) := r
    return
}
"""
        for arch in ("x86_64", "arm64"):
            _pack_and_dual_verify(src_vec_inline, "f_rot_vec", arch, check_v2=False)

        # 2. Passing runtime `var` to `const` param is rejected loudly.
        src_bad_const = """\
def id(x) { x }
inline fn shift_k(x: u64, const k: u64) -> u64 { return x << k }
fn f_bad(x: number, k: number)
    requires x < 100, k < 8
    returns id(x)
    trace depends on x, k
    stack 0
{
    return shift_k(x, k)
}
"""
        p_bad = ode_unified.parse_unified(src_bad_const, src="bad_const.ode")
        with self.assertRaises(ode_unified.UnifiedErr) as cm_c:
            ode_unified.target_source_view(p_bad, "x86_64", src="bad_const.ode")
        self.assertIn("compile-time constant", str(cm_c.exception))

        # 3. Contracted `inline fn` with `select(...)` inside a `while` loop with `writes`:
        # strict call-site `check`, auto-`join` forwarding `writes`, zero `call` insns, AND standalone audit!
        src_contracted_inl = """\
def map_byte(c) {
    if c >= 65 then
        if c <= 90 then c - 65 else c
    else c
}

def map_all(src) {
    [map_byte(src[i]) % 256 for i in 0..64]
}

inline fn lower_ascii(c: u8) -> u64
    requires c <= 255
    returns map_byte(c)
{
    var d: u64 := c
    d := select(65 <= c && c <= 90, c - 65, d)
    return d
}

fn f_map_buf(src: n bytes, out: 64 bytes, n: number)
    requires no_overlap(src, out)
    requires n >= 64
    requires n <= 64
    ensures out = map_all(src)
    trace depends on n
    stack 0
{
    var i: u64 := 0
    while i < 64
        maintains i <= 64
        writes out[.. i] = map_all(src)
        decreases 64 - i
    {
        let b: u64 := lower_ascii(src[i])
        out[i] := b
        i += 1
    }
    return
}
"""
        for arch in ("x86_64", "arm64"):
            _pack_and_dual_verify(src_contracted_inl, "f_map_buf", arch, check_v2=True)
            # Confirm zero `call`/`bl` emitted inside `f_map_buf`!
            p = ode_unified.parse_unified(src_contracted_inl, src="inl_map.ode")
            asm = "\n".join(p["fns_by_name"]["f_map_buf"]["impls"][arch]["lines"])
            self.assertNotIn("call ", asm)
            self.assertNotIn("bl ", asm)
        with tempfile.TemporaryDirectory() as td:
            sp = os.path.join(td, "inl_map.ode")
            with open(sp, "w", encoding="utf-8") as f:
                f.write(src_contracted_inl)
            aud = ode_audit.audit_inlines(sp)
            self.assertEqual(len(aud), 2)
            self.assertEqual({r["target"] for r in aud}, {"x86_64", "arm64"})
            for r in aud:
                self.assertEqual(r["verdict"], "shown")

        # 4. Negative control: violated `requires` on contracted `inline fn` MUST be refused even
        # though `a + 1` alone would never overflow for `x < 1000`!
        src_bad_req = """\
def add1(x) { x + 1 }

inline fn narrow_add1(a: u64) -> u64
    requires a <= 50
    returns add1(a)
{
    return a + 1
}

fn f_caller_bad(x: number)
    requires x < 1000
    returns add1(x)
    trace depends on x
    stack 0
{
    return narrow_add1(x)
}
"""
        for arch in ("x86_64", "arm64"):
            with self.assertRaises(ode_audit.PackProofError):
                _pack_and_dual_verify(src_bad_req, "f_caller_bad", arch, check_v2=False)

        # 5. Early `return` inside `if` inside contracted `inline fn` (`clamp_hi`) + standalone audit!
        src_early_ret = """\
def clamp50(x) {
    if x >= 50 then 50 else x
}

inline fn clamp_hi(x: u64) -> u64
    requires x <= 100
    returns clamp50(x)
    trace depends on x
{
    if x >= 50 {
        return 50
    }
    return x
}

fn f_clamp(x: number)
    requires x <= 100
    returns clamp50(x)
    trace depends on x
    stack 0
{
    let y: u64 := clamp_hi(x)
    return y
}
"""
        for arch in ("x86_64", "arm64"):
            _pack_and_dual_verify(src_early_ret, "f_clamp", arch, check_v2=True)
        with tempfile.TemporaryDirectory() as td:
            sp = os.path.join(td, "clamp.ode")
            with open(sp, "w", encoding="utf-8") as f:
                f.write(src_early_ret)
            aud = ode_audit.audit_inlines(sp)
            self.assertEqual(len(aud), 2)
            for r in aud:
                self.assertEqual(r["verdict"], "shown")

        # 6. `stack(x86_64) var` allocates stack on x86_64 and keeps 0-stack register on arm64!
        src_stack_arch = """\
def sum3(a, b, c) { a + b + c }

fn f_stack_arch(a: number, b: number, c: number)
    requires a < 100, b < 100, c < 100
    returns sum3(a, b, c)
    trace depends on a, b, c
{
    stack(x86_64) var t: u64 := a + b
    return t + c
}
"""
        p_sa = ode_unified.parse_unified(src_stack_arch, src="stack_arch.ode")
        self.assertGreater(p_sa["fns_by_name"]["f_stack_arch"]["impls"]["x86_64"]["hl_meta"]["frame_bytes"], 0)
        self.assertEqual(p_sa["fns_by_name"]["f_stack_arch"]["impls"]["arm64"]["hl_meta"]["total_stack"], 0)
        for arch in ("x86_64", "arm64"):
            _pack_and_dual_verify(src_stack_arch, "f_stack_arch", arch, check_v2=True)

    def test_17_hl_v9_forensic_regressions(self):
        """Regression tests for hl-default-v9 forensic fixes:
        1. Compound `decreases end - i` on a `fn` contract gives a crisp parse-time diagnostic (never leaks to Lean),
           while single-parameter `decreases rem` stays valid.
        2. No-free-register diagnostic from an `inline fn` on `x86_64` recommends `stack(x86_64) var <outer_var>`.
        """
        src_fn_dec = """\
def id(n) { n }
fn f_dec(i: number, end: number)
    requires i <= end, end <= 10
    returns id(end - i)
    decreases end - i
    stack 32 + 32 * (end - i)
{
    return end - i
}
"""
        with self.assertRaises(ode_unified.UnifiedErr) as cm:
            ode_unified.parse_unified(src_fn_dec, src="dec.ode")
        self.assertIn("must name a single numeric parameter", str(cm.exception))
        self.assertIn("while", str(cm.exception))

        # Trigger `x86_64` no-free-register from inside an `inline fn` with 12 live outer scalars
        src_spill_inl = """\
inline fn add_two(a: u64, b: u64) -> u64 {
    let t := (a | b) - (a & b)
    return t
}
fn f_reg_press(a: u64, b: u64, c: u64, d: u64) -> u64
    requires a < 10, b < 10, c < 10, d < 10
    returns a
    trace depends on a, b, c, d
{
    let v0 := a + 1
    let v1 := b + 1
    let v2 := c + 1
    let v3 := d + 1
    let v4 := a + 2
    let v5 := b + 2
    let v6 := c + 2
    let v7 := d + 2
    let r := add_two(v0 + v1, v2 + v3)
    return a + (b & 0) + (c & 0) + (d & 0) + (r & 0) + (v4 & 0) + (v5 & 0) + (v6 & 0) + (v7 & 0) + (v0 & 0) + (v1 & 0) + (v2 & 0) + (v3 & 0)
}
"""
        p_sp = ode_unified.parse_unified(src_spill_inl, src="sp.ode")
        err_x86 = p_sp["fns_by_name"]["f_reg_press"]["impls"]["x86_64"].get("hl_err") or ""
        self.assertIn("has no free register", err_x86)
        self.assertIn("stack(x86_64) var", err_x86)
        self.assertNotIn("stack var t:", err_x86)

    def test_18_hl_v10_forensic_regressions(self):
        """Regression tests for hl-default-v10 forensic fixes:
        1. Mixed `u32x16` + `u32x4` register allocation on x86-64 never aliases `xmmK` with `zmmK`
           and never allocates `zmm15` (colliding with `u32x4` scratch `xmm15`).
        2. Deeply nested balanced vector expressions never silently clobber a live vector scratch
           register — they refuse loudly with a crisp `too deeply nested` error.
        3. Multi-line `join maintains` split across newlines after `==` and `,` parses and verifies `shown`.
        """
        # 1. Mixed 17 live `u32x16` (`zmm16..30`, `zmm1`, `zmm2`) + live `u32x4` (`xmm3`+, NEVER `xmm1`/`xmm2`!)
        src_mixed_vec_live = """\
def sum17(a, b) {
    let d = [a[i] ^ b[i] for i in 0..16]
    let p2 = [d[i] + d[i] for i in 0..16]
    let p4 = [p2[i] + p2[i] for i in 0..16]
    let p8 = [p4[i] + p4[i] for i in 0..16]
    let p16 = [p8[i] + p8[i] for i in 0..16]
    [a[i] + p16[i] for i in 0..16]
}

fn f_mixed_zmm_xmm(out: 64 bytes, out4: 16 bytes, a: 64 bytes, b: 64 bytes)
    requires no_overlap(out, out4, a, b)
    ensures out = bytes_of(sum17(words(a), words(b)))
    ensures out4 = bytes_of([words(a)[0] ^ words(b)[0], words(a)[1] ^ words(b)[1], words(a)[2] ^ words(b)[2], words(a)[3] ^ words(b)[3]])
    trace depends on nothing
for x86_64 needs avx needs avx512 {
    let z0: u32x16 := a.u32x16(0)
    let zb: u32x16 := b.u32x16(0)
    let z1: u32x16 := z0 ^ zb
    let z2: u32x16 := z0 ^ zb
    let z3: u32x16 := z0 ^ zb
    let z4: u32x16 := z0 ^ zb
    let z5: u32x16 := z0 ^ zb
    let z6: u32x16 := z0 ^ zb
    let z7: u32x16 := z0 ^ zb
    let z8: u32x16 := z0 ^ zb
    let z9: u32x16 := z0 ^ zb
    let z10: u32x16 := z0 ^ zb
    let z11: u32x16 := z0 ^ zb
    let z12: u32x16 := z0 ^ zb
    let z13: u32x16 := z0 ^ zb
    let z14: u32x16 := z0 ^ zb
    let z15: u32x16 := z0 ^ zb
    let z16: u32x16 := z0 ^ zb
    let x0: u32x4 := a.u32x4(0)
    let x1: u32x4 := b.u32x4(0)
    out4.u32x4(0) := x0 ^ x1
    let r1: u32x16 := (z1 +% z2) +% (z3 +% z4)
    let r2: u32x16 := (z5 +% z6) +% (z7 +% z8)
    let r3: u32x16 := (z9 +% z10) +% (z11 +% z12)
    let r4: u32x16 := (z13 +% z14) +% (z15 +% z16)
    out.u32x16(0) := z0 +% ((r1 +% r2) +% (r3 +% r4))
}
"""
        p_mx = ode_unified.parse_unified(src_mixed_vec_live, src="mixed.ode", c_abi_fn="f_mixed_zmm_xmm")
        vmap = p_mx["fns_by_name"]["f_mixed_zmm_xmm"]["impls"]["x86_64"]["hl_meta"]["var_map"]
        by_nm = {nm: reg for nm, _, reg, _ in vmap}
        zmm_live = {int(by_nm[f"z{i}"][3:]) for i in range(17)}
        xmm_live = {int(by_nm[f"x{i}"][3:]) for i in range(2)}
        self.assertNotIn(15, zmm_live, f"zmm15 must not be allocated (clobbers u32x4 scratch xmm15): {vmap}")
        self.assertEqual(zmm_live & xmm_live, set(), f"simultaneously live xmmK/zmmK bank collision: {vmap}")
        _pack_and_dual_verify(src_mixed_vec_live, "f_mixed_zmm_xmm", "x86_64", check_v2=False)

        # 2. Deeply nested balanced vector tree refuses cleanly instead of clobbering scratch
        src_deep_vec = """\
fn f_deep(out: 16 bytes, a: 16 bytes, b: 16 bytes)
    requires no_overlap(out, a, b)
    ensures out = out
    trace depends on nothing
{
    let v0: u32x4 := a.u32x4(0)
    let v1: u32x4 := b.u32x4(0)
    out.u32x4(0) := v0 ^ (((v0 ^ v1) ^ (v0 ^ v1)) ^ ((v0 ^ v1) ^ (v0 ^ v1)))
}
"""
        p_dv = ode_unified.parse_unified(src_deep_vec, src="deep.ode", c_abi_fn="f_deep")
        for arch in ("x86_64", "arm64"):
            err = p_dv["fns_by_name"]["f_deep"]["impls"][arch].get("hl_err") or ""
            self.assertIn("too deeply nested", err, f"{arch} should refuse deep nested vec expr, got: {err!r}")

        # 2. Multi-line `join maintains` split after `==` and `,`
        src_ml_join = """\
def dbl(x) {
    if x < 10 then x + x else x + 10
}

fn f_ml_join(x: number)
    requires x <= 100
    returns dbl(x)
    trace depends on x
    stack 0
{
    var r: u64 := 0
    if x < 10 {
        r := x + x
    } else {
        r := x + 10
    }
    join maintains
        r ==
            dbl(x),
        0 <= r,
        r <= 200
    return r
}
"""
        for arch in ("x86_64", "arm64"):
            _pack_and_dual_verify(src_ml_join, "f_ml_join", arch, check_v2=True)

    def test_19_hl_v11_forensic_regressions(self):
        """Regression tests for hl-default-v11 forensic fixes:
        1. `x & 4294967295` on x86-64 emits 1-instruction `mov D32, S32` (zero temp reg) and dual-verifies.
        2. A proof-only `def` referenced only inside `join maintains` (not in the entry contract) is carried
           into `.proof`'s helper spec without changing the canonical `.ode.ocl` contract ID.
        3. Calling a contractless multi-split scalar `inline fn` >= 2 times refuses crisply at compile time.
        4. `_matching_spec_comparisons` resolves `const NAME = INT` when matching `need compare` goals.
        """
        # 1. `x & 4294967295` -> 1-insn `mov r32, r32` on x86_64, dual-verified on both arches
        src_mask32 = """\
def low32_sum(a, b) {
    ((a + b) % 4294967296)
}

fn f_mask32(a: number, b: number)
    returns low32_sum(a, b)
    trace depends on nothing
    stack 0
{
    let s: u64 := (a +% b) & 4294967295
    return s
}
"""
        p_m32 = ode_unified.parse_unified(src_mask32, src="mask32.ode", c_abi_fn="f_mask32")
        x86_lines = p_m32["fns_by_name"]["f_mask32"]["impls"]["x86_64"]["lines"]
        self.assertTrue(any(re.match(r"mov\s+(?:e[a-z]{2}|r\d+d),\s+(?:e[a-z]{2}|r\d+d)\b", ln) for ln in x86_lines), x86_lines)
        self.assertFalse(any(ln.startswith("and ") for ln in x86_lines), x86_lines)
        for arch in ("x86_64", "arm64"):
            _pack_and_dual_verify(src_mask32, "f_mask32", arch, check_v2=True)

        # 2. Proof-only `def` referenced only in `join maintains` (not in entry contract)
        src_proof_def = """\
def u16_le(buf, i) { buf[i] + 256 * buf[i + 1] }
def want_sum(buf) { buf[0] + 256 * buf[1] }

fn f_proof_def(buf: n bytes, n: number)
    requires n >= 2
    returns want_sum(buf)
    trace depends on n
    stack 0
{
    let off: u64 := buf[0] + 256 * buf[1]
    join maintains off == u16_le(buf, 0), off <= 65535
    return off
}
"""
        for arch in ("x86_64", "arm64"):
            _pack_and_dual_verify(src_proof_def, "f_proof_def", arch, check_v2=False)

        # 3. Contractless multi-split scalar `inline fn` called >= 2 times refuses crisply
        src_multi_split_inl = """\
inline fn bad_dec(c: u8) -> u64 {
    return select(c == 65, 1, select(c == 66, 2, 0))
}

fn f_bad_multi(buf: n bytes, n: number)
    requires n >= 2
    returns 0
    trace depends on n
{
    let a := bad_dec(buf[0])
    let b := bad_dec(buf[1])
    return a + b
}
"""
        p_ms = ode_unified.parse_unified(src_multi_split_inl, src="ms.ode", c_abi_fn="f_bad_multi")
        for arch in ("x86_64", "arm64"):
            err = p_ms["fns_by_name"]["f_bad_multi"]["impls"][arch].get("hl_err") or ""
            self.assertIn("branch/select splits", err)
            self.assertIn("returns <spec_expr>", err)

        # 4. `_matching_spec_comparisons` resolves `const OP_EXIT = 149`
        import ode_tool
        spec_const = "const OP_EXIT = 149\ndef step(op, r0) {\n    if op == OP_EXIT then r0 else 0\n}\n"
        hits = ode_tool._matching_spec_comparisons(spec_const, [[-149, 1]], contract={"returns": "step(a0, a1)"})
        self.assertTrue(any("OP_EXIT = 149" in h for h in hits), hits)

    def test_20_phase1_uniform_word_memory(self):
        """Phase 1 cache-and-page memory model regressions:
        1. `fixeds.u32` loads + scalar 32-bit addition (`wAtomK` round-trip to `Node.add`) on both arches.
        2. `inouts.u64` & `inouts.u32` reads BEFORE and AFTER partial writes (`wroteW`) on both arches.
        3. `frameW` (vector stack store) -> scalar `.u64` & `.u32` reads on both arches.
        4. 4-byte scalar stores (`out.u32` & stack `buf.u32`) via `symStore4` on `arm64`.
        5. Pure write-only `out` buffer STILL refused on read (preserving streaming / no-RFO safety).
        6. `advice/estimate.py` static `stlf-width` hazard warning on 8B store -> 16B stack load.
        """
        # 1. Fixed read-only word buffer `.u32` + scalar 32-bit sum (`wAtomK` -> `Node.add`)
        src_fixed_u32 = """\
def sum_pairs(ws) {
    [ws[0] + ws[1], ws[1] + ws[2], ws[2] + ws[3], ws[3] + ws[0]]
}

fn f_fixed_u32(out: 16 bytes, a: 16 bytes)
    requires no_overlap(out, a)
    ensures out = bytes_of(sum_pairs(words(a)))
    trace depends on nothing
{
    let w0: u64 := a.u32(0)
    let w1: u64 := a.u32(4)
    let w2: u64 := a.u32(8)
    let w3: u64 := a.u32(12)
    let s0: u64 := (w0 +% w1) & 4294967295
    let s1: u64 := (w1 +% w2) & 4294967295
    let s2: u64 := (w2 +% w3) & 4294967295
    let s3: u64 := (w3 +% w0) & 4294967295
    out.u64(0) := s0 | (s1 << 32)
    out.u64(8) := s2 | (s3 << 32)
}
"""
        for arch in ("x86_64", "arm64"):
            _pack_and_dual_verify(src_fixed_u32, "f_fixed_u32", arch, check_v2=False)

        # 2. In-out word buffer `.u64` & `.u32` reads BEFORE and AFTER partial write (`wroteW`)
        src_inout_rw = """\
def inout_spec(ws) {
    [ws[0] + ws[2], ws[1] + ws[3], (ws[0] + ws[2]) + ws[2], (ws[1] + ws[3]) + ws[3]]
}

fn f_inout_rw(h: 16 bytes)
    ensures h = bytes_of(inout_spec(words(h)))
    trace depends on nothing
{
    let h01: u64 := h.u64(0)
    let w0: u64 := h01 & 4294967295
    let w1: u64 := h01 >> 32
    let w2: u64 := h.u32(8)
    let w3: u64 := h.u32(12)
    let a: u64 := (w0 +% w2) & 4294967295
    let b: u64 := (w1 +% w3) & 4294967295
    h.u64(0) := a | (b << 32)
    // Read back the just-written words from `h` (read-after-write via `wroteW`!)
    let a_back: u64 := h.u32(0)
    let b_back: u64 := h.u32(4)
    let c: u64 := (a_back +% w2) & 4294967295
    let d: u64 := (b_back +% w3) & 4294967295
    h.u64(8) := c | (d << 32)
}
"""
        for arch in ("x86_64", "arm64"):
            _pack_and_dual_verify(src_inout_rw, "f_inout_rw", arch, check_v2=False)

        # 3. Vector stack store (`frameW`) -> scalar `.u64` & `.u32` loads
        src_framew_scalar = """\
def copy4(ws) { [ws[0], ws[1], ws[2], ws[3]] }

fn f_framew_scalar(out: 16 bytes, src: 16 bytes)
    requires no_overlap(out, src)
    ensures out = bytes_of(copy4(words(src)))
    trace depends on nothing
{
    buf tmp[16]
    let v: u32x4 := src.u32x4(0)
    tmp.u32x4(0) := v
    let p01: u64 := tmp.u64(0)
    let w2: u64 := tmp.u32(8)
    let w3: u64 := tmp.u32(12)
    out.u64(0) := p01
    out.u64(8) := w2 | (w3 << 32)
}
"""
        for arch in ("x86_64", "arm64"):
            _pack_and_dual_verify(src_framew_scalar, "f_framew_scalar", arch, check_v2=False)

        # 4. 4-byte scalar stores (`buf.u32` & `out.u32`) on `arm64` via `symStore4`
        src_store4 = """\
def rev4(ws) { [ws[3], ws[2], ws[1], ws[0]] }

fn f_store4(out: 16 bytes, src: 16 bytes)
    requires no_overlap(out, src)
    ensures out = bytes_of(rev4(words(src)))
    trace depends on nothing
{
    buf tmp[16]
    tmp.u32(0) := src.u32(12)
    tmp.u32(4) := src.u32(8)
    tmp.u32(8) := src.u32(4)
    tmp.u32(12) := src.u32(0)
    out.u32(0) := tmp.u32(0)
    out.u32(4) := tmp.u32(4)
    out.u32(8) := tmp.u32(8)
    out.u32(12) := tmp.u32(12)
}
"""
        _pack_and_dual_verify(src_store4, "f_store4", "arm64", check_v2=False)

        # 5. Pure write-only `out` buffer (`arg out out N`) STILL refused on `.u32`/`.u64` read
        src_wo_read = """\
fn f_wo_read(out: 16 bytes, src: 16 bytes)
    requires no_overlap(out, src)
    ensures out = src
    trace depends on nothing
{
    let bad: u64 := out.u32(0)
    out.u64(0) := src.u64(0)
    out.u64(8) := src.u64(8) +% (bad -% bad)
}
"""
        for arch in ("x86_64", "arm64"):
            with tempfile.TemporaryDirectory(prefix="ode_wo_") as td:
                src_p = Path(td) / "wo.ode"
                src_p.write_text(src_wo_read, encoding="utf-8")
                with self.assertRaises(ode_audit.PackProofError) as ctx:
                    ode_audit.pack_verified(
                        str(src_p), None, str(Path(td) / "o.o"), str(Path(td) / "o.proof"),
                        fn_name="f_wo_read", target=arch, c_abi=True, stores=STD_STORES,
                    )
                self.assertIn("given only to write", str(ctx.exception))

        # 6. `ode advise` static `stlf-width` hazard hint (8B stack store -> 16B stack load)
        src_stlf = """\
def id4(ws) { [ws[0], ws[1], ws[2], ws[3]] }

fn f_stlf(out: 16 bytes, src: 16 bytes)
    requires no_overlap(out, src)
    ensures out = bytes_of(id4(words(src)))
    trace depends on nothing
{
    buf tmp[16]
    let a: u64 := src.u64(0)
    let b: u64 := src.u64(8)
    tmp.u64(0) := a
    tmp.u64(8) := b
    let v: u32x4 := tmp.u32x4(0)
    out.u32x4(0) := v
}
"""
        import advice.estimate as est
        for arch in ("x86_64", "arm64"):
            with tempfile.TemporaryDirectory(prefix="ode_stlf_") as td:
                src_p = Path(td) / "stlf.ode"
                src_p.write_text(src_stlf, encoding="utf-8")
                out_o = str(Path(td) / "stlf.o")
                out_p = str(Path(td) / "stlf.proof")
                res = ode_audit.pack_verified(
                    str(src_p), None, out_o, out_p,
                    fn_name="f_stlf", target=arch, c_abi=True, stores=STD_STORES,
                )
                self.assertEqual(res["verdict"], "shown", f"stlf ({arch}): {res}")
                sym = res["symbol"]
                _, rows = est.decode_object(out_o, sym, arch)
                srep = est.static_analyze(rows, arch)
                kinds = [ht["kind"] for ht in srep.get("hints") or []]
                self.assertIn("stlf-width", kinds, f"expected stlf-width hint on {arch}, got {srep.get('hints')}")
                # Phase 2 leaf x86-64 stack alignment check: `buf tmp[16]` must NOT emit `stack-align` warning!
                self.assertNotIn("stack-align", kinds, f"unexpected stack-align warning on {arch}: {srep.get('hints')}")

    def test_21_phase2_cache_line_alignment_disjointness_and_locality(self):
        """Phase 2 cache-line & VM-page alignment, cache-line disjointness, and static locality metrics:
        1. `requires aligned(buf, 64)` / `aligned(page, 4096)` canonicalization + `verify2.py` + `odeverify`
           (`buf & 63 == 0` and `page & 4095 == 0` simplify without extra facts).
        2. Call-site alignment & `line_disjoint` propagation (`128 B` -> `64 B`) and arena sub-slice
           partitioning (`arena`, `arena + 64` accepted; `arena + 32` false-sharing refused) in BOTH
           Lean 4 (`odeverify`) AND `verify2.py`.
        3. `advice/estimate.py` static locality metrics: unit-stride stream detection, `memory_footprint`
           cache lines / VM pages, `line-split` hint, and `stride-4k-alias` hint.
        """
        import ode_canon
        import advice.estimate as est

        # 1. `requires aligned(...)` + `requires line_disjoint(...)` canonicalization & dual verification
        src_align_call = """\
fn leaf_sum(a: n bytes, b: n bytes, n: u64) -> u64
    requires n >= 1, n <= 64
    requires aligned(a, 64)
    requires line_disjoint(a, b, 64)
    returns a[0] + b[0]
    trace depends on n
{
    let x: u64 := a[0]
    let y: u64 := b[0]
    return x + y
}

fn caller_ok(p: n bytes, q: n bytes, n: u64) -> u64
    requires n >= 1, n <= 64
    requires aligned(p, 128)
    requires line_disjoint(p, q, 128)
    returns p[0] + q[0]
    trace depends on n
{
    return leaf_sum(p, q, n)
}
"""
        for arch in ("x86_64", "arm64"):
            res = _pack_and_dual_verify(src_align_call, "caller_ok", arch, check_v2=True)
            self.assertIn("requires aligned(a0, 128)", res["canonical_ocl"])
            self.assertIn("requires line_disjoint(a0, a1, 128)", res["canonical_ocl"])

        # Negative control 1a: caller only guarantees 16-byte alignment, callee asks 64-byte -> REFUSED
        src_align_bad = src_align_call.replace("requires aligned(p, 128)", "requires aligned(p, 16)")
        for arch in ("x86_64", "arm64"):
            with tempfile.TemporaryDirectory(prefix="ode_albad_") as td:
                sp = Path(td) / "albad.ode"
                sp.write_text(src_align_bad, encoding="utf-8")
                with self.assertRaises(ode_audit.PackProofError) as ctx:
                    ode_audit.pack_verified(
                        str(sp), None, str(Path(td) / "o.o"), str(Path(td) / "o.proof"),
                        fn_name="caller_ok", target=arch, c_abi=True, stores=STD_STORES,
                    )
                self.assertIn("64-byte aligned", str(ctx.exception))

        # Negative control 1b: caller omits `line_disjoint`, callee asks `line_disjoint(a, b, 64)` -> REFUSED
        src_ld_bad = src_align_call.replace("requires line_disjoint(p, q, 128)\n", "")
        for arch in ("x86_64", "arm64"):
            with tempfile.TemporaryDirectory(prefix="ode_ldbad_") as td:
                sp = Path(td) / "ldbad.ode"
                sp.write_text(src_ld_bad, encoding="utf-8")
                with self.assertRaises(ode_audit.PackProofError) as ctx:
                    ode_audit.pack_verified(
                        str(sp), None, str(Path(td) / "o.o"), str(Path(td) / "o.proof"),
                        fn_name="caller_ok", target=arch, c_abi=True, stores=STD_STORES,
                    )
                self.assertIn("64-byte cache-line disjoint", str(ctx.exception))

        # 2. Machine-level arena sub-slice partitioning + alignment bitmask checks in BOTH Lean 4 AND verify2.py
        import lean_verify, verify2
        def _run_lean(st_path, pf_path):
            r = subprocess.run([lean_verify.EXE, lean_verify.TABLE, st_path, pf_path], capture_output=True, text=True)
            return r.returncode == 0, (r.stdout + r.stderr)

        stmt_dir = tempfile.TemporaryDirectory(prefix="ode_p2_stmt_")
        try:
            td = Path(stmt_dir.name)
            tab_x86 = lean_verify.TABLE
            # 2a. `buf & 63 == 0` on 64-byte aligned buffer (`a: n bytes`)
            stmt_mask = """\
fn check_align
arg buf bytes n
arg n number
align buf 64
below n 1000
atleast n 1
returns (num 0)
stack 0
i 0 4 .mov 64 (.reg .rax) (.reg .rdi)
i 4 8 .and 64 (.reg .rax) (.imm 63)
i 8 9 .ret
"""
            pf_mask = "for check_align\n"
            st_p, pf_p = str(td / "mask.s"), str(td / "mask.p")
            Path(st_p).write_text(stmt_mask, encoding="utf-8")
            Path(pf_p).write_text(pf_mask, encoding="utf-8")
            ok_lean, out_lean = _run_lean(st_p, pf_p)
            self.assertTrue(ok_lean, f"aligned mask Lean failed: {out_lean}")
            verify2.verify_files(tab_x86, st_p, pf_p)

            # 2b. Arena splitting (compiled ELF + full prove + Lean 4 verify on BOTH x86_64 and arm64!):
            # `arena` (128 bytes, aligned 64) split at +64 -> `line_disjoint(a, b, 64)` SHOWN!
            src_arena_ok = """\
def sum_ab(h, a, b) {
    [h[0] + a[0] + b[0], h[1] + a[1] + b[1], h[2] + a[2] + b[2], h[3] + a[3] + b[3]]
}

fn worker(out: 16 bytes, a: 64 bytes, b: 64 bytes)
    requires no_overlap(out, a, b)
    requires aligned(a, 64)
    requires aligned(b, 64)
    requires line_disjoint(a, b, 64)
    ensures out = bytes_of(sum_ab(words(out), words(a[0 .. 16]), words(b[0 .. 16])))
    trace depends on nothing
{
    let vh: u32x4 := out.u32x4(0)
    let va: u32x4 := a.u32x4(0)
    let vb: u32x4 := b.u32x4(0)
    out.u32x4(0) := (vh +% va) +% vb
}

fn split_ok(out: 16 bytes, arena: 128 bytes)
    requires no_overlap(out, arena)
    requires aligned(arena, 64)
    ensures out = bytes_of(sum_ab(words(out), words(arena[0 .. 16]), words(arena[64 .. 80])))
    stack 16
    trace depends on nothing
for x86_64 needs avx {
    movups xmm0, [rdi]
    movups [rdi], xmm0
    mov rdx, rsi
    add rdx, 64
    call worker
    ret
}
for arm64 {
    sub sp, sp, 16
    str x30, [sp, 0]
    ldr q0, [x0, 0]
    str q0, [x0, 0]
    add x2, x1, 64
    bl worker
    ldr x30, [sp, 0]
    add sp, sp, 16
    ret
}
"""
            for arch in ("x86_64", "arm64"):
                _pack_and_dual_verify(src_arena_ok, "split_ok", arch, check_v2=False)

            # 2c. NEGATIVE CONTROL: splitting `arena` at +32 (no byte overlap, SAME 64B cache line!) -> REFUSED!
            src_arena_fs = """\
def sum_ab(h, a, b) {
    [h[0] + a[0] + b[0], h[1] + a[1] + b[1], h[2] + a[2] + b[2], h[3] + a[3] + b[3]]
}

fn worker(out: 16 bytes, a: 32 bytes, b: 32 bytes)
    requires no_overlap(out, a, b)
    requires aligned(a, 64)
    requires line_disjoint(a, b, 64)
    ensures out = bytes_of(sum_ab(words(out), words(a[0 .. 16]), words(b[0 .. 16])))
    trace depends on nothing
{
    let vh: u32x4 := out.u32x4(0)
    let va: u32x4 := a.u32x4(0)
    let vb: u32x4 := b.u32x4(0)
    out.u32x4(0) := (vh +% va) +% vb
}

fn split_fs(out: 16 bytes, arena: 128 bytes)
    requires no_overlap(out, arena)
    requires aligned(arena, 64)
    ensures out = bytes_of(sum_ab(words(out), words(arena[0 .. 16]), words(arena[32 .. 48])))
    stack 16
    trace depends on nothing
for x86_64 needs avx {
    movups xmm0, [rdi]
    movups [rdi], xmm0
    mov rdx, rsi
    add rdx, 32
    call worker
    ret
}
for arm64 {
    sub sp, sp, 16
    str x30, [sp, 0]
    ldr q0, [x0, 0]
    str q0, [x0, 0]
    add x2, x1, 32
    bl worker
    ldr x30, [sp, 0]
    add sp, sp, 16
    ret
}
"""
            for arch in ("x86_64", "arm64"):
                sp_fs = td / f"fs_{arch}.ode"
                sp_fs.write_text(src_arena_fs, encoding="utf-8")
                with self.assertRaises(ode_audit.PackProofError) as ctx_fs:
                    ode_audit.pack_verified(
                        str(sp_fs), None, str(td / f"fs_{arch}.o"), str(td / f"fs_{arch}.proof"),
                        fn_name="split_fs", target=arch, c_abi=True, stores=STD_STORES,
                    )
                self.assertIn("64-byte cache-line disjoint", str(ctx_fs.exception))

            # 2d. Also verify `verify2.py` independently refuses false sharing at +32 on raw statement/proof!
            stmt_fs_raw = """\
fn worker
arg a fixed 32
arg b fixed 32
align a 64
linedisjoint a b 64
returns (num 0)
stack 0
i 0 4 .mov 64 (.reg .rax) (.imm 0)
i 4 5 .ret

fn split_fs
arg arena fixed 128
align arena 64
returns (num 0)
stack 8
i 0 4 .mov 64 (.reg .rsi) (.reg .rdi)
i 4 8 .add 64 (.reg .rsi) (.imm 32)
i 8 13 .call worker
i 13 14 .ret
"""
            st_fs, pf_fs = str(td / "fs_raw.s"), str(td / "fs_raw.p")
            Path(st_fs).write_text(stmt_fs_raw, encoding="utf-8")
            Path(pf_fs).write_text("for worker\nfor split_fs\n", encoding="utf-8")
            with self.assertRaises(verify2.Refuse) as ctx_v2:
                verify2.verify_files(tab_x86, st_fs, pf_fs)
            self.assertIn("64-byte cache-line disjoint", str(ctx_v2.exception))
        finally:
            stmt_dir.cleanup()

        # 3. `advice/estimate.py` static locality: unit-stride loop stream + line-split + stride-4k-alias
        src_loop = """\
def sum_u8(bs, n) {
    if n == 0 then 0 else sum_u8(bs, n - 1) + bs[n - 1]
}

fn scan_u8(src: n bytes, n: u64) -> u64
    requires n <= 4096
    returns sum_u8(src, n)
    trace depends on n
{
    var i: u64 := 0
    var acc: u64 := 0
    while i < n
        maintains 0 <= i, i <= n, acc == sum_u8(src, i), acc <= 255 * i
        decreases n - i
    {
        acc += src[i]
        i += 1
    }
    return acc
}
"""
        for arch in ("x86_64", "arm64"):
            with tempfile.TemporaryDirectory(prefix="ode_loc_") as td:
                sp = Path(td) / "loc.ode"
                sp.write_text(src_loop, encoding="utf-8")
                oo, op = str(Path(td) / "loc.o"), str(Path(td) / "loc.proof")
                res = ode_audit.pack_verified(
                    str(sp), None, oo, op, fn_name="scan_u8", target=arch, c_abi=True, stores=STD_STORES,
                )
                self.assertEqual(res["verdict"], "shown")
                _, rows = est.decode_object(oo, res["symbol"], arch)
                srep = est.static_analyze(rows, arch)
                self.assertIn("memory_footprint", srep)
                self.assertTrue(len(srep["loops"]) >= 1)
                loc = srep["loops"][0]["locality"]
                self.assertGreaterEqual(loc["read_streams"], 1)
                self.assertEqual(loc["read_bytes_per_iter"], 1)
                self.assertEqual(loc["streams"][0]["pattern"], "unit")
                self.assertEqual(loc["streams"][0]["stride"], 1)
                rep_txt = est.format_report("scan_u8", srep)
                self.assertIn("locality:", rep_txt)

        # 3b. Synthetic decoded x86-64 checks for `line-split` (16B load at [rsi+56]) and `stride-4k-alias` (add rsi, 4096)
        dec_split = [
            (0, 5, ".xloadu 0 .rsi 56"),
            (5, 9, ".xstoreu .rdi 0 0"),
            (9, 10, ".ret"),
        ]
        rep_sp = est.static_analyze(dec_split, "x86_64", "zen5")
        self.assertIn("line-split", [h["kind"] for h in rep_sp["hints"]])

        dec_4k = [
            (0, 3, ".mov 64 (.reg .rax) (.mem .rsi 0)"),
            (3, 10, ".add 64 (.reg .rsi) (.imm 4096)"),
            (10, 14, ".sub 64 (.reg .rdx) (.imm 1)"),
            (14, 16, ".jne 0"),
            (16, 17, ".ret"),
        ]
        rep_4k = est.static_analyze(dec_4k, "x86_64", "zen5")
        self.assertIn("stride-4k-alias", [h["kind"] for h in rep_4k["loops"][0]["lints"]])


if __name__ == "__main__":
    unittest.main()
