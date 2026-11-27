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
for d in (HERE, os.path.join(ROOT, "proof-core"), os.path.join(ROOT, "kcheck"),
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
            fn_name=fn_name, target=target, c_abi=c_abi,
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
        parsed = ode_unified.parse_unified_file(str(src_p), c_abi_fn=fn_name)
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
            "u32x4": ("u32x4", "u32x4(1, 2, 3, 4)", ("x86_64", "arm64"), ""),
            "pack_u64x2": ("u32x4", "pack_u64x2(k, k)", ("x86_64", "arm64"), ""),
            "rotl32": ("u32x4", "rotl32(a, 7)", ("x86_64", "arm64"), ""),
            "rotr32": ("u32x4", "rotr32(a, 16)", ("x86_64", "arm64"), ""),
            "shl32": ("u32x4", "shl32(a, 3)", ("x86_64", "arm64"), ""),
            "shr32": ("u32x4", "shr32(a, 10)", ("x86_64", "arm64"), ""),
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

        # 2. `inline fn foo(x: u32x4) -> u32x4` must raise clean UnifiedErr (never uncaught HLErr traceback)
        src_inl = """\
inline fn bad_inl(x: u32x4) -> u32x4 {
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
                 "--out", str(td_p / "b.o"), "--proof", str(td_p / "b.p")],
                capture_output=True, text=True,
            )
            self.assertNotEqual(r.returncode, 0)
            out = r.stdout + r.stderr
            self.assertIn("concrete execution disagrees", out, f"refute_conc skipped blake3_compress1! got:\n{out[:500]}")

    def test_06_metamorphic_tail_call_multi_open_and_unroll_t_same_dual_verify(self):
        """Differential + metamorphic test covering BOTH Bug #1 (`verify2.py` tail-call multi-open)
        and Bug #2 (`prove.py` multi-step unroll `t same` + Gomory cut `(69 % 16) * 2 == 10`)."""
        spec_txt = (Path(ROOT) / "paper/EXPERIMENTS/tasks/ipv4_valid_spec.ode").read_text(encoding="utf-8")
        # 1. Tail-call multi-open (exact shape of muse-spark-open arm64 ipv4_valid!)
        src_tail = """\
use spec = "ipv4_valid_spec.ode"

fn fold_ok(s: u64) -> u64
    returns spec.fold2_ok(s)
    trace depends on s
    stack 0
{
    let t1 := s % 65536 + s / 65536
    let t2 := t1 % 65536 + t1 / 65536
    return select(t2 == 65535, 1, 0)
}

fn checksum4_tail(pkt: n bytes, n: number) -> u64
    requires n <= 65535, n >= 8
    returns spec.sum16_check(pkt, 0, 4, 0)
    trace depends on pkt, n
    stack 0
{
    var acc: u64 := 0
    for k in 0..4 unroll {
        acc += pkt[2 * k] * 256 + pkt[2 * k + 1]
    }
    return fold_ok(acc)
}
"""
        for arch in ("x86_64", "arm64"):
            _pack_and_dual_verify(src_tail, "checksum4_tail", arch,
                                  extra_files={"ipv4_valid_spec.ode": spec_txt}, check_v2=True)

        # 2. Metamorphic 4-step unroll with mid-function `join maintains` + Gomory `(69 % 16) * 2 == 10`
        src_unroll = """\
use spec = "ipv4_valid_spec.ode"

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
"""
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

        # Locked manifest of grandfathered multi-instruction vector intrinsics (exact max body insns per target).
        # BINDING RULE: never add an entry here without explicit approval!
        EXPLICIT_MULTI_INSN_OPS = {
            "rotl32": {"x86_64": 3, "arm64": 3},
            "rotr32": {"x86_64": 3, "arm64": 3},
            "pack_u64x2": {"x86_64": 3, "arm64": 3},
        }

        vec_probes = [
            ("add", "x + y", ("x86_64", "arm64")),
            ("xor", "x ^ y", ("x86_64", "arm64")),
            ("and", "x & y", ("x86_64", "arm64")),
            ("or", "x | y", ("x86_64", "arm64")),
            ("shr", "x >> 10", ("x86_64", "arm64")),
            ("shl", "x << 3", ("x86_64", "arm64")),
            ("shl32", "shl32(x, 3)", ("x86_64", "arm64")),
            ("shr32", "shr32(x, 10)", ("x86_64", "arm64")),
            ("rotl32", "rotl32(x, 7)", ("x86_64", "arm64")),
            ("rotr32", "rotr32(x, 7)", ("x86_64", "arm64")),
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
            ("pack_u64x2", "pack_u64x2(w0, w1)", ("x86_64", "arm64")),
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


if __name__ == "__main__":
    unittest.main()
