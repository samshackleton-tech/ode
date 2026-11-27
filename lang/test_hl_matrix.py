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
            "const_u32x4": ("u32x4", "const_u32x4(0x6A09E667)", ("x86_64", "arm64"), ""),
            "u32x4": ("u32x4", "u32x4(1, 2, 3, 4)", ("x86_64", "arm64"), ""),
            "u32x4.splat": ("u32x4", "u32x4.splat(0x6A09E667)", ("x86_64", "arm64"), ""),
            "u32x4.of": ("u32x4", "u32x4.of(1, 2, 3, 4)", ("x86_64", "arm64"), ""),
            "u32x16": ("u32x16", "u32x16(k)", ("x86_64",), "needs avx512"),
            "u32x16.splat": ("u32x16", "u32x16.splat(k)", ("x86_64",), "needs avx512"),
            "pack_u64x2": ("u32x4", "pack_u64x2(k, k)", ("x86_64", "arm64"), ""),
            "rotl32": ("u32x4", "rotl32(a, 7)", ("x86_64", "arm64"), ""),
            "rotr32": ("u32x4", "rotr32(a, 16)", ("x86_64", "arm64"), ""),
            "shl32": ("u32x4", "shl32(a, 3)", ("x86_64", "arm64"), ""),
            "shr32": ("u32x4", "shr32(a, 10)", ("x86_64", "arm64"), ""),
            "shuf32": ("u32x4", "shuf32(a, 0x39)", ("x86_64", "arm64"), ""),
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

    def test_02_vector_shifts_constructors_and_portable_shuf32_verify_both_arches(self):
        """`v >> k`, `v << k`, `u32x4(w0, w1, w2, w3)` (both const & runtime scalar!),
        `u32x4.splat(x)`, `u32x4.of(...)`, `unpackhi64`, and `shuf32` (rotations & lane splats)
        must ALL verify `shown` on BOTH `x86_64` and `arm64`!"""
        src = """\
def vec_test(ws, a, b) {
    let x = [ws[0], ws[1], ws[2], ws[3]]
    let y = [ws[4], ws[5], ws[6], ws[7]]
    let s1 = [x[0] >> 10, x[1] >> 10, x[2] >> 10, x[3] >> 10]
    let s2 = [x[0] >>> 29, x[1] >>> 29, x[2] >>> 29, x[3] >>> 29]
    let hi = [x[2], x[3], y[2], y[3]]
    let rot = [x[1], x[2], x[3], x[0]]
    let sp0 = [y[0], y[0], y[0], y[0]]
    let rt = [word(a), word(b), word(0x12345678), word(0x9ABCDEF0)]
    let spc = [word(0x6A09E667), word(0x6A09E667), word(0x6A09E667), word(0x6A09E667)]
    let spr = [word(a), word(a), word(a), word(a)]
    [s1[i] ^ s2[i] ^ hi[i] ^ rot[i] ^ sp0[i] ^ rt[i] ^ spc[i] ^ spr[i] for i in 0..4]
}

fn vec_ops(out: 16 bytes, src: 32 bytes, a: word, b: word)
    requires no_overlap(out, src)
    ensures out = bytes_of(vec_test(words(src), a, b))
    trace depends on nothing
{
    let x: u32x4 := src.u32x4(0)
    let y: u32x4 := src.u32x4(16)
    let s1: u32x4 := x >> 10
    let s2: u32x4 := (x << 3) | (x >> 29)
    let hi: u32x4 := unpackhi64(x, y)
    let rot: u32x4 := shuf32(x, 0x39)
    let sp0: u32x4 := shuf32(y, 0x00)
    let rt: u32x4 := u32x4(a, b, 0x12345678, 0x9ABCDEF0)
    let spc: u32x4 := u32x4.splat(0x6A09E667)
    let spr: u32x4 := u32x4.splat(a)
    out.u32x4(0) := s1 ^ s2 ^ hi ^ rot ^ sp0 ^ rt ^ spc ^ spr
}
"""
        for arch in ("x86_64", "arm64"):
            _pack_and_dual_verify(src, "vec_ops", arch, check_v2=False)

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
        self.assertTrue(mentioned, "expected at least one u32x4.* mention in ode_hl.py")
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


if __name__ == "__main__":
    unittest.main()
