#!/usr/bin/env pypy3
"""Verify the ordinary content-addressed `std/` library (`std/vec.ode`, `std/bytes.ode`, `std/int.ode`)
across x86-64 and AArch64 using `use <alias> = "<52-char-b3>"` + `--store std`, dual verification
(`odeverify` + `verify2.py` for scalar targets), and standalone `ode_audit.audit_inlines`.
"""
import os
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for _d in (os.path.join(ROOT, "proof-core"), os.path.join(ROOT, "lang"), os.path.join(ROOT, "core"), os.path.join(ROOT, "kcheck")):
    if _d not in sys.path:
        sys.path.insert(0, _d)

import ode_audit
import ode_unified
import prove
import statement
import verify2

HAVE_VERIFIER = os.path.isfile(prove.EXE)
STORES = (HERE,)


def _pack_and_verify(src, fn_name, target, check_v2=False):
    with tempfile.TemporaryDirectory(prefix="ode_std_") as td:
        src_p = os.path.join(td, "test.ode")
        out_o = os.path.join(td, f"{fn_name}_{target}.o")
        out_p = os.path.join(td, f"{fn_name}_{target}.proof")
        with open(src_p, "w", encoding="utf-8") as f:
            f.write(src)
        res = ode_audit.pack_verified(
            src_p, None, out_o, out_p,
            fn_name=fn_name, target=target, c_abi=True, stores=STORES,
        )
        assert res["verdict"] == "shown", res
        if check_v2:
            with open(out_o, "rb") as f:
                elf = ode_audit.parse_elf64(f.read())
            ocl = elf["by_name"][".ode.ocl"][0]["body"].decode("utf-8")
            sym = res["symbol"]
            bound = ocl.replace("contract (", f"contract {sym}(", 1)
            with open(out_p, "r", encoding="utf-8") as f:
                ptxt = f.read()
            idx = ptxt.find("\nfor ")
            raw_pf = ptxt[idx + 1:] if idx >= 0 else ptxt
            st_p = os.path.join(td, "s.statement")
            pf_p = os.path.join(td, "s.rawproof")
            with open(st_p, "w", encoding="utf-8") as f:
                f.write("\n".join(statement.statement(bound, [(out_o, sym)])) + "\n")
            with open(pf_p, "w", encoding="utf-8") as f:
                f.write(raw_pf)
            tab = os.path.join(ROOT, "core", "x86.tab") if target == "x86_64" else os.path.join(ROOT, "arm64", "arm64.tab")
            verify2.verify_files(tab, st_p, pf_p)
        return res


@unittest.skipUnless(HAVE_VERIFIER, "requires built proof-core odeverify binary")
class TestStdModules(unittest.TestCase):
    def test_01_std_vec_rotr_rotl_pack_const_and_transpose(self):
        h_vec = ode_unified.module_hash_file(os.path.join(HERE, "vec.ode"))
        src = ("""\
use vec = "__H_VEC__"  // std/vec.ode

def vec_spec(ws, c0, c1) {
    let r0 = [ws[i] >>> 16 for i in 0..4]
    let r1 = [r0[i] >>> 25 for i in 0..4]
    let p = [lo(c0), hi(c0), lo(c1), hi(c1)]
    let iv = [word(1779033703), word(3144134277), word(1013904242), word(2773480762)]
    [r1[i] ^ p[i] ^ iv[i] for i in 0..4]
}

fn f_vec_all(out: 16 bytes, src: 16 bytes, c0: counter, c1: counter)
    requires disjoint(out, src, 1)
    ensures out = bytes_of(vec_spec(words(src), c0, c1))
    trace depends on nothing
{
    let v: u32x4 := src.u32x4(0)
    let r0: u32x4 := vec.rotr32(v, 16)
    let r1: u32x4 := vec.rotl32(r0, 7)
    let p: u32x4 := vec.pack_u64x2(c0, c1)
    let iv: u32x4 := vec.const_u32x4(0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A)
    out.u32x4(0) := r1 ^ p ^ iv
}
""").replace("__H_VEC__", h_vec)
        # Confirm arm64 `vec.rotr32(v, 16)` emits 1-instruction `rev32` via compile-time `if k == 16`!
        p_arm = ode_unified.parse_unified(src, src="test_vec.ode", stores=STORES)
        arm_asm = "\n".join(p_arm["fns_by_name"]["f_vec_all"]["impls"]["arm64"]["lines"])
        self.assertIn("rev32 ", arm_asm)
        for arch in ("x86_64", "arm64"):
            _pack_and_verify(src, "f_vec_all", arch, check_v2=False)

        # Also test `vec.transpose_4x4`
        src_tr = ("""\
use vec = "__H_VEC__"  // std/vec.ode

def tr4(ws) {
    [
        ws[0], ws[4], ws[8],  ws[12],
        ws[1], ws[5], ws[9],  ws[13],
        ws[2], ws[6], ws[10], ws[14],
        ws[3], ws[7], ws[11], ws[15]
    ]
}

fn f_transpose(out: 64 bytes, src: 64 bytes)
    requires disjoint(out, src, 1)
    ensures out = bytes_of(tr4(words(src)))
    trace depends on nothing
{
    var r0: u32x4 := src.u32x4(0)
    var r1: u32x4 := src.u32x4(16)
    var r2: u32x4 := src.u32x4(32)
    var r3: u32x4 := src.u32x4(48)
    vec.transpose_4x4(r0, r1, r2, r3)
    out.u32x4(0) := r0
    out.u32x4(16) := r1
    out.u32x4(32) := r2
    out.u32x4(48) := r3
}
""").replace("__H_VEC__", h_vec)
        for arch in ("x86_64", "arm64"):
            _pack_and_verify(src_tr, "f_transpose", arch, check_v2=False)

        # Test `vec.rot_lanes(v, 1|2|3)` + high-pressure 12-live-`u32x4` `vec.transpose_4x4` fitting 14 `xmm` regs!
        src_rot_and_12 = ("""\
use vec = "__H_VEC__"  // std/vec.ode

def rot_spec(ws) {
    let a = [ws[1], ws[2], ws[3], ws[0]]
    let b = [ws[2], ws[3], ws[0], ws[1]]
    let c = [ws[3], ws[0], ws[1], ws[2]]
    [a[i] ^ b[i] ^ c[i] for i in 0..4]
}

fn f_rot_lanes(out: 16 bytes, src: 16 bytes)
    requires disjoint(out, src, 1)
    ensures out = bytes_of(rot_spec(words(src)))
    trace depends on nothing
{
    let v: u32x4 := src.u32x4(0)
    out.u32x4(0) := vec.rot_lanes(v, 1) ^ vec.rot_lanes(v, 2) ^ vec.rot_lanes(v, 3)
}
""").replace("__H_VEC__", h_vec)
        for arch in ("x86_64", "arm64"):
            _pack_and_verify(src_rot_and_12, "f_rot_lanes", arch, check_v2=False)

        # 12 live u32x4 vectors on x86_64 + `vec.transpose_4x4` MUST fit in 14 xmm regs (only 2 temps)!
        src_12_tr = ("""\
use vec = "__H_VEC__"  // std/vec.ode

def sum12_tr(ws) {
    let t0 = [ws[0], ws[4], ws[8], ws[12]]
    let t1 = [ws[1], ws[5], ws[9], ws[13]]
    let t2 = [ws[2], ws[6], ws[10], ws[14]]
    let t3 = [ws[3], ws[7], ws[11], ws[15]]
    let base = [t0[i] ^ t1[i] ^ t2[i] ^ t3[i] for i in 0..4]
    let e0 = [ws[16 + i] ^ ws[20 + i] ^ ws[24 + i] ^ ws[28 + i] for i in 0..4]
    let e1 = [ws[32 + i] ^ ws[36 + i] ^ ws[40 + i] ^ ws[44 + i] for i in 0..4]
    [base[i] ^ e0[i] ^ e1[i] for i in 0..4]
}

fn f_tr_12live(out: 16 bytes, src: 192 bytes)
    requires disjoint(out, src, 1)
    ensures out = bytes_of(sum12_tr(words(src)))
    trace depends on nothing
{
    var r0: u32x4 := src.u32x4(0)
    var r1: u32x4 := src.u32x4(16)
    var r2: u32x4 := src.u32x4(32)
    var r3: u32x4 := src.u32x4(48)
    let k0: u32x4 := src.u32x4(64)
    let k1: u32x4 := src.u32x4(80)
    let k2: u32x4 := src.u32x4(96)
    let k3: u32x4 := src.u32x4(112)
    let k4: u32x4 := src.u32x4(128)
    let k5: u32x4 := src.u32x4(144)
    let k6: u32x4 := src.u32x4(160)
    let k7: u32x4 := src.u32x4(176)
    vec.transpose_4x4(r0, r1, r2, r3)
    out.u32x4(0) := (r0 ^ r1 ^ r2 ^ r3) ^ (k0 ^ k1 ^ k2 ^ k3) ^ (k4 ^ k5 ^ k6 ^ k7)
}
""").replace("__H_VEC__", h_vec)
        for arch in ("x86_64", "arm64"):
            _pack_and_verify(src_12_tr, "f_tr_12live", arch, check_v2=False)

        # Also test `for x86_64:avx512` `vec.rotr32` picks single-insn `vprord` when `needs avx512`!
        src_avx512 = ("""\
use vec = "__H_VEC__"  // std/vec.ode

def r12(ws) { [ws[i] >>> 12 for i in 0..4] }

fn f_rotr_avx512(out: 16 bytes, src: 16 bytes)
    requires disjoint(out, src, 1)
    ensures out = bytes_of(r12(words(src)))
    trace depends on nothing
    for x86_64 needs avx512 {
        out.u32x4(0) := vec.rotr32(src.u32x4(0), 12)
    }
""").replace("__H_VEC__", h_vec)
        p_512 = ode_unified.parse_unified(src_avx512, src="test_512.ode", stores=STORES)
        asm_512 = "\n".join(p_512["fns_by_name"]["f_rotr_avx512"]["impls"]["x86_64"]["lines"])
        self.assertIn("vprord ", asm_512)
        _pack_and_verify(src_avx512, "f_rotr_avx512", "x86_64", check_v2=False)

    def test_02_std_bytes_u16_le_and_be(self):
        h_bytes = ode_unified.module_hash_file(os.path.join(HERE, "bytes.ode"))
        src = ("""\
use b = "__H_BYTES__"  // std/bytes.ode

def sum_u16s(buf) {
    (buf[0] + 256 * buf[1]) + (buf[2] * 256 + buf[3])
}

fn f_bytes(buf: n bytes, n: number)
    requires n >= 4
    returns sum_u16s(buf)
    trace depends on n
    stack 0
{
    let lo: u64 := b.load_u16_le(buf, 0)
    let hi: u64 := b.load_u16_be(buf, 2)
    return lo + hi
}
""").replace("__H_BYTES__", h_bytes)
        for arch in ("x86_64", "arm64"):
            _pack_and_verify(src, "f_bytes", arch, check_v2=True)

    def test_03_std_int_mul_const_clamp_and_standalone_audit(self):
        int_path = os.path.join(HERE, "int.ode")
        h_int = ode_unified.module_hash_file(int_path)

        # Standalone audit of all contracted non-const `inline fn`s in `std/int.ode` (`min_u64`, `max_u64`, `clamp_u64`)!
        aud = ode_audit.audit_inlines(int_path, stores=STORES)
        by_key = {(r["name"], r["target"]): r["verdict"] for r in aud}
        for nm in ("min_u64", "max_u64", "clamp_u64"):
            for arch in ("x86_64", "arm64"):
                self.assertEqual(by_key.get((nm, arch)), "shown", f"standalone audit failed for {nm} on {arch}: {aud}")

        # Caller using `int.mul_const` + `int.clamp_u64`
        src = ("""\
use it = "__H_INT__"  // std/int.ode

def want(x) {
    it.clamp(25 * x, 100, 1000)
}

fn f_int(x: number)
    requires x < 10000
    returns want(x)
    trace depends on nothing
    stack 0
{
    let m: u64 := it.mul_const(x, 25)
    return it.clamp_u64(m, 100, 1000)
}
""").replace("__H_INT__", h_int)
        for arch in ("x86_64", "arm64"):
            _pack_and_verify(src, "f_int", arch, check_v2=True)

        # Negative control: violating `it.clamp_u64`'s `requires lo <= hi` is refused at call site!
        src_bad = ("""\
use it = "__H_INT__"  // std/int.ode

fn f_bad_clamp(x: number, lo: number, hi: number)
    requires x < 100, lo < 100, hi < 100
    returns it.clamp(x, lo, hi)
    trace depends on nothing
    stack 0
{
    return it.clamp_u64(x, lo, hi)
}
""").replace("__H_INT__", h_int)
        for arch in ("x86_64", "arm64"):
            with self.assertRaises(ode_audit.PackProofError):
                _pack_and_verify(src_bad, "f_bad_clamp", arch, check_v2=False)


if __name__ == "__main__":
    unittest.main()
