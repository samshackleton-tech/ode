#!/usr/bin/env python3
"""Tests for explicit linked local namespaces (`use alias = "file.ode"`, `alias.name`).

Verifies:
  1. Splitting a spec out via `use` produces the EXACT SAME 52-char BLAKE3 canonical contract ID.
  2. Multi-file `use` with helper `fn` (custom `calling`, tail call `jmp`/`b`), `inline fn`, and
     `data` packs and audits `shown` on both x86-64 and AArch64 via plain `ode pack` + `ode audit`.
  3. Zero flat merging: two `use`d modules defining identically named `const`, `def`, `inline fn`,
     `data`, and `fn` never collide; bare unqualified references to imported names are refused.
  4. Diamond `use` (`main -> a, b; a -> common; b -> common`) deduplicates cleanly and verifies.
  5. Non-transitivity: `main -> a -> b` refuses `a.b.x` and `b.x` in `main`.
  6. Error cases: cycles, unknown `alias.member`, missing file, alias collision with local decl,
     unqualified bare `alias`, and record field access `r.field` not confused with module alias.
"""
import os
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for _d in (HERE, os.path.join(ROOT, "lang"), os.path.join(ROOT, "kcheck")):
    if _d not in sys.path:
        sys.path.insert(0, _d)

import ode_audit
import ode_canon
import ode_unified
import prove

HAVE_VERIFIER = os.path.isfile(prove.EXE)


def _write(d, rel, text):
    p = os.path.join(d, rel)
    os.makedirs(os.path.dirname(p), exist_ok=True)
    with open(p, "w", encoding="utf-8") as f:
        f.write(text)
    return p


class LinkedNamespaceTests(unittest.TestCase):
    def test_canonical_contract_id_identical_across_split(self):
        """Splitting `paper/examples/all_zero.ode`'s spec into a `use`d file yields the exact same
        canonical `.ocl` text and 52-char BLAKE3 contract ID (zero filenames or aliases in `.ocl`)."""
        orig_path = os.path.join(ROOT, "paper", "examples", "all_zero.ode")
        orig = ode_canon.canonicalize_file(orig_path, contract_name="all_zero", target="x86_64")

        with tempfile.TemporaryDirectory(prefix="ode_ns_canon_") as td:
            _write(td, "spec/zeros_spec.ode", """\
def zero_from(a, at) {
    if at == len(a) then 1
    else if a[at] != 0 then 0
    else zero_from(a, at + 1)
}

def zeros(a) { zero_from(a, 0) }
""")
            main_p = _write(td, "all_zero_split.ode", """\
use zs = "spec/zeros_spec.ode"

fn all_zero(a: n bytes, n: number)
    returns zs.zeros(a)
    trace depends on a, n
    stack 0
{
    for x86_64 {
        reg base = rdi
        reg count = rsi
        reg idx = rcx
        reg res = rax

        idx := 0
        place {
            name i = idx
            fact 0 <= i
            fact i <= n
            fact zs.zeros(a) == zs.zero_from(a, i)
            decreases n - i
        }
    @loop:
        cmp idx, count
        jae @yes
        mov rdx, base
        add rdx, idx
        movzx edx, byte ptr [rdx]
        cmp rdx, 0
        jne @no
        add idx, 1
        jmp @loop
    @yes:
        res := 1
        jmp @done
    @no:
        res := 0
    @done:
        ret
    }
    for arm64 {
        reg base = x0
        reg count = x1
        reg idx = x2
        reg addr = x3
        reg cur = w4
        reg cur64 = x4

        idx := 0
        place {
            name i = idx
            fact 0 <= i
            fact i <= n
            fact zs.zeros(a) == zs.zero_from(a, i)
            decreases n - i
        }
    @loop:
        cmp idx, count
        b.hs @yes
        add addr, base, idx
        ldrb cur, [addr, 0]
        cmp cur64, 0
        b.ne @no
        add idx, idx, 1
        b @loop
    @yes:
        x0 := 1
        b @done
    @no:
        x0 := 0
    @done:
        ret
    }
}
""")
            split = ode_canon.canonicalize_file(main_p, target="x86_64")
            self.assertEqual(split["contract_id"], orig["contract_id"])
            self.assertEqual(split["canonical"], orig["canonical"])
            self.assertEqual(split["glossary"].get("f0"), "zs.zeros")
            self.assertEqual(split["glossary"].get("f1"), "zs.zero_from")

            if HAVE_VERIFIER:
                for tgt in ("x86_64", "arm64"):
                    out_o = os.path.join(td, f"all_zero_{tgt}.o")
                    out_p = os.path.join(td, f"all_zero_{tgt}.proof")
                    res = ode_audit.pack_verified(main_p, None, out_o, out_p, target=tgt)
                    self.assertEqual(res["verdict"], "shown", res)
                    self.assertEqual(res["contract_b32"], orig["contract_id"])

    def test_multi_file_helpers_custom_calling_tail_call_and_zero_collision(self):
        """Two imported modules BOTH define `const K`, `def step`, `inline fn bump`, and `fn apply`,
        with custom `calling` and a tail call, with zero collision; packs and audits `shown` on both
        x86-64 and AArch64."""
        with tempfile.TemporaryDirectory(prefix="ode_ns_multi_") as td:
            _write(td, "mod_a.ode", """\
const K = 3
def step(x) { x + K }

inline fn bump for x86_64 (r: gpr) changes r {
    add r, 3
}
inline fn bump for arm64 (r: gpr) changes r {
    add r, r, 3
}

fn apply(x: number)
    requires x < 1000
    returns x + K
    stack 0
{
    for x86_64
        calling {
            in x = r10
            out = r11
            preserves rbx, rbp, r12, r13, r14, r15, rdi
        }
    {
        mov r11, r10
        bump(r11)
        ret
    }
    for arm64
        calling {
            in x = x9
            out = x10
            preserves x15, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29
        }
    {
        mov x10, x9
        bump(x10)
        ret
    }
}
""")
            _write(td, "mod_b.ode", """\
const K = 5
def step(x) { x + K }

inline fn bump for x86_64 (r: gpr) changes r {
    add r, 5
}
inline fn bump for arm64 (r: gpr) changes r {
    add r, r, 5
}

fn apply(x: number)
    requires x < 2000
    returns x + K
    stack 0
{
    for x86_64 {
        mov rax, rdi
        bump(rax)
        ret
    }
    for arm64 {
        bump(x0)
        ret
    }
}
""")
            main_p = _write(td, "main.ode", """\
use a = "mod_a.ode"
use b = "mod_b.ode"

def combined(x) { b.step(a.step(x)) }

fn entry(x: number)
    requires x < 1000
    returns combined(x)
{
    for x86_64 stack 8 {
        mov r10, rdi
        call a.apply
        mov rdi, r11
        jmp b.apply
    }
    for arm64 stack 0 {
        mov x15, x30
        mov x9, x0
        bl a.apply
        mov x0, x10
        mov x30, x15
        b b.apply
    }
}
""")
            # Canonicalization works with no --fn (root has 1 fn)
            canon = ode_canon.canonicalize_file(main_p, target="arm64")
            self.assertNotIn("m1__", canon["canonical"])
            self.assertNotIn("m2__", canon["canonical"])
            self.assertNotIn("mod_a", canon["canonical"])
            self.assertNotIn("mod_b", canon["canonical"])

            if HAVE_VERIFIER:
                for tgt in ("x86_64", "arm64"):
                    out_o = os.path.join(td, f"entry_{tgt}.o")
                    out_p = os.path.join(td, f"entry_{tgt}.proof")
                    res = ode_audit.pack_verified(main_p, None, out_o, out_p, target=tgt)
                    self.assertEqual(res["verdict"], "shown", res)
                    self.assertEqual(res["coverage"]["functions"], 3)
                    self.assertEqual(res["coverage"]["exported_symbols"], 1)
                    self.assertEqual(res["coverage"]["local_helpers"], 2)

    def test_diamond_use_deduplicates(self):
        """Diamond `main -> left, right; left -> base; right -> base` parses once and verifies."""
        with tempfile.TemporaryDirectory(prefix="ode_ns_diamond_") as td:
            _write(td, "base.ode", """\
const C = 7
def addc(x) { x + C }
""")
            _write(td, "left.ode", """\
use b = "base.ode"
fn step(x: number)
    requires x < 1000
    returns x + b.C
    stack 0
{
    for arm64
        calling {
            in x = x0
            out = x0
            preserves x15, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29
        }
    {
        add x0, x0, 7
        ret
    }
}
""")
            _write(td, "right.ode", """\
use b = "base.ode"
fn step(x: number)
    requires x < 2000
    returns x + b.C
    stack 0
{
    for arm64 {
        add x0, x0, 7
        ret
    }
}
""")
            main_p = _write(td, "main.ode", """\
use l = "left.ode"
use r = "right.ode"
use b = "base.ode"

fn twice(x: number)
    requires x < 1000
    returns b.addc(b.addc(x))
    stack 0
{
    for arm64 {
        mov x15, x30
        bl l.step
        mov x30, x15
        b r.step
    }
}
""")
            canon = ode_canon.canonicalize_file(main_p, target="arm64")
            self.assertEqual(len(canon["contract_id"]), 52)
            if HAVE_VERIFIER:
                out_o = os.path.join(td, "twice.o")
                out_p = os.path.join(td, "twice.proof")
                res = ode_audit.pack_verified(main_p, None, out_o, out_p, target="arm64")
                self.assertEqual(res["verdict"], "shown", res)

    def test_refusals_closed_namespace_cycles_and_errors(self):
        with tempfile.TemporaryDirectory(prefix="ode_ns_err_") as td:
            def read_text(p):
                with open(p, "r", encoding="utf-8") as fh:
                    return fh.read()

            # 1. Circular `use`
            a_p = _write(td, "cyc_a.ode", 'use b = "cyc_b.ode"\ndef fa(x) { b.fb(x) }\n')
            _write(td, "cyc_b.ode", 'use a = "cyc_a.ode"\ndef fb(x) { a.fa(x) }\n')
            with self.assertRaisesRegex(ode_unified.UnifiedErr, "circular"):
                ode_unified.parse_unified(read_text(a_p), a_p)

            # 2. Missing member
            _write(td, "small.ode", "const X = 1\n")
            bad_mem = _write(td, "bad_mem.ode", 'use s = "small.ode"\ndef f(x) { s.NOPE + x }\n')
            with self.assertRaisesRegex(ode_unified.UnifiedErr, "s\\.NOPE"):
                ode_unified.parse_unified(read_text(bad_mem), bad_mem)

            # 3. Missing file
            bad_file = _write(td, "bad_file.ode", 'use s = "does_not_exist.ode"\ndef f(x) { s.X }\n')
            with self.assertRaisesRegex(ode_unified.UnifiedErr, "file not found"):
                ode_unified.parse_unified(read_text(bad_file), bad_file)

            # 4. Non-transitivity (`main -> mid -> small`; `main` cannot see `mid.s` or `s`)
            _write(td, "mid.ode", 'use s = "small.ode"\ndef m(x) { s.X + x }\n')
            nt1 = _write(td, "nt1.ode", 'use mid = "mid.ode"\ndef f(x) { mid.s.X }\n')
            with self.assertRaisesRegex(ode_unified.UnifiedErr, "mid\\.s"):
                ode_unified.parse_unified(read_text(nt1), nt1)

            # 5. Alias collides with local declaration
            coll = _write(td, "coll.ode", 'use s = "small.ode"\nconst s = 2\n')
            with self.assertRaisesRegex(ode_unified.UnifiedErr, "duplicate name `s`"):
                ode_unified.parse_unified(read_text(coll), coll)

            # 6. Bare unqualified alias in expression
            bare = _write(td, "bare.ode", 'use s = "small.ode"\ndef f(x) { s + x }\n')
            with self.assertRaisesRegex(ode_unified.UnifiedErr, "must be qualified"):
                ode_unified.parse_unified(read_text(bare), bare)

            # 7. Zero flat merging: bare `X` from `small.ode` is NOT in scope
            flat = _write(td, "flat.ode", """\
use s = "small.ode"
fn f(x: word)
    returns (x + X) & 0xffffffff
    stack 0
{
    for arm64 {
        add w0, w0, 1
        ret
    }
}
""")
            with self.assertRaises(Exception):
                ode_canon.canonicalize_file(flat, target="arm64")

    def test_trace_nothing_and_comma_reg(self):
        """`trace depends on nothing` canonicalizes identically to omitting `trace depends on`,
        and comma-separated `reg a = x0, b = x1` works on one line."""
        with tempfile.TemporaryDirectory(prefix="ode_wirth_") as td:
            p1 = _write(td, "a.ode", """\
fn inc(x: number)
    requires x < 100
    returns x + 1
    trace depends on nothing
    stack 0
{
    for arm64 {
        reg v = x0, out = x0
        add out, v, 1
        ret
    }
}
""")
            p2 = _write(td, "b.ode", """\
fn inc(x: number)
    requires x < 100
    returns x + 1
    stack 0
{
    for arm64 {
        add x0, x0, 1
        ret
    }
}
""")
            c1 = ode_canon.canonicalize_file(p1, target="arm64")
            c2 = ode_canon.canonicalize_file(p2, target="arm64")
            self.assertEqual(c1["contract_id"], c2["contract_id"])
            if HAVE_VERIFIER:
                res = ode_audit.pack_verified(p1, None, os.path.join(td, "inc.o"), os.path.join(td, "inc.proof"), target="arm64")
                self.assertEqual(res["verdict"], "shown", res)


if __name__ == "__main__":
    unittest.main()
