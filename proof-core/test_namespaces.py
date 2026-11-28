#!/usr/bin/env python3
"""Tests for content-addressed linked local namespaces (`use alias = "<52-char-blake3-256>"`, `alias.name`).

Verifies:
  1. Splitting a spec out via content-addressed `use` + `--store` produces the EXACT SAME 52-char
     BLAKE3 canonical contract ID.
  2. Multi-file `use` with helper `fn` (custom `calling`, tail call `jmp`/`b`), `inline fn`, and
     reachability pruning of unused imported `fn`s packs and audits `shown` on both x86-64 and AArch64.
  3. Zero flat merging: two `use`d modules defining identically named `const`, `def`, `inline fn`,
     and `fn` never collide; bare unqualified references to imported names are refused.
  4. Diamond `use` (`main -> a, b; a -> common; b -> common`) deduplicates by content digest and verifies.
  5. Direct `<52>.ode` lookup and strict tamper refusal (`integrity mismatch`) if bytes are altered.
  6. Error cases: filename rejected with helpful hash hint, missing digest lists available modules,
     unknown `alias.member`, non-transitivity, alias collision with local decl, bare `alias`,
     and `ode hash` CLI.
"""
import os
import subprocess
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
    return p, ode_unified.module_hash_file(p)


class LinkedNamespaceTests(unittest.TestCase):
    def test_canonical_contract_id_identical_across_split_and_store(self):
        """Splitting `paper/examples/all_zero.ode`'s spec into a `--store` directory via content-addressed
        `use` yields the exact same canonical `.ocl` text and 52-char BLAKE3 contract ID."""
        orig_path = os.path.join(ROOT, "paper", "examples", "all_zero.ode")
        orig = ode_canon.canonicalize_file(orig_path, contract_name="all_zero", target="x86_64")

        with tempfile.TemporaryDirectory(prefix="ode_ns_canon_") as td:
            _, h_spec = _write(td, "spec/zeros_spec.ode", """\
def zero_from(a, at) {
    if at == len(a) then 1
    else if a[at] != 0 then 0
    else zero_from(a, at + 1)
}

def zeros(a) { zero_from(a, 0) }
""")
            spec_store = (os.path.join(td, "spec"),)
            main_p, _ = _write(td, "all_zero_split.ode", f"""\
use zs = "{h_spec}"  // zeros_spec.ode

fn all_zero(a: n bytes, n: number)
    returns zs.zeros(a)
    trace depends on a, n
    stack 0
{{
    for x86_64 {{
        reg base = rdi
        reg count = rsi
        reg idx = rcx
        reg res = rax

        idx := 0
        place {{
            name i = idx
            fact 0 <= i
            fact i <= n
            fact zs.zeros(a) == zs.zero_from(a, i)
            decreases n - i
        }}
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
    }}
    for arm64 {{
        reg base = x0
        reg count = x1
        reg idx = x2
        reg addr = x3
        reg cur = w4
        reg cur64 = x4

        idx := 0
        place {{
            name i = idx
            fact 0 <= i
            fact i <= n
            fact zs.zeros(a) == zs.zero_from(a, i)
            decreases n - i
        }}
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
    }}
}}
""")
            split = ode_canon.canonicalize_file(main_p, target="x86_64", stores=spec_store)
            self.assertEqual(split["contract_id"], orig["contract_id"])
            self.assertEqual(split["canonical"], orig["canonical"])
            self.assertEqual(split["glossary"].get("f0"), "zs.zeros")
            self.assertEqual(split["glossary"].get("f1"), "zs.zero_from")

            if HAVE_VERIFIER:
                for tgt in ("x86_64", "arm64"):
                    out_o = os.path.join(td, f"all_zero_{tgt}.o")
                    out_p = os.path.join(td, f"all_zero_{tgt}.proof")
                    res = ode_audit.pack_verified(main_p, None, out_o, out_p, target=tgt, stores=spec_store)
                    self.assertEqual(res["verdict"], "shown", res)
                    self.assertEqual(res["contract_b32"], orig["contract_id"])

    def test_multi_file_helpers_custom_calling_tail_call_pruning_and_zero_collision(self):
        """Two imported modules BOTH define `const K`, `def step`, `inline fn bump`, and `fn apply`,
        plus an unused `fn dead_helper` (pruned by reachability!), with zero collision; packs and
        audits `shown` on both x86-64 and AArch64."""
        with tempfile.TemporaryDirectory(prefix="ode_ns_multi_") as td:
            _, h_a = _write(td, "mod_a.ode", """\
const K = 3
def step(x) { x + K }

inline fn bump for x86_64 (r: gpr) changes r {
    add r, 3
}
inline fn bump for arm64 (r: gpr) changes r {
    add r, r, 3
}

fn dead_helper(x: number)
    requires x < 500
    returns x + 99
    stack 0
{
    for x86_64 {
        mov rax, rdi
        add rax, 99
        ret
    }
    for arm64 {
        add x0, x0, 99
        ret
    }
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
            _, h_b = _write(td, "mod_b.ode", """\
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
            main_p, _ = _write(td, "main.ode", f"""\
use a = "{h_a}"  // mod_a.ode
use b = "{h_b}"  // mod_b.ode

def combined(x) {{ b.step(a.step(x)) }}

fn entry(x: number)
    requires x < 1000
    returns combined(x)
{{
    for x86_64 stack 8 {{
        mov r10, rdi
        call a.apply
        mov rdi, r11
        jmp b.apply
    }}
    for arm64 stack 0 {{
        mov x15, x30
        mov x9, x0
        bl a.apply
        mov x0, x10
        mov x30, x15
        b b.apply
    }}
}}
""")
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
                    # `dead_helper` in `mod_a.ode` is pruned: only 3 reachable functions (entry + a.apply + b.apply).
                    self.assertEqual(res["coverage"]["functions"], 3)
                    self.assertEqual(res["coverage"]["exported_symbols"], 1)
                    self.assertEqual(res["coverage"]["local_helpers"], 2)

    def test_diamond_use_deduplicates_by_content_digest(self):
        """Diamond `main -> left, right; left -> base; right -> base` deduplicates by BLAKE3-256 digest."""
        with tempfile.TemporaryDirectory(prefix="ode_ns_diamond_") as td:
            _, h_base = _write(td, "base.ode", """\
const C = 7
def addc(x) { x + C }
""")
            _, h_left = _write(td, "left.ode", f"""\
use b = "{h_base}"
fn step(x: number)
    requires x < 1000
    returns x + b.C
    stack 0
{{
    for arm64
        calling {{
            in x = x0
            out = x0
            preserves x15, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29
        }}
    {{
        add x0, x0, 7
        ret
    }}
}}
""")
            _, h_right = _write(td, "right.ode", f"""\
use b = "{h_base}"
fn step(x: number)
    requires x < 2000
    returns x + b.C
    stack 0
{{
    for arm64 {{
        add x0, x0, 7
        ret
    }}
}}
""")
            main_p, _ = _write(td, "main.ode", f"""\
use l = "{h_left}"
use r = "{h_right}"
use b = "{h_base}"

fn twice(x: number)
    requires x < 1000
    returns b.addc(b.addc(x))
    stack 0
{{
    for arm64 {{
        mov x15, x30
        bl l.step
        mov x30, x15
        b r.step
    }}
}}
""")
            canon = ode_canon.canonicalize_file(main_p, target="arm64")
            self.assertEqual(len(canon["contract_id"]), 52)
            if HAVE_VERIFIER:
                out_o = os.path.join(td, "twice.o")
                out_p = os.path.join(td, "twice.proof")
                res = ode_audit.pack_verified(main_p, None, out_o, out_p, target="arm64")
                self.assertEqual(res["verdict"], "shown", res)

    def test_refusals_tamper_filename_missing_and_closed_namespace(self):
        with tempfile.TemporaryDirectory(prefix="ode_ns_err_") as td:
            def read_text(p):
                with open(p, "r", encoding="utf-8") as fh:
                    return fh.read()

            small_p, h_small = _write(td, "small.ode", "const X = 1\n")

            # 1. Filename instead of 52-char BLAKE3-256 digest is refused AND prints exact hash hint.
            bad_path, _ = _write(td, "bad_path.ode", 'use s = "small.ode"\ndef f(x) { s.X }\n')
            with self.assertRaises(ode_unified.UnifiedErr) as cm:
                ode_unified.parse_unified(read_text(bad_path), bad_path)
            self.assertIn("52-char", str(cm.exception))
            self.assertIn(h_small, str(cm.exception))

            # 2. Tampered `<52>.ode` file in store is refused with `integrity mismatch`.
            store_dir = os.path.join(td, "tampered_store")
            _write(store_dir, f"{h_small}.ode", "const X = 999\n")
            use_tampered, _ = _write(td, "sub/use_tampered.ode", f'use s = "{h_small}"\ndef f(x) {{ s.X }}\n')
            with self.assertRaisesRegex(ode_unified.UnifiedErr, "integrity mismatch"):
                ode_unified.parse_unified(read_text(use_tampered), use_tampered, stores=(store_dir,))

            # 3. Missing member
            bad_mem, _ = _write(td, "bad_mem.ode", f'use s = "{h_small}"\ndef f(x) {{ s.NOPE + x }}\n')
            with self.assertRaisesRegex(ode_unified.UnifiedErr, "s\\.NOPE"):
                ode_unified.parse_unified(read_text(bad_mem), bad_mem)

            # 4. Missing digest lists available modules
            missing_h = "a" * 52
            bad_dig, _ = _write(td, "bad_dig.ode", f'use s = "{missing_h}"\ndef f(x) {{ s.X }}\n')
            with self.assertRaises(ode_unified.UnifiedErr) as cm_m:
                ode_unified.parse_unified(read_text(bad_dig), bad_dig)
            self.assertIn("module digest not found", str(cm_m.exception))
            self.assertIn(h_small, str(cm_m.exception))

            # 5. Non-transitivity (`main -> mid -> small`; `main` cannot see `mid.s` or `s`)
            _, h_mid = _write(td, "mid.ode", f'use s = "{h_small}"\ndef m(x) {{ s.X + x }}\n')
            nt1, _ = _write(td, "nt1.ode", f'use mid = "{h_mid}"\ndef f(x) {{ mid.s.X }}\n')
            with self.assertRaisesRegex(ode_unified.UnifiedErr, "mid\\.s"):
                ode_unified.parse_unified(read_text(nt1), nt1)

            # 6. Alias collides with local declaration
            coll, _ = _write(td, "coll.ode", f'use s = "{h_small}"\nconst s = 2\n')
            with self.assertRaisesRegex(ode_unified.UnifiedErr, "duplicate name `s`"):
                ode_unified.parse_unified(read_text(coll), coll)

            # 7. Bare unqualified alias in expression
            bare, _ = _write(td, "bare.ode", f'use s = "{h_small}"\ndef f(x) {{ s + x }}\n')
            with self.assertRaisesRegex(ode_unified.UnifiedErr, "must be qualified"):
                ode_unified.parse_unified(read_text(bare), bare)

            # 8. Zero flat merging: bare `X` from `small.ode` is NOT in scope
            flat, _ = _write(td, "flat.ode", f"""\
use s = "{h_small}"
fn f(x: word)
    returns (x + X) & 0xffffffff
    stack 0
{{
    for arm64 {{
        add w0, w0, 1
        ret
    }}
}}
""")
            with self.assertRaises(Exception):
                ode_canon.canonicalize_file(flat, target="arm64")

            # 9. `ode hash` CLI prints exact `<52>  <path>`
            tool = os.path.join(ROOT, "lang", "ode_tool.py")
            r = subprocess.run([sys.executable, tool, "hash", small_p], capture_output=True, text=True, check=True)
            self.assertEqual(r.stdout.strip(), f"{h_small}  {small_p}")

    def test_trace_nothing_and_comma_reg(self):
        """`trace depends on nothing` canonicalizes identically to omitting `trace depends on`,
        and comma-separated `reg a = x0, b = x1` works on one line."""
        with tempfile.TemporaryDirectory(prefix="ode_wirth_") as td:
            p1, _ = _write(td, "a.ode", """\
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
            p2, _ = _write(td, "b.ode", """\
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
            self.assertEqual(c1["canonical"], c2["canonical"])


if __name__ == "__main__":
    unittest.main()
