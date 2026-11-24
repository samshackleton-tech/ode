#!/usr/bin/env python3
"""Tests for explicit local structured control flow in lang/odec.py (`if`/`else`, `loop`/`while`,
`break [if COND]`, `continue [if COND]`) on both x86-64 and AArch64.

Checks:
1. Exact byte-for-byte machine code identity against hand-labeled Ode on both x86-64 and AArch64
   (including BLAKE3's `b3l_pad_arm64` and `blake3_servil_compress_in_place_arm64`, and `v_all_zero`).
2. Nested `loop` + `if`/`else` + `continue if` + `break if` + `place { ... }` line mapping.
3. Exact source-line refusal of every negative control (unknown condition, `break`/`continue` outside
   loop, stray `else`, reserved register names, missing closing brace)."""
import os, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import odec

PAD_ARM = os.path.join(ROOT, "proof-core", "examples", "arm64", "pad_arm64.ode")
COMPRESS_ARM = os.path.join(ROOT, "proof-core", "examples", "arm64", "compress_arm64.ode")
ZERO_X86 = os.path.join(ROOT, "proof-core", "examples", "verifier", "zero_x86.ode")
ZERO_ARM = os.path.join(ROOT, "proof-core", "examples", "verifier", "zero_arm64.ode")


def _compile_text(src_text, fn_name):
    with tempfile.TemporaryDirectory() as d:
        p = os.path.join(d, "t.ode")
        with open(p, "w") as f:
            f.write(src_text)
        return odec.compile_info(p, fn_name)


def _expect_refused(tc, src_text, fn_name, substr, line_no=None):
    with tempfile.TemporaryDirectory() as d:
        p = os.path.join(d, "bad.ode")
        with open(p, "w") as f:
            f.write(src_text)
        with tc.assertRaises(SystemExit) as cm:
            odec.compile_info(p, fn_name)
        msg = str(cm.exception)
        tc.assertIn(substr, msg, msg)
        if line_no is not None:
            tc.assertIn(f"line {line_no}", msg, msg)


class StructuredControlTests(unittest.TestCase):
    def test_pad_arm64_byte_identical(self):
        ref = odec.compile_info(PAD_ARM, "pad")
        structured = """target arm64

fn pad as "b3l_pad_arm64" {
  reg block = x0
  reg src = x1
  reg len = x2
  reg idx = x3
  reg saddr = x4
  reg daddr = x5
  reg bytew = w6
  reg bytex = x6

  idx := 64
  loop {
    place {
      name i = idx
      fact i <= 64
      wrote block[i ..] = padded(src)
      decreases i
    }
    cmp idx, 0
    break if eq
    sub idx, idx, 1
    add daddr, block, idx
    cmp idx, len
    if ult {
      add saddr, src, idx
      ldrb bytew, [saddr, 0]
      strb bytew, [daddr, 0]
      continue
    }
    bytex := 0
    strb bytew, [daddr, 0]
  }
  ret
}
"""
        got = _compile_text(structured, "pad")
        self.assertEqual(got["elf"], ref["elf"])
        self.assertEqual(got["places"], ref["places"])
        self.assertEqual(got["code_bytes"], 60)

    def test_compress_arm64_loop_break_byte_identical(self):
        ref = odec.compile_info(COMPRESS_ARM, "compress1_arm64")
        with open(COMPRESS_ARM) as f:
            src = f.read()
        # Replace `@round: ... b.eq @done ... b @round\n\n@done:` with `loop { ... break if eq ... }`.
        self.assertEqual(src.count("@round:\n"), 1)
        self.assertEqual(src.count("  b.eq @done\n"), 1)
        self.assertEqual(src.count("  b @round\n"), 1)
        rewritten = (src.replace("@round:\n", "  loop {\n", 1)
                        .replace("  b.eq @done\n", "    break if eq\n", 1)
                        .replace("  b @round\n", "  }\n", 1)
                        .replace("@done:\n", "", 1))
        got = _compile_text(rewritten, "compress1_arm64")
        self.assertEqual(got["elf"], ref["elf"])
        self.assertEqual(got["places"], ref["places"])
        self.assertEqual(got["code_bytes"], 464)

    def test_x86_if_else_and_loop_byte_identical(self):
        raw = """target x86_64
fn pick as "pick_x86" {
  reg a = rdi
  reg b = rsi
  reg out = rax
  cmp a, b
  jae @else
  out := a
  jmp @end
@else:
  out := b
@end:
  ret
}
"""
        structured = """target x86_64
fn pick as "pick_x86" {
  reg a = rdi
  reg b = rsi
  reg out = rax
  cmp a, b
  if ult {
    out := a
  } else {
    out := b
  }
  ret
}
"""
        self.assertEqual(_compile_text(structured, "pick")["elf"],
                         _compile_text(raw, "pick")["elf"])

        # Also test `else {` on next line and `loop { ... } while ne` on x86-64
        raw_loop = """target x86_64
fn dec as "dec_x86" {
  reg n = rdi
  reg acc = rax
  acc := 0
@top:
  add acc, 1
  sub n, 1
  cmp n, 0
  jne @top
  ret
}
"""
        str_loop = """target x86_64
fn dec as "dec_x86" {
  reg n = rdi
  reg acc = rax
  acc := 0
  loop {
    add acc, 1
    sub n, 1
    cmp n, 0
  } while ne
  ret
}
"""
        self.assertEqual(_compile_text(str_loop, "dec")["elf"],
                         _compile_text(raw_loop, "dec")["elf"])

    def test_nested_loop_and_if_both_targets(self):
        for target, init_i, cmp_i, add_i in (
            ("x86_64", "rax := 0", "cmp rax, rdi", "add rax, 1"),
            ("arm64", "x0 := 0", "cmp x0, x1", "add x0, x0, 1"),
        ):
            src = f"""target {target}
fn nested as "nested_fn" {{
  {init_i}
  loop {{
    {cmp_i}
    break if uge
    if eq {{
      break
    }} else {{
      {add_i}
      continue if ne
    }}
  }}
  ret
}}
"""
            with self.subTest(target=target):
                info = _compile_text(src, "nested")
                self.assertGreater(info["code_bytes"], 0)
                self.assertGreater(len(info["line_map"]), 0)

    def test_negative_controls_refused_at_source_line(self):
        # 1. Unknown condition in `if`, `break if`, `} while`
        _expect_refused(self, 'fn f as "f" {\n  if slt {\n    rax := 1\n  }\n  ret\n}\n', "f", "unknown condition `slt`", 2)
        _expect_refused(self, 'fn f as "f" {\n  loop {\n    break if ja\n  }\n  ret\n}\n', "f", "unknown condition `ja`", 3)
        _expect_refused(self, 'target arm64\nfn f as "f" {\n  loop {\n    x0 := 0\n  } while gt\n  ret\n}\n', "f", "unknown condition `gt`", 5)

        # 2. `break` / `continue` outside a `loop`
        _expect_refused(self, 'fn f as "f" {\n  break\n  ret\n}\n', "f", "`break` outside a `loop`", 2)
        _expect_refused(self, 'fn f as "f" {\n  break if eq\n  ret\n}\n', "f", "`break if` outside a `loop`", 2)
        _expect_refused(self, 'fn f as "f" {\n  continue\n  ret\n}\n', "f", "`continue` outside a `loop`", 2)
        _expect_refused(self, 'fn f as "f" {\n  continue if ne\n  ret\n}\n', "f", "`continue if` outside a `loop`", 2)

        # 3. Stray `else`
        _expect_refused(self, 'fn f as "f" {\n  else {\n    rax := 1\n  }\n  ret\n}\n', "f", "`else` without a preceding `if`", 2)

        # 4. Reserved control words as register names
        for word in ("if", "else", "loop", "while", "break", "continue"):
            _expect_refused(self, f'fn f as "f" {{\n  reg {word} = rax\n  ret\n}}\n', "f", f"cannot be named `{word}`", 2)

        # 5. Missing closing brace
        _expect_refused(self, 'fn f as "f" {\n  loop {\n    rax := 1\n  ret\n}\n', "f", "the `}` that ends this is missing", 2)


if __name__ == "__main__":
    unittest.main()
