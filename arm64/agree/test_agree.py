#!/usr/bin/env python3
"""Tests for arm64/agree: static checks always run; Lean checks run when built."""
import os, re, shutil, subprocess, sys, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ARM64 = os.path.dirname(HERE)
ROOT = os.path.dirname(ARM64)
sys.path.insert(0, os.path.join(ROOT, "core"))
sys.path.insert(0, ARM64)
import table, word

THEOREMS = [
    "ArmAgree.agree_add_rrr",
    "ArmAgree.agree_ldr64_sp_fault",
    "ArmAgree.agree_ldr64_sp",
    "ArmAgree.agree_eor_v",
    "ArmAgree.agree_rev32",
    "ArmAgree.agree_ldrb",
    "ArmAgree.agree_cmp_rr",
    "ArmAgree.agree_b_hs",
    "ArmAgree.agree_b_lo",
    "ArmAgree.agree_nop",
    "ArmAgree.agree_mov_ri",
    "ArmAgree.agree_mov32_ri",
    "ArmAgree.agree_mov_rr",
    "ArmAgree.agree_add_rri",
    "ArmAgree.agree_sub_rri",
    "ArmAgree.agree_sub_rrr",
    "ArmAgree.agree_cmp_ri",
    "ArmAgree.agree_b",
    "ArmAgree.agree_b_eq",
    "ArmAgree.agree_b_ne",
    "ArmAgree.agree_strb",
    "ArmAgree.agree_add_sp",
    "ArmAgree.agree_sub_sp",
    "ArmAgree.agree_add_of_sp",
    "ArmAgree.agree_ldr64",
    "ArmAgree.agree_str64",
    "ArmAgree.agree_ldr32",
    "ArmAgree.agree_str32",
    "ArmAgree.agree_str64_sp_fault",
    "ArmAgree.agree_str64_sp",
    "ArmAgree.agree_bl",
    "ArmAgree.agree_ret",
    "ArmAgree.agree_orr_v",
    "ArmAgree.agree_add_4s",
    "ArmAgree.agree_ushr_4s",
    "ArmAgree.agree_shl_4s",
    "ArmAgree.agree_ld1_4s",
    "ArmAgree.agree_st1_4s",
]
ALLOWED_AXIOMS = "[propext, Classical.choice, Quot.sound]"
CHECK_BIN = os.path.join(HERE, ".lake", "build", "bin", "agree-check")


def norm_sexp(text):
    """Compare decoded instructions with integer tokens normalized to decimal."""
    toks = text.strip().lstrip("(").rstrip(")").split()
    out = []
    for t in toks:
        try:
            out.append(str(int(t, 0)))
        except ValueError:
            out.append(t)
    return out


def lake_bin():
    found = shutil.which("lake")
    if found:
        return found
    elan = os.path.expanduser("~/.elan/bin/lake")
    return elan if os.path.exists(elan) else None


class StaticChecks(unittest.TestCase):
    def test_imports_and_no_shortcuts(self):
        with open(os.path.join(HERE, "Agree.lean")) as f:
            text = f.read()
        imports = re.findall(r"^import\s+(\S+)", text, re.M)
        self.assertEqual(
            imports,
            ["Table", "Machine", "Arm64.Trusted.ISA.Decode", "Arm64.Trusted.ISA.Eval"],
        )
        for bad in (r"\bsorry\b", r"\badmit\b", r"^axiom\s", r"maxHeartbeats"):
            self.assertIsNone(re.search(bad, text, re.M), f"found {bad} in Agree.lean")


class BuiltChecks(unittest.TestCase):
    def setUp(self):
        if not os.path.exists(CHECK_BIN):
            self.skipTest("agree-check not built (run `lake build` in arm64/agree/)")

    def test_rows_match_table(self):
        r = subprocess.run(
            [CHECK_BIN, os.path.join(ARM64, "arm64.tab")],
            cwd=HERE,
            capture_output=True,
            text=True,
            check=True,
        )
        self.assertEqual(r.stdout.strip(), "agree-check: all 36 rows match arm64.tab")

    def test_encodings_match_word_py(self):
        r = subprocess.run(
            [CHECK_BIN, "--words", os.path.join(ARM64, "arm64.tab")],
            cwd=HERE,
            capture_output=True,
            text=True,
            check=True,
        )
        lines = [l for l in r.stdout.splitlines() if l.strip()]
        self.assertGreater(len(lines), 100)
        rows = table.read(word.TABLE)
        all_ways = word.ways(rows)
        by_name = {w.row.name: w for w in all_ways}
        seen = set()
        for line in lines:
            row_name, hex_word, sexp = line.split(" ", 2)
            seen.add(row_name)
            raw = int(hex_word, 16).to_bytes(4, "little")
            got = word.decode(all_ways, raw)
            self.assertIsNotNone(got, f"word.decode refused {line}")
            got_row, bind = got
            self.assertEqual(got_row.name, row_name, line)
            self.assertEqual(norm_sexp(word.written(got_row, bind)), norm_sexp(sexp), line)
            self.assertEqual(word.encode(by_name[row_name], bind), raw, line)
        self.assertEqual(seen, {row.name for row in rows})

    def test_axioms(self):
        lake = lake_bin()
        if not lake:
            self.skipTest("lake not installed")
        env = dict(os.environ)
        env["PATH"] = os.path.dirname(lake) + ":" + env.get("PATH", "")
        script = "import Agree\n" + "\n".join(f"#print axioms {t}" for t in THEOREMS) + "\n"
        r = subprocess.run(
            [lake, "env", "lean", "--stdin"],
            cwd=HERE,
            input=script,
            env=env,
            capture_output=True,
            text=True,
            check=True,
        )
        for t in THEOREMS:
            want = f"'{t}' depends on axioms: {ALLOWED_AXIOMS}"
            self.assertIn(want, r.stdout, r.stdout + r.stderr)


if __name__ == "__main__":
    unittest.main()
