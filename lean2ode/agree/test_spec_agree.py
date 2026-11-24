#!/usr/bin/env python3
"""Tests for standalone Lean 4 spec-agreement proofs (`lean2ode/agree/`).

Verifies three independent properties:
1. Static audit: zero `sorry`, `admit`, `axiom`, or `maxHeartbeats` in `SpecAgree.lean`.
2. Lean build & axiom audit: `lake build` succeeds and all 8 theorems depend only on
   `[propext, Classical.choice, Quot.sound]`.
3. Zero-skew check against live `lean2ode`: runs `lean2ode` live on the exact Lean 4 reference
   definitions from `SpecAgree.lean`, lowers them via `proof-core/statement.py`, and confirms that
   the resulting `.statement` S-expressions match the exact `Contract.Def` ASTs proved in
   `SpecAgree.lean`.
"""

import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN2ODE_DIR = os.path.dirname(HERE)
ROOT = os.path.dirname(LEAN2ODE_DIR)
sys.path[:0] = [os.path.join(ROOT, "kcheck"), os.path.join(ROOT, "proof-core")]

import statement

LEAN2ODE_BIN = os.path.join(LEAN2ODE_DIR, ".lake", "build", "bin", "lean2ode")

EXPECTED_THEOREMS = [
    "SpecAgree.agree_der_tagOk",
    "SpecAgree.agree_der_constructed",
    "SpecAgree.agree_der_beF",
    "SpecAgree.agree_der_be",
    "SpecAgree.agree_der_encodeLen",
    "SpecAgree.agree_blake3_rotr",
    "SpecAgree.agree_b64_val",
    "SpecAgree.agree_b64_letter",
]

EXPECTED_STATEMENT_DEFS = [
    "def tagOk t = (ifx (bin < (name t) (num 256)) (bin != (bin % (name t) (num 32)) (num 31)) (bin == (num 0) (num 1)))",
    "def constructed t = (bin == (bin % (bin / (name t) (num 32)) (num 2)) (num 1))",
    "def beF n x = (ifx (bin == (name n) (num 0)) (list) (ifx (bin == (name x) (num 0)) (list) (bin ++ (call beF (bin - (name n) (num 1)) (bin / (name x) (num 256))) (list (bin % (name x) (num 256))))))",
    "def be n = (call beF (name n) (name n))",
    "def encodeLen n = (ifx (bin < (name n) (num 128)) (list (name n)) (bin ++ (list (bin + (num 128) (call len (call be (name n))))) (call be (name n))))",
    "def rotr x n = (bin >>> (name x) (name n))",
    "def b64Val b = (ifx (ifx (bin >= (name b) (num 65)) (bin <= (name b) (num 90)) (bin == (num 0) (num 1))) (bin % (bin - (bin + (name b) (num 256)) (num 65)) (num 256)) (ifx (ifx (bin >= (name b) (num 97)) (bin <= (name b) (num 122)) (bin == (num 0) (num 1))) (bin % (bin - (bin + (name b) (num 256)) (num 71)) (num 256)) (ifx (ifx (bin >= (name b) (num 48)) (bin <= (name b) (num 57)) (bin == (num 0) (num 1))) (bin % (bin + (name b) (num 4)) (num 256)) (ifx (bin == (name b) (num 43)) (num 62) (ifx (bin == (name b) (num 47)) (num 63) (num 255))))))",
    "def b64Letter v = (ifx (bin < (name v) (num 26)) (bin + (num 65) (name v)) (ifx (bin < (name v) (num 52)) (bin + (num 71) (name v)) (ifx (bin < (name v) (num 62)) (ifx (bin >= (name v) (num 4)) (bin - (name v) (num 4)) (num 0)) (ifx (bin == (name v) (num 62)) (num 43) (num 47)))))",
]

REFERENCE_LEAN = """
namespace X509
def beF : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else beF f (n / 256) ++ [n % 256]

def be (n : Nat) : List Nat := beF n n

def encodeLen (n : Nat) : List Nat :=
  if n < 128 then [n] else (128 + (be n).length) :: be n

def tagOk (t : Nat) : Bool := t < 256 && t % 32 != 31
def constructed (t : Nat) : Bool := (t / 32) % 2 == 1
end X509

namespace B3
def rotr (x : UInt32) (n : Nat) : UInt32 :=
  (x >>> n.toUInt32) ||| (x <<< (32 - n).toUInt32)
end B3

namespace B64
def b64Val (b : UInt8) : UInt8 :=
  if b >= 65 && b <= 90 then b - 65
  else if b >= 97 && b <= 122 then b - 71
  else if b >= 48 && b <= 57 then b + 4
  else if b == 43 then 62
  else if b == 47 then 63
  else 255

def b64Letter (v : Nat) : Nat :=
  if v < 26 then 65 + v
  else if v < 52 then 71 + v
  else if v < 62 then v - 4
  else if v == 62 then 43
  else 47
end B64
"""


def lake_env():
    env = dict(os.environ)
    elan = os.path.expanduser("~/.elan/bin")
    if os.path.isdir(elan) and elan not in env.get("PATH", ""):
        env["PATH"] = elan + ":" + env.get("PATH", "")
    return env


def has_lake():
    return shutil.which("lake", path=lake_env().get("PATH", "")) is not None


class StaticChecks(unittest.TestCase):
    def test_no_sorry_or_axioms_in_spec_agree(self):
        with open(os.path.join(HERE, "SpecAgree.lean")) as f:
            src = f.read()
        for pat in (r"\bsorry\b", r"\badmit\b", r"^axiom\s", r"maxHeartbeats", r"bv_decide"):
            self.assertIsNone(re.search(pat, src, re.M), f"forbidden {pat} in SpecAgree.lean")


@unittest.skipUnless(has_lake(), "Lean 4 / lake not installed")
class LeanChecks(unittest.TestCase):
    def test_build_and_standard_axioms_only(self):
        r = subprocess.run(
            ["lake", "build"],
            cwd=HERE, env=lake_env(), capture_output=True, text=True, check=False,
        )
        self.assertEqual(r.returncode, 0, f"lake build failed:\n{r.stdout}\n{r.stderr}")
        # Re-run `lake env lean CheckMain.lean` so `#print axioms` always prints even when cached
        chk = subprocess.run(
            ["lake", "env", "lean", "CheckMain.lean"],
            cwd=HERE, env=lake_env(), capture_output=True, text=True, check=False,
        )
        self.assertEqual(chk.returncode, 0, f"CheckMain failed:\n{chk.stdout}\n{chk.stderr}")
        allowed = {"propext", "Classical.choice", "Quot.sound"}
        for thm in EXPECTED_THEOREMS:
            m = re.search(rf"'{re.escape(thm)}' depends on axioms: \[([^\]]*)\]", chk.stdout)
            self.assertIsNotNone(m, f"missing axiom line for {thm} in:\n{chk.stdout}")
            got = {a.strip() for a in m.group(1).split(",") if a.strip()}
            self.assertTrue(got <= allowed, f"{thm} uses non-standard axioms: {got}")

    def test_live_lean2ode_matches_proved_defs_exactly(self):
        if not os.path.exists(LEAN2ODE_BIN):
            subprocess.run(["lake", "build"], cwd=LEAN2ODE_DIR, env=lake_env(), check=True)
        with tempfile.TemporaryDirectory(prefix="spec_agree_") as td:
            lp = os.path.join(td, "Ref.lean")
            with open(lp, "w") as f:
                f.write(REFERENCE_LEAN)
            r = subprocess.run(
                [
                    LEAN2ODE_BIN, lp,
                    "--def", "X509.tagOk",
                    "--def", "X509.constructed",
                    "--def", "X509.encodeLen",
                    "--def", "B3.rotr",
                    "--def", "B64.b64Val",
                    "--def", "B64.b64Letter",
                ],
                capture_output=True, text=True, env=lake_env(), check=True,
            )
            got_defs = statement.definitions(r.stdout)
            self.assertEqual(got_defs, EXPECTED_STATEMENT_DEFS)


if __name__ == "__main__":
    unittest.main()
