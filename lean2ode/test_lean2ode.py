#!/usr/bin/env python3
"""Tests for `lean2ode`: strict Lean 4 -> OdeSpecL translator/extractor.

Checks:
  1. Real-world DER/X.509 encoding & tag definitions translated + differentially checked vs Lean 4.
  2. BLAKE3 / ChaCha20 32-bit word vector definitions (`Vector.ofFn`, `rotr`, constants) + dependency order.
  3. Subtle semantic fidelity (`Nat.sub` truncation at 0, `UInt8` wraparound, nested `let` hoisting).
  4. End-to-end chain: Lean 4 spec -> `lean2ode` -> Ode machine code (x86-64 multi-ret & AArch64) -> `odeverify` `shown`!
  5. Short-circuiting `&&` / `||` bounds-guard spec verified on x86-64 & AArch64 (`at < len(a) && a[at] == 65`).
  6. 13 strict negative controls that MUST fail loudly with non-zero exit and an exact reason.
"""
import os, shutil, subprocess, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
BIN = os.path.join(HERE, ".lake", "build", "bin", "lean2ode")
sys.path[:0] = [os.path.join(ROOT, "kcheck"), os.path.join(ROOT, "proof-core"), os.path.join(ROOT, "lang")]
import ode, statement, ode_tool


def has_lake():
    return bool(shutil.which("lake") or os.path.exists(os.path.expanduser("~/.elan/bin/lake")))


def lake_env():
    env = dict(os.environ)
    elan = os.path.expanduser("~/.elan/bin")
    if os.path.isdir(elan) and elan not in env.get("PATH", ""):
        env["PATH"] = elan + ":" + env.get("PATH", "")
    return env


def ensure_built():
    if not os.path.exists(BIN):
        subprocess.run(["lake", "build"], cwd=HERE, env=lake_env(), check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def run_lean2ode(lean_code, extra_args):
    with tempfile.TemporaryDirectory(prefix="lean2ode_t_") as td:
        lp = os.path.join(td, "Input.lean")
        with open(lp, "w") as f:
            f.write(lean_code)
        return subprocess.run([BIN, lp] + extra_args, capture_output=True, text=True, env=lake_env())


def run_lean_eval(lean_code, eval_lines):
    with tempfile.TemporaryDirectory(prefix="lean_eval_") as td:
        lp = os.path.join(td, "Eval.lean")
        with open(lp, "w") as f:
            f.write(lean_code + "\n" + eval_lines + "\n")
        r = subprocess.run(["lean", "--run", lp], cwd=HERE, capture_output=True, text=True, env=lake_env())
        assert r.returncode == 0, f"lean --run failed:\n{r.stderr}\n{r.stdout}"
        return [line.strip() for line in r.stdout.strip().splitlines() if line.strip()]


@unittest.skipUnless(has_lake(), "Lean 4 / lake not installed")
class Lean2OdeTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        ensure_built()

    def test_der_x509_differential(self):
        lean_src = """
namespace X509
def beF : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else beF f (n / 256) ++ [n % 256]

def be (n : Nat) : List Nat := beF n n

def encodeLen (n : Nat) : List Nat :=
  if n < 128 then [n] else (128 + (be n).length) :: be n

def tagOk (t : Nat) : Bool := t < 256 && t % 32 != 31
def constructed (t : Nat) : Bool := t / 32 % 2 == 1
end X509
"""
        r = run_lean2ode(lean_src, ["--def", "encodeLen", "--def", "tagOk", "--def", "constructed"])
        self.assertEqual(r.returncode, 0, r.stderr)
        spec_text = r.stdout
        sp = ode.Spec(spec_text)
        dl = statement.definitions(spec_text)
        self.assertEqual(len(dl), 5)
        self.assertLess(spec_text.index("def beF("), spec_text.index("def be("))
        self.assertLess(spec_text.index("def be("), spec_text.index("def encodeLen("))

        nums = [0, 1, 2, 126, 127, 128, 129, 255, 256, 257, 1000, 65535, 65536]
        tags = [0, 1, 4, 30, 31, 32, 48, 63, 127, 128, 255, 256]
        eval_main = "def main : IO Unit := do\n"
        for n in nums:
            eval_main += f"  IO.println (repr (X509.encodeLen {n}))\n"
        for t in tags:
            eval_main += f"  IO.println (toString (X509.tagOk {t}) ++ \" \" ++ toString (X509.constructed {t}))\n"
        lean_out = run_lean_eval(lean_src, eval_main)

        N = ode.Numbers()
        idx = 0
        for n in nums:
            self.assertEqual(str(sp.call(N, "encodeLen", n)), lean_out[idx])
            idx += 1
        for t in tags:
            got_ok = "true" if sp.call(N, "tagOk", t) else "false"
            got_c = "true" if sp.call(N, "constructed", t) else "false"
            self.assertEqual(f"{got_ok} {got_c}", lean_out[idx])
            idx += 1

    def test_blake3_and_chacha_words(self):
        lean_src = """
abbrev Word := UInt32
def PERMUTATION : Vector (Fin 16) 16 :=
  #v[2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]
def PERMUTE (m : Vector Word 16) : Vector Word 16 :=
  Vector.ofFn fun i => m[PERMUTATION[i]]
def rotr (x : Word) (n : Nat) : Word :=
  (x >>> n.toUInt32) ||| (x <<< (32 - n).toUInt32)
def sigma0 (a : Word) : Word :=
  rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
"""
        r = run_lean2ode(lean_src, ["--def", "PERMUTE", "--def", "sigma0"])
        self.assertEqual(r.returncode, 0, r.stderr)
        spec_text = r.stdout
        self.assertLess(spec_text.index("const PERMUTATION"), spec_text.index("def PERMUTE("))
        self.assertLess(spec_text.index("def rotr("), spec_text.index("def sigma0("))
        sp = ode.Spec(spec_text)
        self.assertEqual(len(statement.definitions(spec_text)), 4)

        test_words = [0, 1, 0x6a09e667, 0xdeadbeef, 0xffffffff, 0x12345678]
        eval_main = "def main : IO Unit := do\n"
        for w in test_words:
            eval_main += f"  IO.println (sigma0 ({w} : UInt32)).toNat\n"
        lean_out = run_lean_eval(lean_src, eval_main)
        N = ode.Numbers()
        for w, want in zip(test_words, lean_out):
            self.assertEqual(str(sp.call(N, "sigma0", ode.Word(w)).v), want)

    def test_semantic_edge_cases(self):
        lean_src = """
def subTrunc (a b : Nat) : Nat := a - b
def u8Wrap (a b : UInt8) : UInt8 := (a + b) - (10 : UInt8)
def nestedLet (x : Nat) : Nat :=
  if x < 10 then
    let y := x * 3 + 1
    y + y
  else
    let z := x - 5
    z * 2
"""
        r = run_lean2ode(lean_src, ["--all"])
        self.assertEqual(r.returncode, 0, r.stderr)
        sp = ode.Spec(r.stdout)
        statement.definitions(r.stdout)

        pairs = [(0, 0), (3, 10), (10, 3), (250, 20), (5, 5), (0, 255)]
        xs = [0, 1, 9, 10, 15, 100]
        eval_main = "def main : IO Unit := do\n"
        for a, b in pairs:
            eval_main += f"  IO.println (subTrunc {a} {b})\n"
            eval_main += f"  IO.println (u8Wrap ({a % 256} : UInt8) ({b % 256} : UInt8)).toNat\n"
        for x in xs:
            eval_main += f"  IO.println (nestedLet {x})\n"
        lean_out = run_lean_eval(lean_src, eval_main)
        N = ode.Numbers()
        i = 0
        for a, b in pairs:
            self.assertEqual(str(sp.call(N, "subTrunc", a, b)), lean_out[i]); i += 1
            self.assertEqual(str(sp.call(N, "u8Wrap", a % 256, b % 256)), lean_out[i]); i += 1
        for x in xs:
            self.assertEqual(str(sp.call(N, "nestedLet", x)), lean_out[i]); i += 1

    def test_end_to_end_lean_spec_to_odeverify_and_multiret_and_shortcircuit(self):
        """End-to-end: Lean 4 spec -> lean2ode -> x86-64 (with early rets) & AArch64 -> odeverify `shown`!
        Also tests short-circuiting `&&` bounds guard (`len(a) >= 1 && a[0] == 65`)."""
        lean_src = """
def b64Val (b : Nat) : Nat :=
  if b >= 65 && b <= 90 then b - 65
  else if b >= 97 && b <= 122 then b - 71
  else if b >= 48 && b <= 57 then b + 4
  else if b == 43 then 62
  else if b == 47 then 63
  else 255

def startsWithA (a : ByteArray) : Nat :=
  if a.size >= 1 && (a.get! 0).toNat == 65 then 1 else 0
"""
        r = run_lean2ode(lean_src, ["--def", "b64Val", "--def", "startsWithA"])
        self.assertEqual(r.returncode, 0, r.stderr)
        spec_with_contracts = r.stdout + """
contract ode_b64_val(b: number) {
    requires b < 256
    returns b64Val(b)
    trace depends on b
    stack 0
}

contract ode_starts_a(buf: n bytes, n: number) {
    returns startsWithA(buf)
    trace depends on buf, n
    stack 0
}
"""
        x86_ode = """target x86_64
fn b64_val as "ode_b64_val" {
    cmp rdi, 65
    if uge {
        cmp rdi, 91
        if ult {
            mov rax, rdi
            sub rax, 65
            ret
        }
    }
    cmp rdi, 97
    if uge {
        cmp rdi, 123
        if ult {
            mov rax, rdi
            sub rax, 71
            ret
        }
    }
    cmp rdi, 48
    if uge {
        cmp rdi, 58
        if ult {
            mov rax, rdi
            add rax, 4
            ret
        }
    }
    cmp rdi, 43
    if eq {
        mov rax, 62
        ret
    }
    cmp rdi, 47
    if eq {
        mov rax, 63
        ret
    }
    mov rax, 255
    ret
}

fn starts_a as "ode_starts_a" {
    cmp rsi, 1
    if ult {
        mov rax, 0
        ret
    }
    movzx eax, byte ptr [rdi + 0]
    cmp rax, 65
    if eq {
        mov rax, 1
        ret
    }
    mov rax, 0
    ret
}
"""
        arm_ode = """target arm64
fn b64_val as "ode_b64_val" {
    cmp x0, 65
    if uge {
        cmp x0, 91
        if ult {
            sub x0, x0, 65
            ret
        }
    }
    cmp x0, 97
    if uge {
        cmp x0, 123
        if ult {
            sub x0, x0, 71
            ret
        }
    }
    cmp x0, 48
    if uge {
        cmp x0, 58
        if ult {
            add x0, x0, 4
            ret
        }
    }
    cmp x0, 43
    if eq {
        mov x0, 62
        ret
    }
    cmp x0, 47
    if eq {
        mov x0, 63
        ret
    }
    mov x0, 255
    ret
}

fn starts_a as "ode_starts_a" {
    cmp x1, 1
    if ult {
        mov x0, 0
        ret
    }
    ldrb w2, [x0, 0]
    cmp x2, 65
    if eq {
        mov x0, 1
        ret
    }
    mov x0, 0
    ret
}
"""
        with tempfile.TemporaryDirectory(prefix="lean2ode_e2e_") as td:
            sp_p = os.path.join(td, "e2e.spec")
            with open(sp_p, "w") as f:
                f.write(spec_with_contracts)
            for label, src in (("x86_64", x86_ode), ("arm64", arm_ode)):
                ode_p = os.path.join(td, f"e2e_{label}.ode")
                with open(ode_p, "w") as f:
                    f.write(src)
                res = ode_tool.run_check(ode_p, sp_p)
                self.assertEqual(res["verdict"], "shown", f"{label} failed: {res.get('diagnostic')}")

    def test_negative_controls(self):
        cases = [
            ("sorry", "def bad (x : Nat) : Nat := sorry", ["--def", "bad"], "sorry"),
            ("io", "def bad : IO Unit := pure ()", ["--def", "bad"], "unsupported type"),
            ("id_run_loop", """def bad (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [0:n] do s := s + i
  return s""", ["--def", "bad"], "Id.run"),
            ("string", 'def bad (s : String) : Nat := s.length', ["--def", "bad"], "String"),
            ("float", "def bad (x : Float) : Float := x + x", ["--def", "bad"], "Float"),
            ("inductive", "inductive MyT | a | b\ndef bad (x : MyT) : Nat := match x with | .a => 0 | .b => 1", ["--def", "bad"], "MyT"),
            ("option", "def bad (x : Nat) : Option Nat := some x", ["--def", "bad"], "Option"),
            ("u32_bare_shr", "def bad (x : UInt32) : UInt32 := x >>> (3 : UInt32)", ["--def", "bad"], "rotate-right"),
            ("higher_order", "def bad (f : Nat → Nat) (x : Nat) : Nat := f x", ["--def", "bad"], "unsupported type"),
            ("symbolic_div", "def bad (a b : Nat) : Nat := a / b", ["--def", "bad"], "symbolic division"),
            ("symbolic_pow", "def bad (n : Nat) : Nat := 2 ^ n", ["--def", "bad"], "XOR"),
            ("partial_def", "partial def bad (n : Nat) : Nat := bad (n + 1)", ["--def", "bad"], "partial"),
            ("mutual_rec", """mutual
def ev : Nat → Bool
  | 0 => true
  | n + 1 => od n
def od : Nat → Bool
  | 0 => false
  | n + 1 => ev n
end""", ["--def", "ev"], "mutual recursion"),
        ]
        for name, src, args, expect in cases:
            with self.subTest(control=name):
                r = run_lean2ode(src, args)
                self.assertNotEqual(r.returncode, 0, f"negative control `{name}` unexpectedly succeeded:\n{r.stdout}")
                self.assertIn(expect.lower(), r.stderr.lower(), f"control `{name}` stderr: {r.stderr}")


if __name__ == "__main__":
    unittest.main()
