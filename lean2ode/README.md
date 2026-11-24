# `lean2ode` — Strict Lean 4 to Ode Specification Translator

`lean2ode` translates pure functional definitions written in Lean 4 into Ode's specification language
(OdeSpecL). It uses Lean 4's own elaborator and kernel equation lemmas (`getEqnsFor?`), never regular
expressions or text guessing. Whenever a Lean 4 definition uses a type, operator, monad, or pattern
outside the exact fragment that maps directly and reliably to OdeSpecL, `lean2ode` fails immediately
with a non-zero exit code naming the definition and the unsupported construct.

`lean2ode` is completely separate from Bob's verifier (`proof-core`). An auditor who reads the
emitted `.spec` file does not rely on `lean2ode` or Lean's elaborator for verification soundness.

## Concrete example

Given a Lean 4 file `Der.lean` containing definitions from an X.509 DER specification:

```lean
def beF : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else beF f (n / 256) ++ [n % 256]

def be (n : Nat) : List Nat := beF n n

def encodeLen (n : Nat) : List Nat :=
  if n < 128 then [n] else (128 + (be n).length) :: be n
```

Running:

```sh
cd lean2ode && lake build
./.lake/build/bin/lean2ode Der.lean --def encodeLen
```

automatically collects `beF` and `be` in dependency order and prints:

```ode
def beF(n, x) {
    if n == 0 then []
    else (if (x == 0) then [] else (beF((n - 1), (x / 256)) ++ [(x % 256)]))
}

def be(n) {
    beF(n, n)
}

def encodeLen(n) {
    (if (n < 128) then [n] else ([(128 + len(be(n)))] ++ be(n)))
}
```

## Supported fragment and strict refusals

Each row below describes one class of Lean 4 construct, how `lean2ode` translates it into OdeSpecL,
and when `lean2ode` refuses instead of guessing.

| Lean 4 construct | OdeSpecL output | Refusal rule (fails loudly) |
|---|---|---|
| `Nat`, `UInt8`, `Fin n` | Numbers (`UInt8` arithmetic wraps `% 256`) | Any other numeric type (`Float`, `Int`, `UInt64` wrapping add) |
| `Nat.sub a b` | `(if a >= b then a - b else 0)` | Never emitted as bare `a - b` without literal proof `a >= b` |
| `Nat.div`, `Nat.mod` | `(a / d)`, `(a % d)` for nonzero literal `d` | Refused on symbolic divisor (Lean defines `x / 0 = 0`) |
| `UInt32` `+`, `^`, `|`, `&` | 32-bit word `+`, `^`, `|`, `&` | Bare `UInt32 >>> k` refused (Lean shift vs OdeSpecL rotate) |
| `(x >>> k) ||| (x <<< (32 - k))` | `(x >>> k)` (exact 32-bit rotate right) | Refused unless shift counts are exact 32-bit complements |
| `Bool`, `if`/`else`, `&&`, `||` | `if ... then ... else ...`, `&&`, `||` | Dependent `dite` whose branches inspect the proof witness |
| `List`, `Array`, `ByteArray`, `Vector` | `[...]`, `len(a)`, `a[i]`, `a ++ b`, `[e for i in 0..N]` | Non-literal `Vector` / `ofFn` length; nested sequences |
| `let` bindings | Top-level `let`; nested `let` lifted to helper `def` | `let` inside `ofFn` comprehension or `Nat` pattern branch |
| 2-case `Nat` recursion (`0`, `n + 1`) | `if n == 0 then ... else ...` | Multi-column, 3+-branch, or custom-inductive pattern match |
| Local helper calls & self-recursion | Dependency-ordered `const` / `def` | Mutual recursion, `partial`, `unsafe`, `axiom`, `sorry` |
| Monads / algebraic types | *(not supported)* | Always refused (`IO`, `Id.run`, `for`/`while`, `Option`, `Except`, `String`, custom `inductive`/`structure`, higher-order functions, symbolic `^`) |

## Building and running the tests

```sh
cd lean2ode && lake build
python3 test_lean2ode.py
```

`test_lean2ode.py` checks real DER/X.509 and BLAKE3/ChaCha20 definitions differentially against
`lean --run`, verifies semantic edge cases (`Nat.sub` truncation, `UInt8` wraparound, nested `let`
hoisting), runs an end-to-end verification from a Lean 4 specification through `lean2ode` and
`odeverify` on both x86-64 and AArch64 (`shown`), and verifies that 13 unsupported constructs all
fail loudly.
