# High-Level Ode: Minimal Grammar and Deterministic Lowering Specification (Draft)

## 1. Motivation and Reliance Boundary

Across 19 cold-room runs (372 cells, 136 failures), **87.2% of still-open failures (95 of 109 cells)** came from five low-level ceremonies: context-wiping `place` invariants (`W1`), manual pointer/offset wraparound (`W2`), manual `cmov`/`csel` and `sub`-underflow clamping (`W3`), manual ABI `preserves` lists and peeled recursion (`W4`), and opaque SIMD lane errors (`W5`).

High-Level Ode replaces arbitrary unstructured assembly with a **single, small, structured Wirth-style language** that:
1. **Keeps performance transparent and controllable:** every statement lowers 1-to-1 in exact written order to known instructions from `core/x86.tab` and `arm64/arm64.tab`. There is no instruction reordering, no hidden loop rewriting, and no best-effort optimizer.
2. **Leaves Bob's reliance set unchanged:** the High-Level Ode compiler is relied on for nothing. It emits ordinary ELF64 `.o` machine code and a `.proof` file; Bob verifies only the compiled bytes against the `.ocl` contract using `odeverify` (Lean 4) or `verify2.py`.
3. **Supports both exact and wrapping 64-bit arithmetic explicitly:** `+`, `-`, `*` oblige the verifier to prove no overflow or underflow (catching index and length bugs immediately); `+%`, `-%`, `*%` perform hardware modular wraparound mod $2^{64}$ (for hash mixers, modular differences, and speculative arms of `select`).

---

## 2. Types and Arithmetic Rules

The table below lists every value type in High-Level Ode; each row gives the type name, its machine representation, and its arithmetic rule.

| Type | Machine Representation | Arithmetic Rule |
| --- | --- | --- |
| `u64` | 64-bit general register (`rax..r15` / `x0..x28`) | `+`, `-`, `*` checked no-wrap (`0..2^64-1`); `+%`, `-%`, `*%` modular mod $2^{64}$ |
| `u8` | Zero-extended byte (`0..255`) in a 64-bit register | Promotes cleanly to `u64`; narrows on `out[i] := e` (mod 256) |
| `n bytes` / `K bytes` | Read-only or writable byte slice (`base + len < 2^64`) | Bounds-checked indexed loads `a[i]`, `a.u16(i)`, `a.u32(i)`, `a.u64(i)` and stores `out[i] := e` |
| `u32x4` | 128-bit vector (`xmm0..15` / `v0..31`, 4 × 32-bit lanes) | `+`, `-` are always modular mod $2^{32}$ per lane (matching `paddd` / `add.4s`) |
| `u32x16` | 512-bit vector (`zmm16..31` on `x86_64`, 16 × 32-bit lanes) | `+`, `-` are always modular mod $2^{32}$ per lane (matching `vpaddd`) |

---

## 3. Complete Grammar (EBNF)

Specifications (`def`), imports (`use alias = "file.ode"`), and function contracts (`requires`, `ensures`, `returns`, `trace depends on`, `stack`) keep Ode's existing syntax, adding only linear stack bounds `stack C + D * param`.

```ebnf
file      := (use_decl | def_decl | fn_decl)*

fn_decl   := "fn" ident "(" params ")" ["->" type] contract_clause*
             ( block | target_block+ )
target_block := "for" ("x86_64" | "arm64") ["needs" "avx"] block

block     := "{" stmt* "}"

stmt      := "let" ident [":" type] ":=" expr               -- immutable local
           | "var" ident [":" type] ":=" expr               -- mutable local
           | "buf" ident "[" int "]" ["align" int]          -- local stack array
           | lvalue assign_op expr                          -- in-place update or store
           | "if" cond block ["else" (if_stmt | block)]
           | "while" cond loop_clause* block
           | "for" ident "in" expr ".." expr ["step" int] loop_clause* block
           | "for" ident "in" int ".." int "unroll" block   -- compile-time unroll
           | "break" | "continue"
           | "return" [expr]                                -- tail call if `return f(...)`

assign_op := ":=" | "+=" | "-=" | "+%=" | "-%=" | "&=" | "|=" | "^=" | "<<=" | ">>="
lvalue    := ident | ident "[" expr "]" | ident "." ("u32x4" | "u32x16") "(" expr ")"

loop_clause := "maintains" spec_expr
             | "writes" ident "[" ".." spec_expr "]" "=" spec_expr
             | "writes" ident "[" spec_expr ".." "]" "=" spec_expr
             | "decreases" spec_expr

expr      := int | ident
           | ident "[" expr "]"                             -- 1-byte load (`u8`)
           | ident "." ("u16" | "u32" | "u64" | "u32x4" | "u32x16") "(" expr ")"
           | expr binop expr                                -- + - * +% -% *% & | ^ << >>
           | "select" "(" cond "," expr "," expr ")"        -- constant-time cmov / csel
           | ident "(" [expr ("," expr)*] ")"               -- helper call or target intrinsic
           | "(" expr ")"

cond      := expr ("==" | "!=" | "<" | "<=" | ">" | ">=") expr
           | cond "&&" cond | cond "||" cond | "!" cond | "(" cond ")"
```

- **Portable vs. target-specialized functions:** A function with a plain `{ ... }` body compiles identically to both `x86_64` and `arm64`. A function that uses target-specific SIMD or crypto intrinsics (`sha256rnds2`, `sha256h`, `shufi32x4`, `u32x16`) writes `for x86_64 { ... }` and `for arm64 { ... }` using the **exact same structured syntax**.
- **Deleted ceremonies:** No `@label:`, no `jmp`/`b`, no manual `reg` aliases, no `place` blocks, no `keep`, no manual `calling { preserves ... }`, and no manual `push`/`pop` stack juggling.

---

## 4. Transparent Register Assignment and Deterministic 1-to-1 Lowering

### 4.1 Deterministic Register Assignment (Zero Hidden Magic)

1. **Private helper calling conventions are derived automatically:** Exported functions keep System V AMD64 (`rdi..r9`, `rax`) and AAPCS64 (`x0..x7`, `x0`). Private helpers take parameters in caller-saved registers in order (`x86_64`: `rdi, rsi, rdx, rcx, r8, r9, r10, r11`; `arm64`: `x0..x15`), return in `rax`/`x0`, and automatically declare `preserves` equal to every register not written by the helper body.
2. **Lexical variable placement:** Each live `let`/`var` is assigned the lowest free caller-saved register (`x86_64`: `rax, rcx, rdx, rsi, rdi, r8..r11` for scalars; `zmm16..31` or `xmm0..15` for vectors; `arm64`: `x0..x15` for scalars; `v0..v7, v16..v31` for vectors). When live variables exceed caller-saved registers, callee-saved registers are allocated next (`rbx, rbp, r12..r15` / `x19..x28`, `v8..v15`) and pushed/popped deterministically at entry/exit. Only if live variables exceed the physical register file does the compiler spill to an aligned local stack slot (`align 16` for 128-bit, `align 64` for 512-bit).
3. **Full visibility:** `ode advise` prints the exact `var -> register / spill` table alongside the simulated cycles/iteration on the compiled `.o` bytes, so the coder sees every spill immediately and controls it by shortening live ranges.

### 4.2 Exact 1-to-1 Lowering Table

The table below gives the fixed instruction lowering of each High-Level Ode construct on `x86_64` and `arm64`; each cell shows the exact machine instruction(s) emitted in statement order.

| High-Level Ode Construct | `x86_64` Lowering (`core/x86.tab`) | `arm64` Lowering (`arm64/arm64.tab`) |
| --- | --- | --- |
| `a += b`, `a +%= b` | `add ra, rb` (in-place, 0 extra `mov`) | `add ra, ra, rb` |
| `a -= b`, `a -%= b` | `sub ra, rb` | `sub ra, ra, rb` |
| `a &= k`, `a >>= k`, `a <<= k` | `and ra, k`, `shr ra, k`, `shl ra, k` | `and ra, ra, rmask`, `lsr ra, ra, k`, `lsl ra, ra, k` |
| `x := a[i]` / `x := a[i + k]` | `movzx rx32, byte ptr [ra + ri + k]` | `add t, ra, ri; ldrb rxw, [t, k]` (or `ldrb rxw, [ra, ri]` if `k == 0`) |
| `x := a.u32(i)` / `a.u64(i)` | `mov rx32, dword ptr [ra + ri]` / `mov rx, qword ptr [ra + ri]` | `ldr rxw, [ra, ri]` / `ldr rx, [ra, ri]` |
| `out[i] := x` | `mov byte ptr [rout + ri], rxb` | `strb rxw, [rout, ri]` |
| `if a < b { ... }` | `cmp ra, rb` immediately before `jae @else` (macro-fused) | `cmp ra, rb` immediately before `b.hs @else` (macro-fused) |
| `r := select(a < b, t, f)` | eval `t` (`-%` allowed), `cmp ra, rb; cmovb rr, rt` (branchless) | eval `t`, `cmp ra, rb; csel rr, rt, rf, lo` (branchless) |
| `while cond { ... }` / `for i in lo..hi` | adjacent `cmp` + `jcc` header; automatic `place` inheriting outer facts on names not written in the loop (`for` adds `lo <= i <= hi` and `decreases hi - i`) | adjacent `cmp` + `b.cc` header; same automatic `place` inheritance |
| `return helper(args...)` | restore saved regs/stack, `jmp helper` (true tail call) | restore saved regs/stack, `b helper` (true tail call) |
| `v := rotl32(v, k)` | `vprord vz, vz, 32-k` (AVX-512) or `pslld + psrld + por` | `shl + ushr + orr` (exact written order!) |
| `v := bswap32(v)` | `pshufb vx, mask_bswap32` | `rev32 vv.16b, vv.16b` |

### 4.3 Automatic Proof Emission (Zero Context-Wipe Surprises)

- **Loop framing (`W1`):** Before emitting a `while` or `for` header, the compiler computes the lexical write-set of the loop body. Every outer variable and parameter not assigned in the loop is emitted automatically in `keep`, and `prove.py` carries forward every pre-loop linear inequality and specification equality mentioning only names not written in the loop. The coder writes only `maintains` clauses for what changes.
- **Join points (`W3`, `W6`):** After `if/else` diamonds and chains of `select` expressions, the compiler emits acyclic join points automatically when helpful so verification stays linear rather than branching $2^k$ ways.
- **Scoped diagnostics (`W5`, `W6`):** Every emitted instruction carries its High-Level Ode source line; verifier refusals map back to the exact High-Level Ode expression, scope `matching spec condition(s)` strictly to `def`s reachable from the function's contract, and print the exact lane index on SIMD mismatches.

---

## 5. Worked Examples (Same Language, Both Scalar and SIMD)

### Example A: Constant-Time Base64 Decoder (`ct_base64_decode` — 1 portable file, both CPUs)

```ode
use spec = "ct_base64_decode_spec.ode"

fn b64_dec(c: u8) -> u64
    returns spec.b64_dec(c)
    trace depends on nothing
{
    var r: u64 := 0
    r := select(65 <= c && c <= 90,  c -% 1,  r)   // `-%` wraps cleanly if c == 0, discarded by select!
    r := select(97 <= c && c <= 122, c -% 7,  r)
    r := select(48 <= c && c <= 57,  c + 68,  r)
    r := select(c == 43, 126, r)
    r := select(c == 47, 127, r)
    return r
}
```
On `arm64`, line 1 of `b64_dec` lowers deterministically to: `sub x9, x0, 1; cmp x0, 65; csel x10, x9, x1, hs; cmp x0, 90; csel x1, x10, x1, ls` — zero clamping hacks, zero branches, zero register names, and portable to `x86_64`.

### Example B: Recursive ASN.1 DER Parser (`der_valid` — 1 function instead of `seq0..seq3`)

```ode
fn der_seq(buf: n bytes, n: u64, pos: u64, end: u64, depth: u64) -> u64
    requires pos <= end, end <= n, n <= 65536, depth <= 3
    returns spec.der_seq(buf, pos, end, depth)
    trace depends on buf, n, pos, end, depth
    stack 32 + 32 * depth
{
    var p: u64 := pos
    while p < end
        maintains pos <= p, p <= end
        maintains spec.der_seq(buf, pos, end, depth) == spec.der_seq(buf, p, end, depth)
        decreases end - p
    {
        if p + 2 > end { return 0 }
        let tag: u8 := buf[p]
        ...
        if tag == 48 {
            if depth == 0 { return 0 }
            if der_seq(buf, n, p + hlen, p + hlen + vlen, depth - 1) == 0 { return 0 }
        } else {
            if der_prim_ok(buf, n, tag, p + hlen, vlen) == 0 { return 0 }
        }
        p += hlen + vlen
    }
    return 1
}
```
Outer facts (`n <= 65536`, `end <= n`, `depth <= 3`) are inherited automatically across the `while` loop; linear `stack 32 + 32 * depth` lets `der_seq` call itself directly without peeling `seq0..seq3`.

### Example C: 4-Way AVX-512 ChaCha20 Quarter-Round (exact coder schedule preserved)

```ode
for x86_64 needs avx {
    // Each line lowers 1-to-1 to vpaddd / vpxord / vprord in exact written order:
    for r in 0..10 unroll {
        a0 +%= b0; d0 := rotl32(d0 ^ a0, 16); c0 +%= d0; b0 := rotl32(b0 ^ c0, 12)
        a0 +%= b0; d0 := rotl32(d0 ^ a0,  8); c0 +%= d0; b0 := rotl32(b0 ^ c0,  7)
        ...
        a0 := shufi32x4(a0, 0x39); c0 := shufi32x4(c0, 0x4E); d0 := shufi32x4(d0, 0x93)
    }
}
```

---

## 6. Small Verifier Additions Needed in `Core.lean` and `verify2.py`

All 11 top-level soundness theorems in `proof-core/test_sound.py` stay unchanged. High-Level Ode relies on five small, orthogonal verifier additions (~110 lines of Lean 4 total):

1. **Buffer bound `base + n < 2^64`** (`Contract.lean`, ~5 lines) — allows one-past-the-end pointers (`base + n`).
2. **Modular `+%` / `-%` rule on `add` / `sub`** (`Core.lean`, ~35 lines) — when no-wrap is not proved, records `if a >= b then a - b else a + 2^64 - b` (recovering exact `a - b` whenever guarded by `a >= b` in `select` or `if`).
3. **Linear stack bound `stack C + D * param`** (`Core.lean`, `statement.py`, ~15 lines) — exact sibling of existing `stack C + D * bits(param)`.
4. **Indexed `[base + idx]` load/store rows** (`x86.tab`, `arm64.tab`, ~20 lines) — single hardware instruction per `buf[i]`.
5. **SIMD `pshufb` `bswap32`, 16-byte `bytes` loads, periodic SWAR byte masks, and `or64` in `verify2.py`** (~35 lines).

*(For future Brotli/LZ77 decompress and compress tasks, two additional `Core.lean` rules will be needed later: reading back from a written output buffer for back-references `out[dst] := out[dst - dist]`, and variable-length output return contracts `ensures out[0..ret] = ...`.)*
