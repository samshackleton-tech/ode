# Ode Quickstart

*For the complete High-Level Ode design, see [`paper/HIGH-LEVEL-ODE-SPEC.md`](../paper/HIGH-LEVEL-ODE-SPEC.md); for the core language and formal semantics, see [`paper/ODE.pdf`](../paper/ODE.pdf).*

When you write performance-critical code in C or assembly, you rely on an optimizing compiler or manual review not to introduce an out-of-bounds read, integer overflow, missed edge case, or data-dependent branch. An Ode source file (`.ode`) pairs a short mathematical specification (`def`) with structured, deterministic systems code (`fn`) that lowers 1-to-1 in written statement order to exact machine instructions. A prover searches for a `.proof` file (relied on for nothing), and a standalone verifier checks the compiled ELF object bytes directly against the contract.

---

## 1. A First Program: `all_zero`

Consider a function `all_zero` that tests whether every byte of an `n`-byte buffer is zero: on `[0, 0]` it returns `1`; on `[0, 7]` it returns `0`; on `[]` it returns `1`. One portable `.ode` file defines the specification (`def`), the contract (`fn`), and a single structured body that compiles and verifies for both `x86_64` and `arm64`:

```ode
def zero_from(a, at) {
    if at == len(a) then 1
    else if a[at] != 0 then 0
    else zero_from(a, at + 1)
}

def zeros(a) { zero_from(a, 0) }

fn all_zero(a: n bytes, n: number)
    returns zeros(a)
    trace depends on a, n
    stack 0
{
    for i in 0..n
        maintains zeros(a) == zero_from(a, i)
    {
        if a[i] != 0 { return 0 }
    }
    return 1
}
```

How to read it:

- Every `def` is a pure mathematical definition evaluated over exact integers; `fn` binds that specification to native machine code.
- `a: n bytes` grants read-only access to `n` bytes at `a` (`n` is a `number`, an unsigned 64-bit integer; `u64` is a synonym for `number`, and `u8` adds `0 <= x <= 255`). Without an `out` buffer, any write to caller memory is refused.
- `returns zeros(a)` obliges the compiled machine code to return the exact value of `zeros(a)`.
- `trace depends on a, n` permits branches and memory addresses to depend on both the length `n` and the bytes of `a` (allowing early exit on the first nonzero byte).
- `stack 0` promises zero local stack workspace beyond the caller's return mechanism (when omitted on non-recursive functions, the compiler computes the exact stack budget automatically).
- Inside the body, `for i in 0..n` automatically tracks `0 <= i <= n` and `decreases n - i`, and lowers deterministically to exact machine code on both `x86_64` and `arm64` with zero spills.

---

## 2. Checking, Packing, Auditing, and Instant Assembly Feedback

Run all commands from the repository root (`python3 lang/ode_tool.py ...`, abbreviated `ode ...`):

```sh
# Development: compile, prove, and verify one target
python3 lang/ode_tool.py check paper/examples/all_zero.ode --target arm64

# Instant (< 50 ms) register/spill map, exact lowered assembly, and static pipeline sim
python3 lang/ode_tool.py advise --asm paper/examples/all_zero.ode --target arm64 --all-archs

# Release: emit ELF64 object (.o with embedded .ode.ocl) + separate .proof
# Pass --c-abi when linking against a legacy C or Rust caller
# Optional: --effort fast (quick interactive stop) or --effort deep / --try-harder
python3 lang/ode_tool.py pack paper/examples/all_zero.ode --c-abi --target arm64 \
  --out /tmp/all_zero.o --proof /tmp/all_zero.proof

# Audit: verify 100% of .text against an independently expected contract ID
python3 lang/ode_tool.py audit /tmp/all_zero.o --proof /tmp/all_zero.proof \
  --expect-contract jbqyjqpese4s4cq35qxlhaevjvzuaqznquqw6mtlaqleluc25ika
```

The auditor obtains `--expect-contract` independently from the published specification—never from the object file under audit. `ode audit` verifies that 100% of executable bytes in `.text` belong to verified functions, that no unresolved external relocations exist, that `.ode.ocl` hashes to the expected 52-character lowercase base-32 BLAKE3 identifier, and that the verifier accepts the `.proof` file for those bytes. An auditor can also run the independent pure-Python verifier `python3 proof-core/verify2.py` on the same `.statement` and `.proof` files.

### The Four Outcomes

| Tool outcome | Meaning | Next action |
|---|---|---|
| **`shown`** | Verified: every path of the compiled machine bytes meets the contract. | Ship the `.o` object file together with its `.proof` file. |
| **`refused with a proof`** | Counterexample: a concrete input shows the machine code violates the contract. | Fix the code or contract using the printed failing input. |
| **`no proof found`** | Inconclusive: no counterexample was found, and the prover could not close an obligation. | Strengthen loop `maintains` / `writes` / `join` facts or fix unintended branches. |
| **`run`** | Execution without a proof (concrete test or benchmark, not a verification verdict). | Verify with `ode check` or `ode pack` before shipping. |

---

## 3. Structured Language Summary

High-Level Ode lowers statements in exact written order with lexical block scoping and deterministic register allocation (check the exact variable-to-register mapping and spill count any time in `< 50 ms` via `ode advise --asm`):

| Construct | Syntax | Deterministic lowering & proof semantics |
|---|---|---|
| Immutable / mutable scalar | `let x := expr`, `var i: u64 := 0`, `var b: u8 := 0`, `{ ... }` | Allocates a register (`u8` records `0 <= b <= 255`); lexical `{ ... }` blocks and dead parameters reuse registers immediately. |
| Explicit stack variable | `stack var x: u64 := 0`, `stack let v: u32x4 := expr` | Places the variable in an explicit aligned stack slot instead of a register (avoids register pressure with no hidden spills). |
| Local stack buffer | `buf tmp[64] align 16` | Fixed aligned stack frame slot; no dynamic allocation. |
| Exact arithmetic (default) | `a + b`, `a - b`, `a * b`, `x += k`, `x -= k` | Verifier proves no 64-bit unsigned overflow or underflow. |
| Explicit wrapping mod $2^{64}$ | `a +% b`, `a -% b`, `a *% b`, `x +%= k`, `x -%= k` | Emits hardware wraparound (`wrap` proof marker); enables single-compare unsigned range checks like `(c -% 65) <= 25`. |
| Bitwise & shifts | `a & b`, `a \| b`, `a ^ b`, `a << k`, `a >> k` | Exact bitmask (`& (2^w - 1)`), contiguous bitfields, power-of-two shifts (`<< k` / `>> k`). |
| Branchless select | `select(cond, then_expr, else_expr)` | Lowers directly to `cmov*` (x86-64) / `csel` (AArch64); safe on data kept out of the trace (`trace depends on ...`). |
| Scalar memory loads/stores | `a[i]`, `a.u16(i)`, `a.u32(i)`, `a.u64(i)`, `out[i] := v`, `buf.u64(i) := v` | 1-, 2-, 4-, or 8-byte little-endian loads; 1-byte stores to `out`, 8-byte stores to stack `buf` (pack 32-bit words with `u32x4` and `.u32x4(i) := v`). |
| Branches | `if cond { ... } else if cond2 { ... } else { ... }` | Exact comparisons (`==`, `!=`, `<`, `<=`, `>`, `>=`) and short-circuit `&&`, `\|\|`, `!`. |
| Counted loop | `for i in lo..hi [step k] [maintains ...] [writes ...] { ... }` | Auto-tracks `lo <= i <= hi`, step alignment, `decreases hi - i`, and inherits all invariant dominating outer `if`-guards and `let` equalities automatically. |
| Compile-time unroll | `for i in 0..N [step k] unroll { ... }` | Expands straight-line at compile time with constant folding on `i` (zero loop overhead). |
| General loop | `while cond [maintains ...] [writes ...] decreases E { ... }` | Explicit termination measure `decreases E`; inherits invariant outer facts automatically. |
| Acyclic branch merge | `join maintains fact1, fact2` | Emits a `place` without `decreases` to merge `k` sequential `if/else` diamonds in linear `2k` steps instead of `2^k` paths. |
| Calls & tail calls | `let r := helper(a, b)`, `return helper(a, b)` | Plain `fn` uses Ode's fast calling convention (auto-derived exact `preserves` across local and `use`-imported files); `return helper(...)` lowers to a verified tail jump (`jmp`/`b`). |

**Output-buffer loop invariants (`writes`):** For a function with an output buffer `out: N bytes` and `ensures out = E`, state on the loop what prefix has already been written:
- Count-up loop: `writes out[.. j] = spec_expr[i]` (promises `out[0 .. j)` matches the specification on entry to each iteration).
- Count-down loop: `writes out[j ..] = spec_expr[i]`.

---

## 4. Multi-File Namespaces (`use`) and Trace Policies (`trace depends on`)

In Ode, the **trace** of an execution is the sequence of instruction addresses executed and memory addresses accessed. Given fixed buffer addresses and lengths, two executions whose inputs agree on everything listed in `trace depends on` are proved to follow the exact same instruction and address trace. (Physical effects outside the architectural trace—speculative execution, power draw, and variable instruction latency—are not modeled.)

- Omitting `trace depends on` (or writing `trace depends on nothing`) keeps every input value and every buffer byte out of the trace.
- `trace depends on n` permits branches and memory addresses to depend only on `n`, never on any byte in memory.
- `trace depends on a, n` permits dependence on both `n` and the bytes of `a`.

Import another `.ode` file under a closed local alias using its 52-character lowercase base-32 BLAKE3-256 digest (`ode hash eq_spec.ode`) and refer to its definitions or functions as `alias.name`. Below is a complete constant-time byte-slice comparison using `select` so no branch ever depends on input bytes:

```ode
// eq_spec.ode
def eq_from(a, b, i, diff) {
    if i >= len(a) then 1 - diff
    else eq_from(a, b, i + 1, if a[i] != b[i] then 1 else diff)
}
def ct_bytes_eq(a, b) { eq_from(a, b, 0, 0) }
```

```ode
// eq.ode  (run `ode hash eq_spec.ode` to obtain the 52-character digest)
use eq = "<52-char-blake3-256-of-eq_spec.ode>"

fn ct_bytes_eq(a: n bytes, b: n bytes, n: number)
    returns eq.ct_bytes_eq(a, b)
    trace depends on n
    stack 0
{
    var diff: u64 := 0
    for i in 0..n
        maintains 0 <= diff, diff <= 1
        maintains eq.ct_bytes_eq(a, b) == eq.eq_from(a, b, i, diff)
    {
        let va := a[i]
        let vb := b[i]
        diff := select(va != vb, 1, diff)
    }
    return 1 - diff
}
```

Because `select(va != vb, 1, diff)` lowers directly to `cmp` + `cmovne` (x86-64) or `cmp` + `csel` (AArch64) with zero conditional jumps on `va` or `vb`, the verifier approves `trace depends on n` on both architectures.

---

## 5. Helper Functions, Recursion, and Calling Conventions

Every plain `fn` in `.ode` stays free of C-ABI boilerplate. When one Ode function calls another (in the same file or across `use`-imported files, with callees defined before callers), the compiler automatically derives the callee's exact `preserves` set so caller registers stay live across the call with minimal or zero stack spills. Only the exported boundary packed with `ode pack --c-abi` follows System V AMD64 (`rdi..r9`, return `rax`) / AAPCS64 (`x0..x7`, return `x0`).

**Direct self-recursion:** A recursive function declares a `decreases arg` clause (where `arg` is a parameter listed in `trace depends on`) and a linear stack budget `stack C + D * arg` (for example `stack 64 + 64 * depth` for frame size `<= 64` bytes per recursive level) or logarithmic `stack C + D * bits(arg)`:

```ode
fn rec_all_zero(a: n bytes, n: u64, d: u64) -> u64
    requires d <= n, n <= 65536
    returns zero_prefix(a, d)
    decreases d
    trace depends on a, n, d
    stack 32 + 32 * d
{
    if d == 0 { return 1 }
    if a[d - 1] != 0 { return 0 }
    return rec_all_zero(a, n, d - 1)
}
```

---

## 6. Target Blocks and Typed SIMD (`u32x4`, `u32x16`)

Portable functions use a single `{ ... }` body. When you want architecture-specific vector widths, CPU feature gates (`needs avx`, `needs avx512`), or manual instruction tuning, write target blocks `for x86_64 [needs ...] { ... }` and `for arm64 { ... }`:

| SIMD Operation | Syntax (`u32x4` on both arches; `u32x16` on `x86_64 needs avx needs avx512`) | Lowering (`x86_64` / `arm64`) |
|---|---|---|
| Unaligned vector load | `let v: u32x4 := inp.u32x4(off)` / `inp.u32x16(off)` | `vmovdqu` / `vmovdqu32` (`x86_64`); `ldr qN, [base, off]` (`arm64`) |
| Unaligned vector store | `out.u32x4(off) := v` / `out.u32x16(off) := v` | `vmovdqu` / `vmovdqu32` (`x86_64`); `str qN, [base, off]` (`arm64`) |
| Vector scalar load / broadcast | `u64_to_vec(x)`, `const_u32x4(data_label)` (`x86_64`), `broadcast_u32x16(w)` (`x86_64`) | `vmovq` / `fmov dN, r`; `vmovaps [rip + #label]`; `vpbroadcastd` |
| 32-bit lane add / xor / and / or | `a +% b` (or `a +%= b`), `a ^ b`, `a & b`, `a \| b` | `vpaddd`, `vpxord`, `vpand`, `vpor` / `add.4s`, `eor.16b`, `and.16b`, `orr.16b` |
| 32-bit lane shift & 1-insn rotate | `a >> k`, `a << k`, `vprord(a, k)` (`x86_64 needs avx512`), `rev32_16(a)` (`arm64`) | `vpsrld`/`vpslld`, `vprord` (`x86_64`); `ushr.4s`/`shl.4s`, `rev32.8h` (`arm64`) |
| 128-bit lane rotate / align | `ext4(a, b)`, `ext8(a, b)`, `ext12(a, b)` | `vpalignr` (`x86_64`) / `ext.16b` (`arm64`) |
| 32-bit lane shuffle / unpack | `unpacklo32/hi32(a, b)`, `unpacklo64/hi64(a, b)`, `uzp1_32/uzp2_32(a, b)`; `x86_64` only: `shuf32(a, imm)`, `shufps(a, b, imm)`, `blend32(a, b, imm)`, `shufi32x4(a, b, imm)` | `vpunpckldq`/`hdq`/`lqdq`, `vshufps`, `vpshufd`, `vpblendd`, `vshufi32x4` / `zip1.4s`/`zip2.4s`/`zip1.2d`/`zip2.2d`/`uzp1.4s`/`uzp2.4s` (`arm64`) |

On AArch64, `u32x4` uses up to 22 caller-saved NEON registers (`v0..v7, v16..v29`, keeping `v8..v15` preserved with zero stack pushes; declare `stack var` or `stack(arm64) var` for any extra vectors). On x86-64, `u32x4` uses `xmm1..xmm14` and `u32x16` uses `zmm1..zmm30` (emitting `vzeroupper` automatically on exit). Raw assembly from `core/x86.tab` and `arm64/arm64.tab` also remains accepted inside `for x86_64 { ... }` / `for arm64 { ... }` blocks whenever you want full manual register control.

### Zero-Overhead Helpers (`inline fn`) and the Ordinary `std/` Library

To share repeated sequences (round functions, bit-packing steps, target-specialized rotates, constant-multiplier expansions) with zero call overhead and without losing surrounding path facts across a call boundary, define a hygienic `inline fn` with by-value, `var`, or compile-time `const` parameters, optional return type (`-> ty`), optional contract clauses (`requires` checked strictly at every call site via a non-generalizing `check`), and optional per-target `for <target>[:variant]` arms:

```ode
use vec = "7zjhuvtcpskuqp5hojlblzp4sohvyncst5we3ol4ohbhk43ujbxa"  // std/vec.ode

inline fn mix_step(var a: u32x4, var b: u32x4, c: u32x4) {
    a +%= b
    b := vec.rotr32(b ^ a, 8)
    a +%= c
}
```

At each call site `mix_step(v0, v1, m0)`, `var` parameters alias the caller's live variables directly (zero copies, zero stack slots), `const` parameters fold at compile time (eliminating dead `if` branches and unrolling `for ... unroll` loops), value parameters bind fresh hygienic locals, and the expanded code is verified in place alongside the caller.

Ordinary, auditable helper modules live in `std/` and carry zero special compiler privilege — import them by their 52-character BLAKE3-256 digest (`ode hash std/*.ode`) with `--store std`:

| Module | BLAKE3-256 digest (`ode hash`) | Helpers (exact signatures) |
|---|---|---|
| `std/vec.ode` | `7zjhuvtcpskuqp5hojlblzp4sohvyncst5we3ol4ohbhk43ujbxa` | `rotr32(v: u32x4, const k: u64) -> u32x4` (`vprord` on `x86_64:avx512`, `rev32_16` on `arm64` when `k == 16`, shift-or otherwise), `rotl32(v: u32x4, const k: u64) -> u32x4`, `rotr32_x16(v: u32x16, const k: u64) -> u32x16`, `rotl32_x16(v: u32x16, const k: u64) -> u32x16`, `pack_u64x2(lo: u64, hi: u64) -> u32x4`, `const_u32x4(const a, const b, const c, const d) -> u32x4`, `transpose_4x4(var r0, var r1, var r2, var r3)` |
| `std/bytes.ode` | `ozgki74ogmdvuzubstiqnse5xlh2guawnta5dmhrmaqokwp3dfqa` | `load_u16_le(buf, i) -> u64`, `load_u16_be(buf, i) -> u64`, `store_u16_le(out, i, v)`, `store_u16_be(out, i, v)` |
| `std/int.ode` | `raeybpdavam7upiziaktzghulvfgv6er54pcn6xjgiq7uuoc6kvq` | `mul_const(x: u64, const k: u64) -> u64`, `min_u64(a, b) -> u64`, `max_u64(a, b) -> u64`, `clamp_u64(x, lo, hi) -> u64` (`requires lo <= hi`; also exports spec `def min2`, `def max2`, `def clamp`) |

---

## 7. Static Performance Analysis (`ode advise --asm`)

Without executing the binary, `ode advise --asm --all-archs` prints:
1. The exact `variable -> register / [sp+off] (SPILL)` table and stack frame size.
2. Side-by-side High-Level Ode source lines and the exact machine instructions emitted.
3. A calibrated out-of-order pipeline simulation over every loop and straight-line function (`cyc/iter`, `cyc/B`, active bottleneck: `frontend`, `dependency`, or execution ports, critical-path chains, i-cache line alignment, and microarchitectural hints).

Common optimization levers visible in `ode advise --asm`:
- **Eliminate spills and callee-saves:** inspect the `variables:` table; shrinking live ranges or using `unroll` keeps hot state in caller-saved registers (`stack 0 B`, `spills: 0`).
- **Interleave independent chains:** compute 2–4 independent lanes or blocks side by side (e.g., `a0..d0` and `a1..d1`, or 4-way interleaved vectors) to hide multi-cycle ALU/vector latency and fill all execution ports.
- **Widen memory reads/unroll loops:** use `.u32(off)` / `.u64(off)` / `.u32x4(off)` / `.u32x16(off)` and `for k in 0..4 unroll` to reduce loop overhead and saturate load pipes.
- **Keep branchless hot paths:** replace short data-dependent branches with `select(cond, a, b)` and single-compare wrapping checks `(c -% lo) <= hi - lo`.

---

## 8. Release and Audit Checklist

1. **Contract:** Every `def` terminates; `requires` states every buffer bound and `no_overlap`; `trace depends on` names only inputs permitted in branches and addresses.
2. **Verify and pack:** `ode pack FILE.ode --c-abi --target TARGET --out FILE.o --proof FILE.proof` prints `VERDICT: shown`.
3. **Independent audit:** `ode audit FILE.o --proof FILE.proof --expect-contract EXPECTED_ID` prints `shown` with 100% coverage of `.text`, where `EXPECTED_ID` comes from the independently audited specification.
