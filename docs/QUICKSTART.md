# Ode Quickstart

*Companion to `paper/quickstart.pdf` and `paper/ODE.pdf`.*
*(Informally: **O**bject-code **D**irect **E**vidence — or **O**nly **D**eclared **E**ffects.)*

An Ode source file (`.ode`) pairs a short declarative specification with the exact machine instructions you want the processor to execute on x86-64 and AArch64. You control every register, stack slot, branch, and calling convention. A prover searches for a proof behind the scenes; standalone verifiers check the compiled object bytes directly against the contract.

---

## 1. First Program: `all_zero`

See `paper/examples/all_zero.ode` for a complete two-target program:

```ode
def all_zero_from(a, i) {
    if i == len(a) then 1
    else if a[i] != 0 then 0
    else all_zero_from(a, i + 1)
}

def all_zero_spec(a) { all_zero_from(a, 0) }

fn all_zero(a: n bytes, n: number)
    returns all_zero_spec(a)
    trace depends on a, n
    stack 0
{
    for x86_64 {
        reg base = rdi, len_r = rsi, idx = rcx
        idx := 0
        place {
            name i = idx
            fact 0 <= i
            fact i <= n
            fact all_zero_spec(a) == all_zero_from(a, i)
            decreases n - i
        }
    @loop:
        cmp idx, len_r
        jae @yes
        mov rdx, base
        add rdx, idx
        movzx edx, byte ptr [rdx]
        cmp rdx, 0
        jne @no
        add idx, 1
        jmp @loop
    @yes:
        mov rax, 1
        ret
    @no:
        mov rax, 0
        ret
    }
    for arm64 {
        reg base = x0, len_r = x1, idx = x2, addr = x3, cur = x4, curw = w4
        idx := 0
        place {
            name i = idx
            fact 0 <= i
            fact i <= n
            fact all_zero_spec(a) == all_zero_from(a, i)
            decreases n - i
        }
    @loop:
        cmp idx, len_r
        b.hs @yes
        add addr, base, idx
        ldrb curw, [addr, 0]
        cmp cur, 0
        b.ne @no
        add idx, idx, 1
        b @loop
    @yes:
        mov x0, 1
        ret
    @no:
        mov x0, 0
        ret
    }
}
```

Key elements:
- `a: n bytes, n: number`: a buffer of `n` bytes (`0 <= n < 2^64`). Other scalar kinds: `byte` (`< 256`), `word` (`< 2^32`), `cv` (32 bytes / 8 words), `block` (64 bytes / 16 words), or a declared `layout`.
- `returns E` / `ensures buf = E`: return value and written buffers. Any memory not named in `ensures` cannot be modified.
- `stack N`: maximum stack bytes touched below the caller's stack pointer (`stack 0` for leaf functions).
- `reg alias = hw_reg`: readable register aliases (aliases cannot shadow hardware register names such as `v0..v31` on AArch64 or `al..dh` on x86-64).

---

## 2. Checking, Packing, and Auditing

```bash
# Develop one function at a time:
python3 lang/ode_tool.py check paper/examples/all_zero.ode --target arm64

# Emit a release ELF64 .o (with embedded .ode.ocl) + separate .proof bundle:
python3 lang/ode_tool.py pack paper/examples/all_zero.ode --target arm64 \
    --out /tmp/all_zero.o --proof /tmp/all_zero.proof

# Audit an object file and proof bundle against an expected 52-char BLAKE3 contract ID:
python3 lang/ode_tool.py audit /tmp/all_zero.o /tmp/all_zero.proof \
    --expect-contract jbqyjqpese4s4cq35qxlhaevjvzuaqznquqw6mtlaqleluc25ika

# Independent cross-check with the standalone Python verifier:
python3 proof-core/verify2.py arm64/arm64.tab FILE.statement FILE.proof
```

The four exact outcomes:
- `shown` — verified on every path of the compiled object bytes.
- `refused with a proof` — a concrete input witnesses that the machine code violates the contract.
- `no proof found` — no counterexample found, and the prover could not close a path (check `place` facts, bounds, or `trace depends on`).
- `run` — an unverified test or benchmark run.

---

## 3. Loop Invariants (`place`) and Termination

Place a `place { ... }` block immediately before each loop label:

| Directive | Meaning |
|---|---|
| `name x = reg` | Bind loop-varying register `reg` to a fresh symbolic variable `x` at the loop head |
| `fact E` | Linear inequality (`0 <= i`, `i <= n`) or specification equality (`f(a) == g(a, i)`) proved on entry and every back-edge |
| `decreases E` | Whole-number measure proved `>= 0` on entry and strictly smaller on every back-edge |
| `wrote buf[k ..] = E` | Countdown write loop: bytes `k .. len(buf)` already match `E` (`wrote buf[.. k] = E` for count-up loops) |
| `keep r1 r2` | Registers that retain their pre-loop values across the loop |

---

## 4. Linked Local Namespaces (`use`)

Split specifications and implementations across files with explicit local aliases:

```ode
use eq = "hash_eq_ct_spec.ode"

fn ct_bytes_eq(a: n bytes, b: n bytes, n: number)
    returns eq.ct_bytes_eq(a, b)
    trace depends on n
    stack 0
{ ... }
```

Imports are local to the file that writes them (non-transitive), and shared imports are deduplicated so multi-file and single-file programs produce the exact same canonical `.ocl` contract and 52-character BLAKE3 identifier.

---

## 5. Side-Channel Contracts (`trace depends on`)

The **trace** is the sequence of executed instructions and memory addresses. By default, every input is kept out of the trace: branching on an input or using it in a memory address is refused unless named in `trace depends on`:

- `trace depends on nothing` — strictly constant-time in all inputs.
- `trace depends on n` — branches and addresses depend only on length `n`, never on memory bytes (see `proof-core/examples/hasher/hash_eq_ct.ode`).
- `trace depends on a, n` — branches and addresses may depend on both length and bytes (see `paper/examples/all_zero.ode`).

**Specification style for fast proofs:** Write scalar `def` functions in direct tail-recursive form, passing running accumulators as parameters and returning a sentinel value on invalid input. Avoid `let` bindings inside scalar `def` bodies.

---

## 6. Custom Calling Conventions, Tail Calls, and Inline Helpers

Exported functions follow the C ABI (`rdi, rsi, rdx, rcx, r8, r9` on x86-64; `x0..x7` on AArch64). Private helpers may declare a `calling { in ...; out ...; preserves ... }` block (see `paper/examples/quad.ode`) and `stack 0` helpers can be tail-called with `jmp helper` (x86-64) or `b helper` (AArch64). Short repeated instruction sequences can be factored into `inline fn` with `distinct(...)` and `changes ...` clauses.

---

## 7. Core Instruction Quick Reference

Both the compiler and the verifiers read `core/x86.tab` and `arm64/arm64.tab`:

| Operation | x86-64 (`core/x86.tab`) | AArch64 (`arm64/arm64.tab`) |
|---|---|---|
| Move / constant | `mov r, s` / `r := k` | `mov r, s` / `r := k` (`0..65535`) |
| Add / subtract | `add r, s` / `sub r, s` | `add d, a, b` / `sub d, a, b` |
| Shift / mask | `shl r, k` / `shr r, k` / `and r, k` | `lsl d, a, k` / `lsr d, a, k` / `and d, a, b` |
| Byte load / store | `movzx r32, byte ptr [a]` / `mov byte ptr [a], r8` | `ldrb w, [a, off]` / `strb w, [a, off]` |
| 64-bit stack slot | `mov r, qword ptr [rsp + off]` / `push` / `pop` | `ldr r, [sp, off]` / `str r, [sp, off]` |
| Compare | `cmp a, b` | `cmp a, b` |
| Unsigned branches | `je`, `jne`, `jb`, `jae` | `b.eq`, `b.ne`, `b.lo`, `b.hs` |
| Jump / call / tail / ret | `jmp @L`, `call fn`, `jmp fn`, `ret` | `b @L`, `bl fn`, `b fn`, `ret` |

On AArch64, compose constants above 65,535 from two 16-bit halves (`mov r, hi; lsl r, r, 16; mov t, lo; add r, r, t`). Caller-saved scratch registers for `stack 0` functions are `rax, rcx, rdx, rsi, rdi, r8..r11` on x86-64 and `x0..x15` on AArch64.
