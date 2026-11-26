# Ode Quickstart

*For the full book-style edition, see [`paper/quickstart.pdf`](../paper/quickstart.pdf); for the complete language design and formal semantics, see [`paper/ODE.pdf`](../paper/ODE.pdf).*

When you write performance-critical code in C or assembly, you rely on a compiler or manual review not to introduce an out-of-bounds read, a missed edge case, or a data-dependent branch. An Ode source file (`.ode`) pairs a short mathematical specification with the exact machine instructions you want the processor to execute. You keep full control over registers, branches, and stack layout; a prover searches for a `.proof` file (relied on for nothing), and a standalone verifier checks the compiled object bytes directly against the contract.

---

## 1. A First Program: `all_zero`

Consider a function `all_zero` that tests whether every byte of an `n`-byte buffer is zero: on `[0, 0]` it returns `1`; on `[0, 7]` it returns `0`; on the empty buffer `[]` it returns `1`. A single file (`paper/examples/all_zero.ode`) states the specification (`def`), the contract (`fn`), and both target bodies (`for x86_64` and `for arm64`):

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
    for x86_64 {
        reg base = rdi, count = rsi, idx = rcx, res = rax
        reg addr = rdx, cur = edx, cur64 = rdx

        idx := 0
        place {
            name i = idx
            fact 0 <= i
            fact i <= n
            fact zeros(a) == zero_from(a, i)
            decreases n - i
        }
    @loop:
        cmp idx, count
        jae @yes
        mov addr, base
        add addr, idx
        movzx cur, byte ptr [addr]
        cmp cur64, 0
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
        reg base = x0, count = x1, idx = x2, res = x0
        reg addr = x3, cur = w4, cur64 = x4

        idx := 0
        place {
            name i = idx
            fact 0 <= i
            fact i <= n
            fact zeros(a) == zero_from(a, i)
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
        res := 1
        b @done
    @no:
        res := 0
    @done:
        ret
    }
}
```

How to read it:

- Every `def` is a pure mathematical definition evaluated over exact integers; `fn` binds that specification to executable machine code.
- `a: n bytes` grants read-only access to `n` bytes at `a` (`n` is a `number`, an unsigned 64-bit integer). Because no output buffer is declared, any write to caller memory is refused.
- `returns zeros(a)` obliges the machine code to return the exact value of `zeros(a)`.
- `trace depends on a, n` permits branches and memory addresses to depend on both the length `n` and the bytes of `a` (allowing early exit on the first nonzero byte).
- `stack 0` promises zero local stack workspace beyond the caller's return mechanism.
- Exported functions follow System V AMD64 on x86-64 (`rdi, rsi, rdx, rcx, r8, r9`; return in `rax`) and AAPCS64 on AArch64 (`x0..x7`; return in `x0`).
- Inside each target body, `reg name = r` declares a readable alias (`cur`/`cur64` are the 32-bit/64-bit views of one register so the byte load zero-extends into the 64-bit compare), `r := k` loads a small constant, and `place { ... }` is a proof annotation (never emitted as machine instructions) stating why the loop is sound: on every arrival at `@loop`, all bytes before `idx` have tested zero so checking the suffix from `idx` gives the same answer, and `n - idx` strictly decreases each turn.

---

## 2. Checking, Packing, and Auditing

Run all commands from the repository root (`python3 lang/ode_tool.py ...`, abbreviated `ode ...` in prose):

```sh
# Development: compile, prove, and verify one target
python3 lang/ode_tool.py check paper/examples/all_zero.ode --target arm64

# Release: emit ELF64 object (.o, with embedded .ode.ocl) + separate .proof
python3 lang/ode_tool.py pack paper/examples/all_zero.ode --target arm64 \
  --out /tmp/all_zero.o --proof /tmp/all_zero.proof

# Audit: verify 100% of .text against an independently expected contract ID
python3 lang/ode_tool.py audit /tmp/all_zero.o --proof /tmp/all_zero.proof \
  --expect-contract jbqyjqpese4s4cq35qxlhaevjvzuaqznquqw6mtlaqleluc25ika
```

The auditor obtains `--expect-contract` independently from the published specification or release record—never by copying it from the object file under audit. `ode audit` verifies that 100% of executable bytes in `.text` belong to verified functions, that no external symbol relocations remain unresolved, that the embedded `.ode.ocl` section hashes to the expected 52-character lowercase base-32 BLAKE3 identifier, and that the verifier accepts the `.proof` file for those bytes. An auditor who wants a second check outside the primary Lean verifier can also run the standalone pure-Python verifier `python3 proof-core/verify2.py` on the same proof files.

### The Four Outcomes

| Tool outcome | Meaning | Next action |
|---|---|---|
| **`shown`** | Verified: the verifier checked every path of the compiled bytes against the contract. | Ship the `.o` object file together with its `.proof` file. |
| **`refused with a proof`** | Counterexample: a concrete input demonstrates that the machine code violates the contract. | Fix the code or contract using the printed failing input. |
| **`no proof found`** | Inconclusive: no counterexample was found, and the prover could not close a proof obligation. | Check bounds and `place` facts; fix unintended branches rather than relaxing `trace depends on`. |
| **`run`** | Execution without a proof (concrete test or benchmark, not a verification verdict). | Verify with `ode check` or `ode pack` before shipping. |

---

## 3. Loop Invariants and Join Points (`place`)

The verifier never guesses invariants: state what holds at a loop head or a branch merge point in a `place { ... }` block immediately before its label. Writing loop specifications in direct tail-recursive form (passing running accumulators as parameters) lets the prover close each iteration in a single step.

| Directive in `place { ... }` | Meaning or obligation |
|---|---|
| `name x = reg` | Binds a register `reg` to a symbolic name `x` at the label so `fact` lines can constrain it. |
| `fact E` | Inequality (`0 <= i`, `i <= n`) or specification equality proved on every path reaching the label. |
| `decreases E` | Whole-number measure proved `>= 0` on entry and strictly smaller on every back-edge (proves loop termination). |
| `wrote buf[.. k] = E` | For count-up loops writing `buf`: promises bytes `[0, k)` already match `E`. For count-down loops, write `wrote buf[k ..] = E` for `[k, len(buf))`. |
| `keep r1 r2` | Promises that registers `r1`, `r2` retain their pre-loop values across every iteration. |

**Merging branches without a loop (mid-function join points):** A `place { ... }` block *without* a `decreases` line acts as an acyclic join point. Every incoming branch proves the stated `fact` lines, and the verifier checks the code after the label only once — turning a chain of `k` sequential `if/else` diamonds from `2^k` paths into `2k` linear steps. Join points work both at top level and inside loops; if a path ever returns to a join point without a `decreases` measure, the verifier refuses it.

```ode
        cmp rax, 0
        je @case_zero
        mov r9, 5
        jmp @merged
    @case_zero:
        mov r9, 1
        place {
            name i = rcx
            name dv = r9
            fact i < n
            fact 0 <= dv
            fact dv <= 5
            fact dv == step_v(buf[i])
        }
    @merged:
        add r10, r9
```

---

## 4. Multi-File Namespaces (`use`) and Trace Policies (`trace depends on`)

Unlike `all_zero` (which may stop on the first nonzero byte), a cryptographic tag comparison must not disclose which byte differed first. In Ode, the **trace** of an execution is the sequence of instruction addresses executed and memory addresses accessed. Given fixed starting buffer addresses and lengths, two executions whose inputs agree on everything named in `trace depends on` are proved to follow the exact same instruction and address trace. (Physical effects outside the architectural trace—speculative execution, power draw, and data-dependent instruction latency—are not modeled.)

- Omitting `trace depends on` (or writing `trace depends on nothing`) keeps every input value and every buffer byte out of the trace.
- `trace depends on n` permits branches and memory addresses to depend only on the length `n`, never on any byte in memory.
- `trace depends on a, n` permits dependence on both the length and the bytes of `a`.

To keep a pure specification separate from its implementations, import another `.ode` file under a local alias with `use alias = "file.ode"` and qualify its definitions as `alias.name`. Below is a complete constant-time byte-slice comparison (`proof-core/examples/hasher/hash_eq_ct_spec.ode` + `hash_eq_ct.ode`):

```ode
// hash_eq_ct_spec.ode
def eq_from(a, b, i, diff) {
    if i >= len(a) then 1 - diff
    else eq_from(a, b, i + 1, (diff + ((a[i] + 256 - b[i]) % 256) + 255) / 256)
}

def ct_bytes_eq(a, b) { eq_from(a, b, 0, 0) }
```

```ode
// hash_eq_ct.ode
use eq = "hash_eq_ct_spec.ode"

fn ct_bytes_eq(a: n bytes, b: n bytes, n: number)
    returns eq.ct_bytes_eq(a, b)
    trace depends on n
    stack 0
{
    for arm64 {
        reg pa = x0, pb = x1, len_r = x2, idx = x3, diff = x4, addr = x5
        reg vaw = w6, va = x6, vbw = w7, vb = x7, mask = x8

        idx := 0
        diff := 0
        mask := 255
        place {
            name i = idx
            name d = diff
            fact 0 <= i
            fact i <= n
            fact 0 <= d
            fact d <= 1
            fact eq.ct_bytes_eq(a, b) == eq.eq_from(a, b, i, d)
            decreases n - i
        }
    @loop:
        cmp idx, len_r
        b.hs @done
        add addr, pa, idx
        ldrb vaw, [addr, 0]
        add addr, pb, idx
        ldrb vbw, [addr, 0]
        add va, va, 256
        sub va, va, vb
        and va, va, mask
        add diff, diff, va
        add diff, diff, 255
        lsr diff, diff, 8
        add idx, idx, 1
        b @loop
    @done:
        mov x0, 1
        sub x0, x0, diff
        ret
    }
}
```

In `eq_from`, `diff` stays `0` while all bytes match and becomes `1` once any pair differs (`(a[i] + 256 - b[i]) % 256` is `0` on equal bytes and `1..255` otherwise; integer division by `256` after adding `255` maps `0 -> 0` and any positive sum to `1`). The AArch64 loop executes that exact arithmetic without branching on any byte, so the verifier approves `trace depends on n`.

---

## 5. Custom Calling Conventions and Tail Calls

Exported entry points follow System V AMD64 (`rdi, rsi, rdx, rcx, r8, r9`; return `rax`) on x86-64 and AAPCS64 (`x0..x7`; return `x0`) on AArch64. Between private helper functions inside one program, saving and restoring C-convention registers wastes instructions. A private helper (placed above its caller in the `.ode` file) may declare a `for <target> calling { ... }` block with one clause per line: argument bindings (`in param = reg, ...`), return register (`out = reg`), and preserved registers (`preserves ...`):

```ode
// paper/examples/quad.ode (x86-64 excerpt)
fn step(a: number, b: number)
    requires a < 1000000
    requires b < 1000000
    returns a + b + 3
    trace depends on nothing
    stack 0
{
    for x86_64 calling {
        in a = r10, b = r11
        out = r9
        preserves rdi, rsi, rdx, rcx, r8, rbx, rbp, r12, r13, r14, r15
    } {
        mov r9, r10
        add r9, r11
        add r9, 3
        ret
    }
}

fn quad(x: number, y: number)
    requires x < 100000
    requires y < 100000
    returns quad_fn(x, y)
    trace depends on nothing
{
    for x86_64 stack 8 {
        mov r10, rdi
        mov r11, rsi
        call step
        mov r8, r9
        mov r10, rsi
        mov r11, rdi
        call step
        mov rax, r8
        add rax, r9
        add rax, rdi
        add rax, rsi
        ret
    }
}
```

Here `step` preserves `rdi`, `rsi`, and `r8`, so `quad` calls `step` twice with zero stack spills. Factoring complex multi-way dispatch (such as a bytecode interpreter loop) into small `calling` helpers matching specification sub-definitions also keeps symbolic proof paths additive rather than multiplicative.

A leaf helper with `stack 0` can also be tail-called with `jmp helper` (x86-64) or `b helper` (AArch64) once the caller has restored its own stack frame and callee-saved registers. Repeated short straight-line sequences can be factored into an `inline fn` with explicit `distinct(...)` and `changes` clauses (see `paper/ODE.pdf`, sections 4 and 5).

---

## 6. Core Instruction Reference

Both the compiler and the verifiers read `core/x86.tab` and `arm64/arm64.tab`. Operands: `d, a, b` are 64-bit general registers (`rax..r15` / `x0..x30`); `w` is a 32-bit AArch64 register (`w0..w30`); `r32` is a 32-bit x86-64 register (`eax..r15d`); `breg` is an 8-bit x86-64 byte register (`al, cl, dl, ...`); `k` is an immediate; `off` is a byte offset.

| Operation | x86-64 | AArch64 |
|---|---|---|
| Register move | `mov d, a` | `mov d, a` |
| Constant load (shorthand) | `d := k` | `d := k` (`0..65535`) |
| Add / subtract | `add d, a`, `sub d, a` | `add d, a, b`, `sub d, a, b` |
| Shift / mask | `shl d, k`, `shr d, k`, `and d, k` | `lsl d, a, k`, `lsr d, a, k`, `and d, a, b` |
| Byte load / store | `movzx r32, byte ptr [a]`, `mov byte ptr [a], breg` | `ldrb w, [a, off]`, `strb w, [a, off]` |
| 64-bit stack slot | `mov d, qword ptr [rsp + off]`, `mov qword ptr [rsp + off], a` | `ldr d, [sp, off]`, `str a, [sp, off]` |
| Stack push / pop | `push a`, `pop d` | `sub sp, sp, 16`, `add sp, sp, 16` |
| Compare | `cmp a, b` | `cmp a, b` |
| Equality branches | `je @L`, `jne @L` | `b.eq @L`, `b.ne @L` |
| Unsigned order branches | `jb`, `jbe`, `ja`, `jae` | `b.lo`, `b.ls`, `b.hi`, `b.hs` |
| Jump / call | `jmp @L`, `call fn` | `b @L`, `bl fn` |
| Tail call / return | `jmp fn`, `ret` | `b fn`, `ret` |

**Target notes:**
- Register aliases (`reg idx = rcx`) cannot shadow hardware register names (such as `v0..v31` on AArch64 or `al..dl` on x86-64).
- On AArch64, constants from `65,536` up to `2^32 - 1` are built from two 16-bit halves (`d := hi; lsl d, d, 16; t := lo; add d, d, t`).
- Leaf functions (those making no calls) with `stack 0` keep all state in caller-saved registers (`rax, rcx, rdx, rsi, rdi, r8..r11` on x86-64; `x0..x15` on AArch64).

---

## 7. Static Performance Analysis (`ode advise`)

Without executing the binary, `ode advise` runs a calibrated static out-of-order pipeline simulation over every loop and reports cycles per iteration, bytes loaded per iteration (`cyc/B`), the active bottleneck (`frontend`, `dependency`, or execution ports), source-line critical-path chains when dependency-limited, instruction-cache line alignment, and microarchitectural hints (broken macro-op fusion, non-eliminated self-moves, and Apple Silicon NEON pipe saturation):

```sh
# Static cross-CPU report (no execution; runs in a few milliseconds)
python3 lang/ode_tool.py advise paper/examples/all_zero.ode --target x86_64 --all-archs
```

Use `--arch NAME` to focus on one microarchitecture (`zen5`, `zen4`, `zen3`, `icelake` on x86-64; `apple_m`, `ampere1` on AArch64), or declare explicit compile-time budgets inside a target body (`budget { max_bytes N; max_icache_lines N; max_loop_cycles C }`) so regressions fail immediately.

Common levers that show up directly in `ode advise` reports:
- **Throughput per byte (`cyc/B`):** unrolling a hot byte or word loop `4x` or `8x` by computing `addr = base + idx` once per iteration and loading via base-plus-immediate offsets (`[addr + 0]`, `[addr + 1]`, ... or `[addr, 0]`, `[addr, 1]`, ...) cuts address-generation overhead and fills the CPU's load pipes (`3` on Apple M-series, `4` on Zen 5, `2` on AmpereOne).
- **Independent accumulators:** splitting one loop-carried sum into `2`–`4` independent accumulator registers breaks serial dependency chains (and on Apple M-series NEON, keeping at least `12` independent vector chains reaches `4.0` ops/cycle instead of `3.0`).
- **Branch macro-op fusion:** keeping `cmp` immediately before its conditional jump (`jb`/`jae`/`je`/`jne` on x86-64; `b.lo`/`b.hs`/`b.eq`/`b.ne` on AArch64) fuses them into a single uop.

---

## 8. Release and Audit Checklist

1. **Contract:** Every `def` terminates; `requires` states every buffer bound and non-overlap precondition (`no_overlap`); `trace depends on` names only inputs that branches and memory addresses are permitted to use.
2. **Verify and pack:** `ode check` prints `shown` for every target; `ode pack` produces the `.o` object file and separate `.proof` file.
3. **Independent audit:** `ode audit FILE.o --proof FILE.proof --expect-contract EXPECTED_ID` prints `shown` with 100% coverage of `.text`, where `EXPECTED_ID` comes from the independently audited specification—not from the object file itself.
