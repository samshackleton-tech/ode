# Ode for Security Auditors

So you are auditing a codebase, and it contains Ode code. You have come to the right place.

This guide is a short pocket reference for a busy security auditor. It explains what files you can
safely ignore, what commands to run to verify the compiled binaries yourself, how to read an Ode
contract in five minutes, and the exact checklist of things you still need to check yourself.

> **Status note (November 2026):** Ode is an active research prototype. Every command in this guide
> runs against the current repository, and Section 5 lists every current limitation plainly so nothing
> catches you off guard.

---

## 1. First: What You Can Safely Ignore

When a project ships Ode code, you will usually see four kinds of files. The table below lists each
file type, what it holds, and whether you need to read it during a security audit.

| File | What it holds | Do you need to read it? |
|---|---|---|
| **`.ode`** | Machine-level implementation (instructions, registers, loops, stack frames) | **No — safely ignore.** |
| **`.proof`** | Loop invariants, arithmetic witnesses, and hints produced by the prover | **No — safely ignore.** |
| **`.spec`** | Short declarative specification and function **contract** | **Yes — read this carefully.** |
| **`.o` / binary** | Compiled machine-code bytes that actually run | **Verify with `odeverify` (do not read by eye).** |

**Why you can ignore `.ode` source files and `.proof` files:**
Ode's verifier (`odeverify`) does **not** read `.ode` source code. It checks the **actual compiled
machine-code bytes** directly against the `.spec` contract, using the `.proof` file only as a guide.
You do not rely on the author, the `.ode` compiler, the assembler, or the prover for the binary
satisfying its contract: if any of them introduced a bug or a backdoor into the machine code or the
proof, `odeverify` refuses it.

*(If you also want build reproducibility—confirming that compiling `.ode` produces the exact same
bytes as `.o`—that is a separate optional check, not something your security conclusion relies on.)*

---

## 2. Two Real Contracts in 60 Seconds

Before looking at any rules, read two real contracts that already verify in this repository.

### Example A: A strict UTF-8 byte parser (`factory/verified/utf8_decode_2byte_x86_64.spec`)

```spec
def utf8_cp2(a) {
    if len(a) == 0 then 4294967295
    else if a[0] < 128 then a[0]
    else if a[0] >= 194 && a[0] <= 223 then
        if len(a) >= 2 && a[1] >= 128 && a[1] <= 191 then
            (a[0] - 192) * 64 + (a[1] - 128)
        else 4294967295
    else 4294967295
}

contract ode_utf8_decode_2byte(input: n bytes, n: number) {
    returns utf8_cp2(input)
    trace depends on input, n
    stack 0
}
```

When `odeverify` prints `shown` for this contract on a binary, it proves for **every** valid input
buffer of **every** length `n`:
- The binary returns the exact value `utf8_cp2(input)`—rejecting empty buffers, truncated 2-byte
  sequences, overlong `0xC0`/`0xC1` encodings (CVE-2008-2938), and invalid continuation bytes.
- It reads **only** bytes inside `input[0 .. n]` and writes **no** caller memory at all (zero
  out-of-bounds reads or writes).
- It uses `0` bytes of stack, preserves callee-saved registers, and returns cleanly.
- Its control flow and memory accesses may depend on `input` and `n` (fine for a text parser).

### Example B: Constant-time cryptography (`factory/verified/chacha20_block_arm64.spec`)

```spec
contract ode_chacha20_block(out: 64 bytes, state: 64 bytes) {
    requires no_overlap(out, state)
    ensures out = bytes_of(chacha20_block(words(state)))
    stack 0
}
```

Notice what is **missing** from Example B: **there is no `trace depends on` line.**
In Ode, omitting an input from the `trace depends on` line means the binary's timing trace—every
instruction executed and every memory address read or written—**cannot depend on that input at all**.
So `shown` here proves that `ode_chacha20_block` computes the exact 20-round RFC 8439 ChaCha20 block
in `0` bytes of stack, writes only `out[0 .. 64]`, and runs completely branch-free and
data-independent with respect to the key, nonce, and block counter.

---

## 3. Run the Verifier Yourself

### Step 1: Build the Lean 4 verifier once

From the root of the Ode repository (requires Lean 4 via `elan` / `lake`; no network needed once the
toolchain is installed):

```sh
cd proof-core && lake build odeverify && cd ..
```

This builds `proof-core/.lake/build/bin/odeverify`. You can also ask Lean to re-check the verifier's
own soundness theorems from scratch:

```sh
python3 -m unittest proof-core/test_sound.py
```

`test_sound.py` confirms that the soundness theorems (`Ode.verify_all_sound`, `Ode.verify_all_trace`,
`Ode.verify_all_result`) compile with **zero `sorry`** and depend only on Lean's three standard
axioms (`propext`, `Classical.choice`, `Quot.sound`).

### Step 2: Verify a binary against its contract and proof

The verifier takes three files: the processor instruction table (`core/x86.tab` or
`arm64/arm64.tab`), a `.statement` file binding the binary's decoded bytes to the contract, and the
`.proof` file.

**Verify a shipped statement + proof directly:**

```sh
# Strict UTF-8 2-byte decoder (x86-64 and AArch64):
./proof-core/.lake/build/bin/odeverify core/x86.tab \
    factory/verified/utf8_decode_2byte_x86_64.statement \
    factory/verified/utf8_decode_2byte_x86_64.proof

./proof-core/.lake/build/bin/odeverify arm64/arm64.tab \
    factory/verified/utf8_decode_2byte_arm64.statement \
    factory/verified/utf8_decode_2byte_arm64.proof

# Complete 16-block AVX-512 ChaCha20 kernel (1,090 instructions, 26 B proof, ~42 ms):
./proof-core/.lake/build/bin/odeverify core/x86.tab \
    proof-core/examples/chacha20/blocks16_x86_64.statement \
    proof-core/proofs/ode_chacha20_blocks16.proof
```

**Or rebuild the `.statement` yourself directly from an ELF `.o` object file and `.spec` file** (so
you do not rely on a pre-built `.statement` file):

```sh
python3 proof-core/statement.py YOUR.spec /tmp/check.statement YOUR.o:SYMBOL
./proof-core/.lake/build/bin/odeverify core/x86.tab /tmp/check.statement YOUR.proof
```

*(For full single-threaded BLAKE3—all 14 x86-64 functions or all 7 AArch64 functions in one
`odeverify` run—see `proof-core/test_hashr.py` and `proof-core/test_hashr_arm64.py`.)*

### Step 3: Read the verdict

- **`shown` (exit code `0`):** The decoded machine instructions satisfy every clause of the contract
  on every input that satisfies the `requires` clauses.
- **`refused: ...` (non-zero exit code):** The proof did not establish the contract. Either the
  binary violates the contract or the proof is invalid; either way, **do not accept the binary**.

---

## 4. How to Read an Ode Contract (`.spec` Pocket Reference)

Every Ode contract follows the **closed-world rule**: *anything the contract does not explicitly
allow, the binary is forbidden to do.* A function cannot read memory outside its listed input
buffers, cannot write memory outside its listed output buffers, cannot exceed its stack bound, cannot
execute instructions outside its `needs` CPU features, and cannot let inputs omitted from
`trace depends on` affect branches or memory addresses.

The table below lists every clause you will encounter inside a `contract` block and what it means for
your audit.

| Clause | Meaning for an auditor |
|---|---|
| `arg: n bytes` / `arg: 64 bytes` / `arg: cv` | Memory region passed as a pointer (`cv` = 32 bytes; `block` = 64 bytes). Read-only unless an `ensures` line writes to it. |
| `arg: number` | 64-bit unsigned integer passed in a register. |
| `requires no_overlap(a, b, ...)` | Caller promise: no two listed memory buffers share any byte. **Verify every caller obeys this.** |
| `requires COND` | Caller precondition (for example `requires len == 2 * pairs` or `requires n <= 64`). **Check that it is not contradictory** and that every caller satisfies it. |
| `returns EXPR` | Exact value placed in the return register (`rax` on x86-64, `x0` on AArch64). |
| `ensures out = EXPR` | Exact bytes written to `out` when the function returns. |
| `trace depends on X, Y` | The *only* inputs (or computed expressions like `same(want, tag)`) that branches and memory addresses may depend on. Any input **not** listed here is kept out of the timing trace (constant-time). |
| `result depends on X` | For contracts that return a named result without an explicit formula: restricts which inputs the returned number may depend on. |
| `stack N` (or formula) | Maximum bytes of stack the function (plus any callees) may use. |
| `decreases EXPR` | Non-negative measure that strictly decreases on every recursive call (proves termination). |
| `needs avx` / `needs avx512` / `needs sse41` | Processor instruction sets used by the binary. **Verify the caller checks CPU features before calling.** |

### Quick sanity check on the `.spec` file itself

A contract only proves the binary matches *what the `.spec` text says*. Always check that the `.spec`
definitions match the actual RFC, standard, or security property you care about. You can run any
`.spec` definition directly on concrete test vectors (RFC vectors, CVE regression inputs, edge cases)
using Ode's specification evaluator:

```sh
python3 -c '
import sys; sys.path.insert(0, "kcheck")
import ode
sp = ode.Spec(open("factory/verified/utf8_decode_2byte_x86_64.spec").read())
print("ASCII A ->", sp.call(ode.Numbers(), "utf8_cp2", [0x41]))
print("Overlong / (CVE-2008-2938) ->", sp.call(ode.Numbers(), "utf8_cp2", [0xC0, 0xAF]))
'
```

*(Where a specification was translated from an existing Lean 4 specification using `lean2ode/`, check
`lean2ode/agree/` for machine-checked Lean 4 theorems proving the Ode specification agrees with the
source Lean 4 specification on all inputs.)*

---

## 5. What You Still Must Check Yourself (The Auditor's Checklist)

Passing `odeverify` eliminates whole classes of low-level vulnerabilities (buffer overflows, out-of-bounds
reads, integer/shift bugs inside the verified routine, accidental data-dependent branches or table
lookups, stack overflows, infinite loops). It does **not** eliminate everything outside the boundary.

Check these five items on every audit:

1. **Contract vs. intent:** Read every line of the `.spec` file. Watch for:
   - **Vacuous or too-strict `requires`:** e.g. a precondition that is impossible or stronger than what
     callers guarantee.
   - **Under-specified `ensures`:** e.g. a function that is allowed to return an error code on every
     input, or leaves part of an output buffer without a promised value.
   - **Over-broad `trace depends on`:** e.g. accidentally naming a key or tag in `trace depends on`.
2. **Caller / FFI boundary (Rust, C, or other assembly calling Ode):**
   - Check that the Rust/C `extern "C"` declaration matches the contract's parameter order, sizes,
     and types.
   - Check that every `requires` clause (`no_overlap`, buffer length bounds, alignment, `needs` CPU
     feature gating) is upheld by the caller on every call path.
   - Confirm that **only** the verified entry-point symbol(s) are exported (`.globl` / `STB_GLOBAL`)
     from the object file to the linker, so internal symbols or symbols without proofs cannot be
     linked by mistake.
3. **Linked binary bytes across platforms (important current limitation):**
   - Today `proof-core/statement.py` decodes **ELF `.o`** object files (on both x86-64 and AArch64).
   - If the project builds on macOS (Mach-O) or Windows (COFF) from `.S` assembly (as
     `blake3-servil-core --features ode-verified` does), verify that the assembled `.text` instruction
     bytes linked into the final binary match the bytes verified in the ELF `.o`.
4. **Hardware side channels outside the trace model:**
   - Ode's trace theorem (`Ode.verify_all_trace`) guarantees identical instruction streams and identical
     memory-address sequences across runs that agree on `trace depends on`. It does **not** model
     data-dependent instruction latency on quirky microarchitectures, power/EM leakage, or speculative
     execution (Spectre/Meltdown).
5. **Your reliance set (what a `shown` verdict relies on today):**
   The table below lists every component that a `shown` verdict relies on today, its size, and how it
   is currently checked.

   | Component | Size | How it is checked today |
   |---|---:|---|
   | **Lean 4 verifier (`proof-core/*.lean`)** | 8,673 lines across 8 core files | Formally proved sound in Lean 4 (`Ode.verify_all_sound`, `verify_all_trace`, `verify_all_result`; zero `sorry`, standard axioms only). |
   | **Instruction tables (`core/x86.tab`, `arm64/arm64.tab`)** | 94 x86-64 rows; 54 AArch64 rows | Cross-checked against real x86-64 and Apple M6 hardware (`0` diffs); all `54/54` AArch64 rows formally proved against Google DeepMind's `arm64-semantics` (`arm64/agree/`). |
   | **Statement builder (`proof-core/statement.py`)** | 791 lines of Python | Tested and audited, not yet formally proved. Translates ELF `.o` + `.spec` into `.statement`. |
   | **Lean 4 kernel / runtime** | External | Standard Lean 4 toolchain (independent verifiers for the same `.proof` format are a future goal). |
   | **Current ABI caveat (AArch64 `v8..v15`)** | Tracked in `paper/CALL-CONV-PROPOSAL.md` §5b | `Contract.keeps` checks `x19..x29` on AArch64 today; AAPCS64 callee-saved vector registers `d8..d15` (`v8..v15`) are currently enforced by static and hardware tests (`factory/test_factory_native.py`, `proof-core/test_chacha20.py`) and queued to be added to the Lean model. |

---

## 6. Where to Go Next

- **Full design and reliance-set analysis:** [`DESIGN.md`](../DESIGN.md)
- **What the Lean soundness theorems prove and assume:** [`proof-core/README.md`](../proof-core/README.md)
- **Standalone AArch64 instruction model & Google `arm64-semantics` agreement proofs:** [`arm64/README.md`](../arm64/README.md)
- **Verified catalog of 38+ routines across x86-64 and AArch64:** [`CATALOG.md`](../CATALOG.md)
- **Companion pocket reference for people writing Ode code:** [`docs/ODE-CARD.md`](ODE-CARD.md)
