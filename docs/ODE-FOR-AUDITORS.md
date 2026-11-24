# Ode for Security Auditors

> **Documentation-Driven Design note:** This pocket guide describes the minimal auditor workflow
> using `.ocl` (Ode Contract Language) contracts and `ode audit`. [Appendix D](#appendix-d-prototype-status-todays-commands-vs-this-guide)
> maps each step to the exact commands that run in this repository today and notes the pieces still
> on our roadmap.

So you are auditing a codebase, and it contains Ode code. You have come to the right place.

Ode code ships with a complete formal proof that the compiled binary matches a short formal
specification—called a **contract**—written in `.ocl` (Ode Contract Language). Because the verifier
checks the compiled machine-code bytes directly against that contract, you can ignore the `.ode`
source files and `.proof` files, run `ode audit` on the binary, and focus your audit on the
contract.

---

## 1. Start From the Binary

Begin with the compiled binary artifact that will actually run, and run:

```sh
ode audit path/to/binary --proof path/to/binary.proof
```

Each Ode binary carries its canonical `.ocl` contract in a non-executable `.ode.ocl` metadata
section (while the proof lives in a separate `.proof` file, or is regenerated on demand). Running
`ode audit` does four things:

1. Extracts the single canonical `.ocl` contract bound to the binary (and confirms it has no
   comments, unused definitions, or author-chosen names).
2. Verifies the proof directly against the binary's actual machine-code bytes.
3. Confirms that the contract covers 100% of the binary's executable code and exported symbols, with
   no extra code, extra exported symbols, or startup hooks (such as `.init_array`).
4. Prints the full **52-character lowercase base-32 BLAKE3 hashes** (RFC 4648 base-32 without
   padding: letters `a–z` and digits `2–7`) of both the binary and its canonical contract:

```text
BINARY:   utf8_decode_2byte_x86_64.o
  BLAKE3(binary):    wc4msdb3bowibu5e2resxtx7hahku4byjec4isfro737ikjiulda
  BLAKE3(contract):  jsvn5lp6d5igxjd5vq6iz4da5bmtqsfpvp5h3wle27pgrbm2peqa  (embedded .ode.ocl)
  SYMBOL:            ode_jsvn5lp6d5igxjd5vq6iz4da5bmtqsfpvp5h3wle27pgrbm2peqa
  COVERAGE:          100% of executable code (1 function, 24 instructions, 92 B, 1 exported symbol, 0 hooks)
  VERDICT:           shown
```

### Contracts Have No Names

An Ode contract has **no name**; its sole identifier is the 52-character base-32 BLAKE3 hash of its
canonical `.ocl` form. Every exported linker symbol is derived directly from that hash
(`ode_<52-character-hash>`), so swapping in a binary with a different contract fails at link time as
well as during `ode audit`.

When you already know the expected contract hash (for example, from a prior review or registry),
pass it to `--expect-contract` so the tool checks it:

```sh
ode audit path/to/binary --proof path/to/binary.proof \
    --expect-contract jsvn5lp6d5igxjd5vq6iz4da5bmtqsfpvp5h3wle27pgrbm2peqa
```

Standalone `.ocl` files produced by `ode canon --out-dir` are named by their 52-character hash
(`<52-character-hash>.ocl`). Whenever `ode audit --contract` or `ode spec-test` reads a
hash-named `.ocl` file, it hashes the file's contents and refuses if the contents do not match the
filename.

To inspect the exact canonical contract text that was verified—or render it with your own local
glossary of human-readable names—run:

```sh
ode audit --show-contract path/to/binary --proof path/to/binary.proof
ode audit --show-contract --glossary my_names.json path/to/binary --proof path/to/binary.proof
```

You do not need to read any `.ode` source files or `.proof` files. The verifier checks the binary
bytes themselves, so the verdict does not rely on the author, the `.ode` compiler, the assembler, or
the prover.

---

## 2. Read and Test the Contract

A security flaw or backdoor cannot exist in the binary code covered by this contract unless there is
a mistake, a backdoor, or excess looseness in the contract itself.

### A complete canonical contract example

Below is the exact canonical `.ocl` contract whose 52-character base-32 BLAKE3 hash is
`jsvn5lp6d5igxjd5vq6iz4da5bmtqsfpvp5h3wle27pgrbm2peqa`. Every helper and parameter uses a neutral
slot (`f0`, `a0`, `a1`, `p0`); author-chosen names live in an optional glossary file.

```ocl
def f0(p0) {
    if len(p0) == 0 then 4294967295
    else if p0[0] < 128 then p0[0]
    else if p0[0] >= 194 && p0[0] <= 223 then
        if len(p0) >= 2 && p0[1] >= 128 && p0[1] <= 191 then (p0[0] - 192) * 64 + (p0[1] - 128)
        else 4294967295
    else 4294967295
}

contract (a0: a1 bytes, a1: number) {
    returns f0(a0)
    trace depends on a0, a1
    stack 0
}
```

### The Closed-World Rule

Every Ode contract is a **closed world**: anything the contract does not explicitly permit, the
binary is forbidden to do. On the example above, `shown` establishes for every valid input of every
length `a1` that the binary reads only `a0[0 .. a1]`, writes no caller memory, returns `f0(a0)`
(rejecting empty inputs, truncated sequences, and overlong `0xC0`/`0xC1` encodings such as
CVE-2008-2938), uses at most `0` bytes of stack, terminates, and returns cleanly. Both our x86-64
and AArch64 implementations share this exact same 52-character contract hash.

### Contract Clauses at a Glance

The table below lists each clause that can appear inside a `contract` block, what it establishes,
and what to check while reading it.

| Clause | What the verifier proves | What you need to check |
|---|---|---|
| `a0: a1 bytes` / `64 bytes` / `cv` | Memory buffer passed by pointer (`cv` = 32 B, `block` = 64 B); read-only unless written by `ensures`. | Buffer size and layout match what callers pass. |
| `a1: number` | 64-bit unsigned integer argument. | Range and sentinel values match what callers expect. |
| `requires COND` | Assumed true at entry (for example, `no_overlap(a0, a1)`, `a1 <= 64`). | Callers actually satisfy it, and the preconditions are not contradictory. |
| `returns EXPR` | Binary returns `EXPR` on every valid input. | Edge cases (empty, maximum-length, malformed inputs) match the intended behavior. |
| `ensures a0 = EXPR` | Binary writes `EXPR` into `a0` on every valid input. | Every byte of `a0` matches the intended behavior. |
| `stack N` (or formula) | Binary uses at most `N` bytes of stack (including callees). | Fits inside the caller's stack budget. |
| `decreases EXPR` | Recursive calls strictly decrease `EXPR` (so the function terminates). | Nothing — checked mechanically by the verifier. |
| `needs avx` / `avx512` | Binary uses only instructions from the listed CPU features. | Callers check CPU features before calling the function. |

### Testing the contract on concrete vectors

To evaluate any definition inside a `.ocl` contract on RFC vectors, boundary inputs, or regression
cases:

```sh
ode spec-test utf8.ocl --call f0 --arg "[65]"          # -> 65 ('A')
ode spec-test utf8.ocl --call f0 --arg "[192, 175]"    # -> 4294967295 (overlong rejected)
```

---

## 3. Recording Your Audit Result

When reporting your conclusion to your client, record **both** full 52-character base-32 BLAKE3
hashes from `ode audit`:

- **`BLAKE3(binary)`** binds your audit to the exact binary bytes you inspected and tested.
- **`BLAKE3(contract)`** binds your audit to the exact canonical contract text that the binary was
  proved to satisfy, so your client can check it automatically with `--expect-contract`.

---

## Advanced Chapter A: Auditing Timing Side Channels

*Read this chapter when the code handles keys, authentication tags, passwords, or other data that
must be kept out of timing side channels.*

Ode contracts support an optional `trace depends on` clause governing which inputs may affect
**instructions executed** and **memory addresses read or written**:

- **Default (no `trace depends on` line):** No argument may influence control flow or memory
  addresses. For example, our 20-round RFC 8439 ChaCha20 block contract omits `trace depends on`:
  ```ocl
  contract (a0: 64 bytes, a1: 64 bytes) {
      requires no_overlap(a0, a1)
      ensures a0 = bytes_of(f0(words(a1)))
      stack 0
  }
  ```
  A `shown` verdict proves that neither the key, the nonce, nor the block counter affects which
  instructions run or which memory addresses are touched.
- **Explicit `trace depends on a0, a1`:** Branches and memory addresses may depend only on the
  listed arguments or computed values (for example, `f1(a0, a1)` for a tag comparison). Every input
  omitted from that line is kept out of the timing trace.
- **Optional `result depends on a0`:** For contracts that return a named result without an explicit
  formula, restricts which inputs the returned integer may depend on.

**Scope of the trace theorem:** `Ode.verify_all_trace` guarantees identical instruction streams and
memory-address sequences across runs that agree on `trace depends on`. It does not model
data-dependent arithmetic latency on specific CPUs, power or electromagnetic leakage, or speculative
execution (Spectre/Meltdown).

---

## Advanced Chapter B: Mixed-Language Binaries (Ode Linked With Rust or C)

When a final executable combines verified Ode objects with Rust or C code, the audit splits 100% of
the executable code in the final binary into two lists:

1. **Verified by Ode:** each Ode code unit (with its `BLAKE3(binary)`, `BLAKE3(contract)`, and
   `ode_<52-character-hash>` link symbol checked against the Rust or C call site).
2. **Not verified by Ode:** all remaining objects and functions in the binary, which you audit
   using your normal process.

Where legacy C or Rust callers expect a fixed legacy name, keep that alias as a one-line wrapper
outside Ode pointing to `ode_<52-character-hash>`, so the link still fails if the contract changes.

---

## Advanced Chapter C: Installing and Verifying Ode Itself

*Read this chapter if you want to build `odeverify` from source, check its Lean 4 soundness proof,
or review the exact reliance set behind a `shown` verdict.*

### Building `odeverify` and checking its soundness proof

```sh
cd proof-core && lake build odeverify && cd ..
python3 -m unittest proof-core/test_sound.py
```

`test_sound.py` confirms that Lean 4 checks the soundness theorems (`Ode.verify_all_sound`,
`Ode.verify_all_trace`, `Ode.verify_all_result`) with zero `sorry` and only Lean's three standard
axioms (`propext`, `Classical.choice`, `Quot.sound`).

### Your reliance set (what a `shown` verdict relies on today)

The table below lists every component that a `shown` verdict relies on in the current repository, its
size, and how it is checked.

| Component | Size | How it is checked today |
|---|---|---|
| **Lean 4 verifier (`proof-core/*.lean`)** | 8,673 lines across 8 core files | Formally proved sound in Lean 4 (zero `sorry`, standard axioms only). |
| **Instruction tables (`core/x86.tab`, `arm64/arm64.tab`)** | 94 x86-64 rows; 54 AArch64 rows | Cross-checked against real x86-64 and Apple M6 hardware (`0` diffs); all `54/54` AArch64 rows formally proved against Google DeepMind's `arm64-semantics` (`arm64/agree/`). |
| **Statement builder (`proof-core/statement.py`)** | 791 lines of Python | Tested and audited, not yet formally proved. Translates ELF `.o` + canonical `.ocl` into `.statement`. |
| **Auditor front-end (`lang/ode_canon.py`, `lang/ode_audit.py`)** | 1,490 lines of Python | Tested with positive and adversarial controls (`lang/test_ode_canon.py`, `proof-core/test_ode_audit.py`); checks ELF structure, `.ode.ocl`, hashes, and invokes `odeverify`. |
| **Lean 4 kernel / runtime** | External | Standard Lean 4 toolchain (independent verifiers for the same `.proof` format are a future goal). |

*(Where a specification was translated from an existing Lean 4 specification using `lean2ode/`, see
`lean2ode/agree/` for machine-checked Lean 4 theorems proving the Ode specification agrees with the
source Lean 4 specification on all inputs.)*

---

## Appendix D: Prototype Status (Today's Commands vs. This Guide)

The table below maps each step of this guide to what already runs in the repository today and what is
still on our roadmap.

| Target workflow in this guide | Status today (November 2026) | Exact command that runs today |
|---|---|---|
| Canonical `<52-char-hash>.ocl` extraction + glossary split + hash-filename check | **Working today** (`lang/ode_canon.py`, `lang/ode_unified.py`) | `python3 lang/ode_tool.py canon program.ode --fn name --target x86_64 --out-dir /tmp` |
| Hash-bound ELF `.o` (`ode_<52>` symbol + embedded `.ode.ocl` + separate `.proof`) | **Working today** for single-function and multi-function ELF `.o` bundles (unified `.ode` with local custom-`calling` helpers, plus full 14-fn x86-64 & 7-fn AArch64 BLAKE3 bundles) (`lang/ode_audit.py`) | `python3 lang/ode_tool.py pack program.ode --fn name --target x86_64 --out /tmp/u.o --proof /tmp/u.proof` |
| Binary-first `ode audit` (100% `.text` & symbol coverage across exported + `STB_LOCAL` functions, rejects hooks/extra sections/undefined symbols/non-NOP gaps/shadowing/spoofed `<hash>.ocl`, optional `--proof` auto-proving for loop-free single-fn `.o`, runs `odeverify`) | **Working today** for single- and multi-function ELF `.o` bundles (`lang/ode_tool.py audit`; suites in `proof-core/test_ode_audit.py`, `test_unified_ode.py`, `test_bundle_audit.py`) | `python3 lang/ode_tool.py audit /tmp/u.o --proof /tmp/u.proof --expect-contract jsvn5lp6d5igxjd5vq6iz4da5bmtqsfpvp5h3wle27pgrbm2peqa --show-contract` |
| Concrete `.ocl` vector tests (`ode spec-test`) | **Working today** (`lang/ode_tool.py spec-test`) | `python3 lang/ode_tool.py spec-test /tmp/<52-char-hash>.ocl --call f0 --arg "[192, 175]"` |
| Multi-function `.o` bundles with local Ode callees & custom calling conventions | **Working today** — pure-Python ELF64 merger (`ode_audit.merge_elf_objects`), helper contracts & `calling` blocks inside `.proof` checked via `ode.with_proof`, verified on `quad.ode` and full x86-64 (14 fns) & AArch64 (7 fns) BLAKE3 | `python3 proof-core/test_bundle_audit.py` |
| Cross-platform binary decoding (Mach-O, COFF) | `ode_audit.py` and `statement.py` decode **ELF `.o`** today (x86-64 & AArch64) | On macOS Mach-O / Windows COFF builds, compare linked `.text` instruction bytes against the verified ELF `.o` |
| Source format (`unified .ode` vs legacy `.ode` + `.spec`) | Unified `.ode` (contracts on `fn`, multi-arch `for <arch>`, `calling` on `fn`, closed per-file namespace) is live (`lang/ode_unified.py`); existing library `.spec` files remain supported during migration | Pass a unified `.ode` directly to `ode_tool.py canon`, `check`, or `pack` |

### Where to go next

- Full design and reliance-set analysis: [`DESIGN.md`](../DESIGN.md)
- Verified catalog of 38+ routines across x86-64 and AArch64: [`CATALOG.md`](../CATALOG.md)
- Companion pocket reference for people writing Ode code: [`docs/ODE-CARD.md`](ODE-CARD.md)
