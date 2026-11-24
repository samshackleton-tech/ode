# Ode for Security Auditors

> **Documentation-Driven Design note:** This pocket guide describes the minimal auditor workflow we
> are building toward (using `.ocl` — Ode Contract Language — and `ode audit`). Because Ode is an
> active research prototype, [Appendix C](#appendix-c-prototype-status-todays-commands-vs-this-guide)
> maps each step to the exact commands that already run in this repository today.

So you are auditing a codebase, and it contains Ode code. You have come to the right place.

You are in luck: Ode code comes with a **complete formal proof** that the compiled binary code
matches a short formal specification—which we call a **contract**—written in a `.ocl` (Ode Contract
Language) file. That means you can ignore the `.ode` implementation files and the `.proof` files,
run `ode audit` on the final binary, and spend your time on the one job that actually requires human
security judgment: scrutinizing the contracts.

---

## 1. What You Can Safely Ignore

When you open a repository or tarball containing Ode code, you do **not** need to read:

- **`.ode` files** (the machine-level implementation: instructions, registers, loops, stack frames)
- **`.proof` files** (loop invariants, arithmetic witnesses, and prover hints)
- **Decoy or unused files** anywhere in the repository or tarball

`ode audit` verifies the **actual compiled machine-code bytes inside the final binary** directly
against the contract. You do not rely on the author, the `.ode` compiler, the assembler, or the
prover for the binary satisfying its contract.

---

## 2. Step 1 — Start From the Final Binary, Never From Filenames

Never start an audit by scanning directories for `.ocl` files. A hostile author could fill a tarball
with ten thousand decoy `.ocl` files to exhaust you, or hide a backdoor inside an innocently named
object file while pointing your eyes at clean files.

Instead, always start from the **final built binary** (the executable, library, or crate artifact
that will actually run) and run:

```sh
ode audit path/to/final_binary
```

`ode audit` inspects the actual executable code linked into `final_binary`, runs the formal verifier
on every Ode code unit inside it, checks the FFI call boundaries mechanically, and partitions **100%
of the executable code in `final_binary`** into two lists:

```text
FINAL BINARY: libblake3_servil_core.rlib (BLAKE3 9f3c...a812)

1. VERIFIED BY ODE (1 contract, 3,761 instructions, all proofs: shown)
   - blake3_servil_ode_hashr  ->  contract BLAKE3 4a71...c09e  (7 lines)
     FFI boundary: matches Rust wrapper in src/ffi_ode.rs (0 issues)

2. NOT VERIFIED BY ODE (audit normally)
   - Rust crate code: src/lib.rs, src/hasher.rs, src/platform.rs, ...
   - 0 other native object files
```

Notice what this guarantees immediately:
- **Decoy files vanish.** Even if the tarball contains 10,000 unused `.ode` or `.ocl` files, none of
  them appear in `final_binary`, so `ode audit` ignores all 10,000 of them.
- **Hidden backdoors cannot hide.** Any extra native code linked into `final_binary` either lacks a
  valid proof—so it shows up loudly in **List 2 (Not verified by Ode)**—or it carries a proof, in
  which case its contract appears right in **List 1**, where an extra contract sticks out
  immediately.
- **No manual FFI plumbing checks.** Because `ode audit` mechanically checks that each verified
  entry point matches its Rust or C FFI binding (parameter order, types, sizes, memory overlap
  guarantees, CPU feature guards, and exported symbol list), you do not have to hand-check raw
  `extern "C"` declarations.

Ask `ode audit` to print the exact contract(s) in List 1:

```sh
ode audit --show-contracts path/to/final_binary
```

---

## 3. Step 2 — Your One Job: Scrutinize Every Contract in List 1

Because the formal verifier already proves that the binary obeys each contract on **every** possible
input, the primary way a bug or backdoor can slip past Ode is if the **contract itself** allows
something harmful.

**Reading, questioning, and stress-testing the `.ocl` contract is your main job.** Do not treat it
as a quick glance. Spend real audit time on those few dozen lines—cross-check them against the RFC or
security requirements, test them on edge cases and historical CVEs, and where the stakes are high,
rewrite the specification yourself from scratch and compare the two.

### A real contract example (`utf8_decode_2byte.ocl`)

Here is a complete 15-line contract for a strict 1- and 2-byte UTF-8 decoder:

```ocl
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
    stack 0
}
```

### The Closed-World Rule

Every Ode contract is a **closed world**: *anything the contract does not explicitly allow, the
binary is forbidden to do.* For the example above, `shown` proves that on every possible input:
- The function reads **only** bytes inside `input[0 .. n]` and writes **no** caller memory at all.
- It returns the exact value `utf8_cp2(input)`—rejecting empty buffers, truncated 2-byte sequences,
  and overlong `0xC0`/`0xC1` encodings (CVE-2008-2938).
- It uses at most `0` bytes of stack, terminates, and returns cleanly.

### Contract Clauses at a Glance

The table below lists every clause you will read inside a `contract` block and what to check when
auditing it.

| Clause | What it promises | What to look out for as an auditor |
|---|---|---|
| `arg: n bytes` / `64 bytes` / `cv` | Memory buffer passed by pointer (`cv` = 32 B, `block` = 64 B). Read-only unless written by `ensures`. | Check the size matches the caller's buffer and the protocol format. |
| `arg: number` | 64-bit unsigned integer argument. | Watch for wraparound or sentinel-value ambiguity in the return value. |
| `requires COND` | Precondition the caller must guarantee (e.g. `no_overlap(out, inp)`, `n <= 64`). | **Check that `requires` is not contradictory or stronger than real callers provide.** |
| `returns EXPR` | Exact value returned by the function. | **Check every edge case:** empty input, max length, malformed bytes, error sentinel. |
| `ensures out = EXPR` | Exact bytes written into output buffer `out`. | **Check that every byte of `out` is pinned down** and matches the standard. |
| `stack N` (or formula) | Upper bound on stack bytes used (including callees). | Check the bound fits safely inside your program's stack budget. |
| `decreases EXPR` | Non-negative measure that strictly drops on every recursive call. | Guarantees the function always terminates (no denial-of-service loops). |
| `needs avx` / `avx512` | CPU instruction set used by the binary. | Verified against the caller's CPU feature guard by `ode audit`. |

### Stress-test the contract on real vectors

You can execute any `.ocl` definition directly on concrete test vectors (RFC vectors, CVE inputs,
boundary cases) to verify that the contract means what you think it means:

```sh
ode spec-test utf8_decode_2byte.ocl --call utf8_cp2 --input "[0x41]"          # -> 65 ('A')
ode spec-test utf8_decode_2byte.ocl --call utf8_cp2 --input "[0xC0, 0xAF]"    # -> 4294967295 (rejected!)
```

Once every contract in List 1 matches your security requirements, your audit of the Ode portion of
`final_binary` is **done**. Spend the rest of your audit on List 2.

---

## Advanced Chapter A: Auditing Timing Side Channels

*Read this chapter only if the code handles keys, authentication tags, passwords, or other data that
must be kept out of timing side channels.*

Ode contracts support an optional `trace depends on` clause that controls what **instructions
executed** and **memory addresses read or written** may depend on:

- **Default (no `trace depends on` line):** Nothing in the function's arguments may affect which
  instructions run or which memory addresses are touched. For example, our 20-round RFC 8439
  ChaCha20 contract omits `trace depends on` completely:
  ```ocl
  contract ode_chacha20_block(out: 64 bytes, state: 64 bytes) {
      requires no_overlap(out, state)
      ensures out = bytes_of(chacha20_block(words(state)))
      stack 0
  }
  ```
  A `shown` verdict here proves that neither the key, the nonce, nor the counter influences any
  branch or memory address.
- **Explicit `trace depends on X, Y`:** Branches and memory addresses may depend **only** on `X` and
  `Y` (which may be inputs like `len`, or computed values like `same(want, tag)` for a tag check).
  Every input omitted from that line is kept out of the timing trace.
- **Optional `result depends on X`:** For contracts that return an abstract named result without an
  explicit formula, restricts which inputs the returned integer may depend on.

**What to check as an auditor:** Make sure no key, plaintext, or authentication tag appears on the
`trace depends on` line.

**What the trace theorem does not cover:** Ode's trace theorem (`Ode.verify_all_trace`) guarantees
identical instruction streams and identical memory-address sequences across runs that agree on
`trace depends on`. It does **not** model variable-latency arithmetic instructions on quirky CPUs,
power or electromagnetic emanations, or speculative execution (Spectre/Meltdown).

---

## Advanced Chapter B: Installing and Verifying Ode Itself

*Read this chapter if you want to build the verifier from source, check its soundness proof, or
examine the exact reliance set behind a `shown` verdict.*

### Building `odeverify` and checking its soundness proof

```sh
cd proof-core && lake build odeverify && cd ..
python3 -m unittest proof-core/test_sound.py
```

`test_sound.py` asks Lean 4 to verify the verifier's own soundness theorems (`Ode.verify_all_sound`,
`Ode.verify_all_trace`, `Ode.verify_all_result`) with zero `sorry` and only Lean's three standard
axioms (`propext`, `Classical.choice`, `Quot.sound`).

### Your reliance set (what a `shown` verdict relies on today)

The table below lists every component that a `shown` verdict relies on in the current repository, its
size, and how you can check it.

| Component | Size | How it is checked today |
|---|---|---|
| **Lean 4 verifier (`proof-core/*.lean`)** | 8,673 lines across 8 core files | Formally proved sound in Lean 4 (zero `sorry`, standard axioms only). |
| **Instruction tables (`core/x86.tab`, `arm64/arm64.tab`)** | 94 x86-64 rows; 54 AArch64 rows | Cross-checked against real x86-64 and Apple M6 hardware (`0` diffs); all `54/54` AArch64 rows formally proved against Google DeepMind's `arm64-semantics` (`arm64/agree/`). |
| **Statement builder (`proof-core/statement.py`)** | 791 lines of Python | Tested and audited, not yet formally proved. Translates ELF `.o` + contract file into `.statement`. |
| **Lean 4 kernel / runtime** | External | Standard Lean 4 toolchain (independent verifiers for the same `.proof` format are a future goal). |

*(Where a specification was translated from an existing Lean 4 specification using `lean2ode/`, see
`lean2ode/agree/` for machine-checked Lean 4 theorems proving the Ode specification agrees with the
source Lean 4 specification on all inputs.)*

---

## Appendix C: Prototype Status (Today's Commands vs. This Guide)

Ode is under active development. The table below maps each part of the target auditor workflow in
Sections 1–3 to what already works in this repository today and what is still being built.

| Target workflow in this guide | Status today (November 2026) | Exact command that runs today |
|---|---|---|
| File extension `.ocl` | Files in the repo currently use `.spec` | Replace `.ocl` with `.spec` (e.g. `factory/verified/utf8_decode_2byte_x86_64.spec`) |
| `ode audit FINAL_BINARY` (partition binary, check all proofs, hide decoys) | **Not built yet** — today you pass ELF `.o` + `.spec` + `.proof` explicitly | `python3 proof-core/statement.py FILE.spec /tmp/s.statement FILE.o:SYM` then `./proof-core/.lake/build/bin/odeverify core/x86.tab /tmp/s.statement FILE.proof` (or run `python3 -m unittest proof-core/test_hashr.py proof-core/test_hashr_arm64.py proof-core/test_chacha20.py factory/test_factory_native.py`) |
| Mechanical FFI boundary & symbol-export verification | **Not built yet** — check `extern "C"` types, `requires`, CPU feature guards, and `.globl` exports manually for now | Inspect `src/ffi_ode.rs` and `nm`/`objdump` on the linked binary; see `paper/CALL-CONV-PROPOSAL.md` for the AArch64 `v8..v15` ABI fix currently enforced by tests and queued for the Lean model |
| Cross-platform binary decoding (ELF, Mach-O, COFF) | `statement.py` decodes **ELF `.o`** today (both x86-64 and AArch64) | On macOS Mach-O / Windows COFF builds, compare the linked `.text` instruction bytes against the verified ELF `.o` |
| `ode spec-test FILE.ocl --call FN --input ...` | Works via Python `kcheck/ode.py` | `python3 -c 'import sys; sys.path.insert(0,"kcheck"); import ode; sp=ode.Spec(open("factory/verified/utf8_decode_2byte_x86_64.spec").read()); print(sp.call(ode.Numbers(),"utf8_cp2",[0xC0,0xAF]))'` |

### Where to go next

- Full design and reliance-set analysis: [`DESIGN.md`](../DESIGN.md)
- Verified catalog of 38+ routines across x86-64 and AArch64: [`CATALOG.md`](../CATALOG.md)
- Companion pocket reference for people writing Ode code: [`docs/ODE-CARD.md`](ODE-CARD.md)
