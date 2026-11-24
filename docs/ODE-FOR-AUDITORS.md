# Ode for Security Auditors

> **Documentation-Driven Design note:** This pocket guide describes the minimal auditor workflow we
> are building toward (using `.ocl` — Ode Contract Language — and `ode audit`). Because Ode is an
> active research prototype, [Appendix D](#appendix-d-prototype-status-todays-commands-vs-this-guide)
> maps each step to the exact commands that already run in this repository today.

So you are auditing a codebase, and it contains Ode code. You have come to the right place.

Ode code ships with a complete formal proof that the compiled binary matches a short formal
specification—called a **contract**—written in a `.ocl` (Ode Contract Language) file. Because the
verifier checks the compiled machine-code bytes directly against that contract, you can ignore the
`.ode` source files and `.proof` files, run `ode audit` on the binary, and focus your audit on the
contract.

---

## 1. Start From the Binary

Begin with the compiled binary artifact (object file, library, or executable) that will actually run,
and run:

```sh
ode audit path/to/binary
```

Each Ode binary carries its `.ocl` contract in a non-executable metadata section (while the proof
lives in a separate `.proof` file, or is regenerated on demand). Running `ode audit` does four
things:

1. Extracts the single `.ocl` contract bound to the binary (or checks an external `--contract
   FILE.ocl` you supply).
2. Verifies the proof directly against the binary's actual machine-code bytes.
3. Confirms that the contract covers 100% of the binary's executable code and exported symbols, with
   no extra code or startup initializers.
4. Prints the full 64-character BLAKE3 hashes of both the binary and the canonical contract:

```text
BINARY:   libblake3_ode.a
  BLAKE3(binary):    9f3c...a812  (exact 64-hex digest)
  BLAKE3(contract):  4a71...c09e  (canonical .ocl, 7 lines)
  COVERAGE:          100% of executable code (14 functions, 3,761 instructions, 1 exported symbol)
  VERDICT:           shown
```

To inspect the exact contract text that was verified, run:

```sh
ode audit --show-contract path/to/binary
```

You do not need to read any `.ode` source files or `.proof` files. The verifier checks the binary
bytes themselves, so the verdict does not rely on the author, the `.ode` compiler, the assembler, or
the prover.

---

## 2. Read and Test the Contract

A security flaw or backdoor cannot exist in the binary code covered by this contract unless there is
a mistake, a backdoor, or excess looseness in the contract itself.

### A complete contract example (`utf8_decode_2byte.ocl`)

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

Every Ode contract is a **closed world**: anything the contract does not explicitly permit, the
binary is forbidden to do. On the example above, `shown` establishes for every valid input of every
length `n` that the binary reads only `input[0 .. n]`, writes no caller memory, returns
`utf8_cp2(input)` (rejecting empty inputs, truncated sequences, and overlong `0xC0`/`0xC1` encodings
such as CVE-2008-2938), uses at most `0` bytes of stack, terminates, and returns cleanly.

### Contract Clauses at a Glance

The table below lists each clause that can appear inside a `contract` block, what it establishes,
and what to verify while reading it.

| Clause | What it establishes | What to check in the contract |
|---|---|---|
| `arg: n bytes` / `64 bytes` / `cv` | Memory buffer passed by pointer (`cv` = 32 B, `block` = 64 B). Read-only unless written by `ensures`. | Size and layout match the protocol or API. |
| `arg: number` | 64-bit unsigned integer argument. | No wraparound or sentinel-value ambiguity. |
| `requires COND` | Precondition callers must satisfy (e.g. `no_overlap(out, inp)`, `n <= 64`). | Not contradictory, and no stronger than what callers guarantee. |
| `returns EXPR` | Exact value returned by the function. | Edge cases: empty input, maximum length, malformed input, error sentinel. |
| `ensures out = EXPR` | Exact bytes written into output buffer `out`. | Every byte of `out` is specified and matches the standard. |
| `stack N` (or formula) | Upper bound on stack bytes used (including callees). | Fits safely inside the caller's stack budget. |
| `decreases EXPR` | Non-negative measure that strictly drops on every recursive call. | Guarantees termination (no infinite loops). |
| `needs avx` / `avx512` | CPU instruction set used by the binary. | Callers gate on CPU feature detection before invoking the function. |

### Testing the contract on concrete vectors

To evaluate any `.ocl` definition on RFC vectors, boundary inputs, or regression cases:

```sh
ode spec-test utf8_decode_2byte.ocl --call utf8_cp2 --input "[0x41]"          # -> 65 ('A')
ode spec-test utf8_decode_2byte.ocl --call utf8_cp2 --input "[0xC0, 0xAF]"    # -> 4294967295
```

If your team or community has already reviewed a standard contract (for example, RFC 8439 ChaCha20
or BLAKE3), you can compare `BLAKE3(contract)` directly against that known 64-character hash.

---

## 3. Recording Your Audit Result

When reporting your conclusion to your client, record **both** full 64-character BLAKE3 hashes from
`ode audit`:

- **`BLAKE3(binary)`** binds your audit to the exact binary bytes you inspected and tested.
- **`BLAKE3(contract)`** binds your audit to the exact canonical contract text that the binary was
  proved to satisfy, so your client can verify that the contract matches their requirements.

---

## Advanced Chapter A: Auditing Timing Side Channels

*Read this chapter when the code handles keys, authentication tags, passwords, or other data that
must be kept out of timing side channels.*

Ode contracts support an optional `trace depends on` clause governing which inputs may affect
**instructions executed** and **memory addresses read or written**:

- **Default (no `trace depends on` line):** No argument may influence control flow or memory
  addresses. For example, our 20-round RFC 8439 ChaCha20 contract omits `trace depends on`:
  ```ocl
  contract ode_chacha20_block(out: 64 bytes, state: 64 bytes) {
      requires no_overlap(out, state)
      ensures out = bytes_of(chacha20_block(words(state)))
      stack 0
  }
  ```
  A `shown` verdict proves that neither the key, the nonce, nor the block counter affects which
  instructions run or which memory addresses are touched.
- **Explicit `trace depends on X, Y`:** Branches and memory addresses may depend only on `X` and `Y`
  (which may be inputs such as `len`, or computed values such as `same(want, tag)` for a tag check).
  Every input omitted from that line is kept out of the timing trace.
- **Optional `result depends on X`:** For contracts that return a named result without an explicit
  formula, restricts which inputs the returned integer may depend on.

**Scope of the trace theorem:** `Ode.verify_all_trace` guarantees identical instruction streams and
memory-address sequences across runs that agree on `trace depends on`. It does not model
data-dependent arithmetic latency on specific CPUs, power or electromagnetic leakage, or speculative
execution (Spectre/Meltdown).

---

## Advanced Chapter B: Mixed-Language Binaries (Ode Linked With Rust or C)

When a final executable combines verified Ode objects with Rust or C code, `ode audit final_binary`
splits 100% of the executable code in `final_binary` into two lists:

1. **Verified by Ode:** each Ode code unit (with its `BLAKE3(binary)` slice, `BLAKE3(contract)`,
   and mechanical FFI boundary check against the Rust/C call site).
2. **Not verified by Ode:** all remaining objects and functions in `final_binary`, which you audit
   using your normal process.

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
| **Statement builder (`proof-core/statement.py`)** | 791 lines of Python | Tested and audited, not yet formally proved. Translates ELF `.o` + contract file into `.statement`. |
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
| File extension `.ocl` | Repository files currently use `.spec` | Replace `.ocl` with `.spec` (e.g. `factory/verified/utf8_decode_2byte_x86_64.spec`) |
| Embedded `.ode.ocl` section + `ode audit BINARY` (100% coverage, BLAKE3 hashes) | **Planned** — today you pass ELF `.o` + `.spec` + `.proof` explicitly | `python3 proof-core/statement.py FILE.spec /tmp/s.statement FILE.o:SYM` then `./proof-core/.lake/build/bin/odeverify core/x86.tab /tmp/s.statement FILE.proof` (or `python3 -m unittest proof-core/test_hashr.py proof-core/test_hashr_arm64.py proof-core/test_chacha20.py factory/test_factory_native.py`) |
| Mechanical FFI boundary & symbol-export check (mixed binaries) | **Planned** — inspect `extern "C"`, `requires`, CPU feature guards, and `.globl` exports manually for now | Inspect `src/ffi_ode.rs` and `nm`/`objdump`; see `paper/CALL-CONV-PROPOSAL.md` for the AArch64 `v8..v15` ABI fix currently enforced by tests and queued for the Lean model |
| Cross-platform binary decoding (ELF, Mach-O, COFF) | `statement.py` decodes **ELF `.o`** today (both x86-64 and AArch64) | On macOS Mach-O / Windows COFF builds, compare linked `.text` instruction bytes against the verified ELF `.o` |
| `ode spec-test FILE.ocl --call FN --input ...` | Works via Python `kcheck/ode.py` | `python3 -c 'import sys; sys.path.insert(0,"kcheck"); import ode; sp=ode.Spec(open("factory/verified/utf8_decode_2byte_x86_64.spec").read()); print(sp.call(ode.Numbers(),"utf8_cp2",[0xC0,0xAF]))'` |

### Where to go next

- Full design and reliance-set analysis: [`DESIGN.md`](../DESIGN.md)
- Verified catalog of 38+ routines across x86-64 and AArch64: [`CATALOG.md`](../CATALOG.md)
- Companion pocket reference for people writing Ode code: [`docs/ODE-CARD.md`](ODE-CARD.md)
