# Ode

*Object-code Direct Evidence* — native machine code whose actual bytes carry a machine-checked proof against a readable contract.

Ode is built for **Bob**, the skeptical auditor. Bob reads a short declarative contract, runs a standalone verifier on the compiled object file and its proof, and gets a verdict on the exact instructions the processor will execute — without reading the implementation, without running the compiler, and without relying on the prover.

---

## Where to Start

- **The Language Book:** [`paper/ODE.pdf`](paper/ODE.pdf) — the complete design report (contracts, nameless BLAKE3 contract identities, linked local namespaces, machine models, proof format, reliance sets, and measured results).
- **The Quickstart:** [`paper/quickstart.pdf`](paper/quickstart.pdf) / [`docs/QUICKSTART.md`](docs/QUICKSTART.md) — a hands-on guide to writing, checking, packing, and auditing two-target `.ode` programs.
- **For Auditors:** [`docs/ODE-FOR-AUDITORS.md`](docs/ODE-FOR-AUDITORS.md) — how to audit a compiled binary with `ode audit` and cross-check it with the independent second verifier `proof-core/verify2.py`.
- **Verified Catalog:** [`CATALOG.md`](CATALOG.md) — every verified program and target across x86-64 and AArch64.

---

## How Verification Works

1. **One source format (`.ode`).** Specifications (`const`, `def`, `layout`) and machine-code implementations (`for x86_64`, `for arm64`) live in `.ode` files connected by explicit linked local namespaces (`use alias = "file.ode"`).
2. **Nameless, content-defined contracts.** Canonicalizing a contract strips all chosen names and hashes the resulting text with BLAKE3-256 to a 52-character lowercase base-32 identifier (`ode_<52>`). The same contract produces the exact same identifier on x86-64 and AArch64.
3. **Separate proof-carrying artifacts.** `ode pack` produces a standard ELF64 object file (`.o`, with the canonical contract embedded in `.ode.ocl`) and a separate `.proof` file whose arithmetic refutation steps carry explicit rows (`r ...`), independent of any verifier's internal fact order.
4. **Two independent verifiers.**
   - **`proof-core/odeverify`** (Lean 4) — proved sound in Lean 4 against formal x86-64 and AArch64 machine semantics (`SoundTop.lean`, zero `sorry`, standard axioms only).
   - **`proof-core/verify2.py`** (pure Python) — an independent second verifier sharing zero verification code with Lean, checking the exact same `.statement` and `.proof` files.
5. **Four exact verdicts:** `shown`, `refused with a proof`, `no proof found`, and `run`.

---

## Quick Commands

```bash
# Type-check, compile, and verify a single function during development
python3 lang/ode_tool.py check paper/examples/all_zero.ode --target arm64

# Compile, prove, and audit a release ELF64 .o + separate .proof bundle
python3 lang/ode_tool.py pack paper/examples/all_zero.ode --target arm64 \
    --out /tmp/all_zero.o --proof /tmp/all_zero.proof

# Audit an object file and proof bundle against an expected contract ID
python3 lang/ode_tool.py audit /tmp/all_zero.o --proof /tmp/all_zero.proof \
    --expect-contract jbqyjqpese4s4cq35qxlhaevjvzuaqznquqw6mtlaqleluc25ika
```

---

## Repository Layout

| Directory | Purpose |
|---|---|
| `paper/` | The Ode Language Report (`ODE.pdf`, `ode.typ`), the Quickstart (`quickstart.pdf`, `quickstart.typ`), tested examples, and cold-room editorial tooling |
| `docs/` | Quickstart (`QUICKSTART.md`) and Auditor's Guide (`ODE-FOR-AUDITORS.md`) |
| `lang/` | Unified `.ode` parser and linked local namespaces (`ode_unified.py`), canonicalizer (`ode_canon.py`), compiler (`odec.py`), packer/auditor (`ode_audit.py`), and CLI (`ode_tool.py`) |
| `proof-core/` | Lean 4 verifier (`Core.lean`, `Arithmetic.lean`, `Contract.lean`, `Machine.lean`, `Reader.lean`, `Trace.lean`), Lean soundness proofs (`Sound*.lean`), prover (`prove.py`), independent second verifier (`verify2.py`), and verified examples |
| `core/` | x86-64 instruction table (`x86.tab`), table parser (`table.py`), and table rules (`RULES.md`) |
| `arm64/` | Standalone AArch64 instruction table (`arm64.tab`), encoder/decoder, hardware cross-checks, and Lean agreement proofs against Google's `arm64-semantics` (`arm64/agree/`) |
| `lean2ode/` | Standalone translator from Lean 4 pure functional specifications to Ode `.ode` specs with differential testing (`lean2ode/agree/`) |
| `kcheck/` | Specification parser and evaluator (`ode.py`), linear arithmetic prover (`klin.py`, `kprove.py`), and BLAKE3 reference specs |
| `wide/` | AVX-512 wide-vector BLAKE3 kernels in `.ode` (`one.ode`, `p16.ode`, `p32.ode`, `k32.ode`) |
| `advice/` | Microarchitectural cost advice and cache-line analysis |

---

## Licensing

Dual/quad-licensed under MIT, Apache-2.0, TGPPL-1.0, or BOSL-1.0, at your option.
