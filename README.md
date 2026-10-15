# Ode

*A short poem of praise.*

Ode builds cryptographic code together with independently checkable proofs.
This is the **0.1 research prototype**: it has a small equational proof
kernel, proof-producing arithmetic and abstract-machine tools, and a
separate executable verifier for BLAKE3. Native ISA refinement and a
competitive cryptographic implementation remain development goals.

## Try it

Run from this checkout with **PyPy3**; no third-party Python packages are
required. Proof checking is portable. Native execution needs AArch64 Linux.

```sh
pypy3 -m ode --version
pypy3 -m ode.proof_cli examples/proofs/arx.theory.sexp \
  examples/proofs/arx.goal.sexp examples/proofs/arx.proof.sexp
pypy3 -m unittest discover -s tests
```

The arithmetic example proves an equation combining 32-bit addition, XOR,
and rotation. The owner selects the theory and goal; the producer supplies
only a proof. The checker verifies every supporting lemma from definitions.

For an executable BLAKE3 example on AArch64 Linux:

```sh
pypy3 -m ode bind examples/blake3.sexp /tmp/ode-b3
pypy3 -m ode check /tmp/ode-b3
pypy3 -m ode hash /tmp/ode-b3 "The quick brown fox jumps over the lazy dog."
# 4c9bd68d7f0baa2e167cef98295eb1ec99a3ec8f0656b33dbae943b387f31d5d
pypy3 -m ode assure /tmp/ode-b3
```

Add `w32` to the `bind` command for interpreted bytecode on other machines.
The binding covers every valid message length: the specification's tree
logic runs in the interpreter, calling checked compression/chunk programs.
`build` and `build-a64` instead compile a chosen instantiation. These
executable checks rely on Ode's evaluator, normalizer, and instruction
models; they are separate from proof-object kernel verification.

## What is checked

| Component | Current guarantee | Boundary |
|---|---|---|
| Proof kernel (`ode/kernel.py`) | Sorted equations and structural induction, with checked reusable lemmas | Owner-selected definitions; checker/runtime correctness |
| Arithmetic producers | Word32 XOR, rotation, ripple-carry addition laws, and combined normalization | Native arithmetic refinement remains open |
| Numeric interpretation | Full-adder conservation and arbitrary finite ripple carry, retaining final carry | Fixed Word32 truncation bridge remains open |
| Register execution | BLAKE3 G equations and unbounded repetition/batching in a six-register model | Memory, flags, and ABI are outside this model |
| Fragment recipient | Exact bytes encode the same program whose abstract execution is proved | The 56-byte fragment is not a callable native function |
| Executable verifier (`ode/check.py`) | Decoded W32/AArch64 programs match specifications in its symbolic model | Its larger reliance set remains separate from the kernel |

The AArch64 model is cross-checked against the CPU. Derivation from Arm's
formal ISA, native memory/ABI proofs, constant-time guarantees, and full
compiled BLAKE3 loop refinements remain open. Ode has no current runtime
speed claim: qualifying measurements need the team's wall-time and
core-cycle measurement infrastructure.

## Identity and delivery

Canonical s-expressions represent specifications, certificates, theories,
goals, and proofs. Every identity uses BLAKE3 derive-key mode with an
explicit **kind and semantic revision**. Changing the interpretation changes
the domain even when bytes stay unchanged. [DOMAINS.md](DOMAINS.md) specifies
this policy; the release number and semantic revisions are independent.

The [adversarial game](game/README.md) checks delivery from a relying party's
perspective. A small owner-provided root admits checker packages by hash,
serves their checked bytes from memory, and enforces owner-selected claims.
Hash admission identifies code; its correctness remains a reliance.

Authors can supply intermediate lemmas when automation needs help.
`ode.equation_cli` emits an ordinary residual goal and accepts its checked
proof on a later invocation. Assistance changes neither the owner's goal
nor the kernel's rules.

## Reading and development

- [QUALITY.md](QUALITY.md): assurance boundaries and validation commands.
- [KERNEL.md](KERNEL.md): implemented logic, proof format, and resource limits.
- [PROOFS.md](PROOFS.md): runnable examples and their precise statements.
- [SPEC.md](SPEC.md) and [DESIGN.md](DESIGN.md): target contract and design;
  these include requirements the prototype has yet to implement.
- [AUTHOR-ASSISTED-PROOFS.md](AUTHOR-ASSISTED-PROOFS.md): related work.
- [RELEASING.md](RELEASING.md): versioning, checks, and release procedure.

Next: connect bit-list numeric addition to Word32 truncation, then connect
source operations and register execution to native ISA semantics. Memory,
calling conventions, native loops, and measured performance remain explicit
obligations on the path to a verified high-performance BLAKE3 implementation.
