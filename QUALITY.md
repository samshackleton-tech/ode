# Ode assurance and validation

Ode 0.1 is a research prototype. This page describes checks available in
this repository. [SPEC.md](SPEC.md) describes the target contract; the
blake3-servil experience in [LESSONS-blake3-verification.md](LESSONS-blake3-verification.md)
is background, not evidence of Ode's guarantees.

## Two checking paths

**The proof-object kernel** checks sorted equations and structural induction
against owner-selected theories and goals. Definitions are total and
structurally recursive; reusable lemmas need complete derivations.
[KERNEL.md](KERNEL.md) specifies the rules, soundness argument, and limits.
Generated proof artifacts are committed so recipients can check them
without running producers. The kernel itself has tests and a written
soundness argument; it has not been formally verified or independently audited.

**The executable verifier** compares decoded programs and specifications
using a symbolic evaluator and normalizer. Its larger reliance set includes
the word semantics, AArch64 model, and native runner. CPU cross-checks test
the instruction model. The proof kernel's declared register/encoding models
and exact fragment-byte checks do not yet establish Arm ISA correspondence.

Both paths rely on the selected specification expressing the owner's intent,
their checkers and readers, domain-separated BLAKE3 identities, PyPy and its
standard library, the OS, and hardware. [game/README.md](game/README.md)
describes package admission and adversarial delivery. Identity establishes
which code was admitted, not the soundness of that code.

## Reproduce the checks

From the repository root, with PyPy3:

```sh
pypy3 -m unittest discover -s tests
pypy3 game/kernel_attacks.py
pypy3 game/make_attacks.py
pypy3 game/referee.py game/attacks/*
pypy3 game/bootstrap/root/launch.py \
  game/bootstrap/kernel-targets/RELIANCE game/kernel-base examples/proofs g-fragment
```

The suite includes:

- proof regeneration, independent recipient checks, and resource bounds;
- malformed definitions, invalid rules, false goals, and proof mutations;
- deliberately broken kernels as controls for negative tests;
- full-adder and arbitrary-width numeric proofs, with small integer controls;
- official BLAKE3 hash/derive-key vectors and cross-domain/version rejection;
- package, owner-pin, proof, binary, and callee substitution attacks;
- specification/reference comparisons and AArch64 CPU cross-checks;
- freshly checked assurance reports and release-tool tests in temporary repos.

Native tests require AArch64 Linux and report skips elsewhere. A portable
suite pass therefore has a narrower scope than a native-host pass. Tests
exercise concrete cases; universal claims come from the specified proofs.
No independent audit or second independent kernel implementation is claimed.

## Remaining obligations

- Numeric Word32 truncation, source-syntax translation, native instruction
  refinement, memory, calling conventions, and compiled BLAKE3 loops.
- Constant-time/noninterference proofs and explicit hardware timing assumptions.
- Capability confinement and the broader runtime requirements in SPEC.md.
- Runtime performance measurements using `clocks`: wall time and core cycles,
  paired runs, and load-aware comparisons. Proof bytes/rules/work counts are
  deterministic proof-cost measures, not speed measurements.
- Hostile filesystem availability: package/store I/O is not wholly bounded
  by the kernel's proof-work limits. Package admission guarantees identity,
  not an overall wall-time bound for delivery from an arbitrary filesystem.

## Maintaining the evidence

Each changed claim needs positive and negative tests. Regenerate affected
proofs, then run the full suite and adversarial checks. After changing copied
checker modules, run `pypy3 game/pin_ode_base.py`; tests detect copy/pin drift.
Owner semantic pins require explicit review. Meaning changes follow
[DOMAINS.md](DOMAINS.md), including dependent identities and artifacts.

`assure` rechecks the store and writes a snapshot of the resulting model-level
claim, distinguishing executable code from interpreter-based bindings.
An owner still needs to approve the specification identity in that report.
The `ode-symbolic` checker label names the checking path; package pins identify
its code. `pypy3 -m ode --version` reports the separate release version.
