# Author-assisted proof production: precedents and opportunity

Ode authors may supply proof structure and restructure implementations to
make verification tractable. A producer may ask for specific help after a
bounded attempt. `DESIGN.md` states the design and its correctness and
performance boundaries; this page records related work.

## Established practice

- **Interactive proof assistants** such as Coq/Rocq, Lean, and Isabelle
  already make author-provided lemmas, induction choices, and tactics
  central. Their interaction demonstrates that useful proof systems need
  not infer every proof automatically.
- **Dafny**, an open-source verifier originating at Microsoft Research,
  explicitly recommends intermediate assertions, small lemmas, opaque
  definitions, splitting verification conditions, and restructuring code.
  Its [verification optimization guide](https://dafny.org/dafny/VerificationOptimization/VerificationOptimization)
  explains how source structure changes the facts available to the solver
  and how authors can improve verification predictability and cost. This
  is a particularly close precedent for the proposed performance strategy.
- **F***, an open-source research language used in verified cryptography,
  treats proofs as programs and supports explicit author-written lemmas.
  Its [lemmas and induction tutorial](https://www.fstar-lang.org/tutorial/book/part1/part1_lemmas.html)
  explicitly describes cases where automation needs the author's help and
  recommends structuring proofs with lemmas.
- **Jasmin**, an open-source language and toolchain for high-assurance
  cryptography, couples verification support with programmer control over
  performance-critical low-level details. Its [documentation](https://jasmin-lang.readthedocs.io/en/latest/)
  emphasizes instruction selection, scheduling, register spilling, and
  predictable assembly without runtime penalties for high-level
  abstractions. This is a precedent for designing the language and its
  verification around the needs of fast cryptographic implementations.
- **Commercial verification tools**, including SPARK Pro and Frama-C's
  commercial support ecosystem, likewise use author-written contracts,
  loop invariants, and proof guidance. This is established assisted
  verification, rather than evidence that those products implement the
  exact proposed author-request interaction.

## What Ode can make better

The basic idea is established; the product opportunity is its execution.
A producer should ask for the smallest useful contribution, in the author's
terms: for example, “prove this relation between the two incoming carries,”
rather than emitting an opaque solver timeout. Requests should be scoped,
reproducible, and usable by either people or agents. Answers should become
checked, reusable artifacts. Source restructuring should preserve the
specification and the program's performance obligations.

The primary documentation linked above establishes the precedents for
hints, proof decomposition, and verification-oriented source design. It
does not establish a novelty claim for automatically generated requests
or a comparative performance claim for Ode. Those require implementation
and evidence.

## Current Ode interface

`ode.equation_cli` implements a small handoff using ordinary kernel goals
and proofs: unresolved arithmetic normalization emits a residual goal,
and an author-supplied proof is composed into the original proof and
checked. [PROOFS.md](PROOFS.md) documents its status codes and limits.
The richer diagnostic requests described above remain design objectives.
