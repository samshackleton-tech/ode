# Reading the first Ode draft

This sheet accompanies `ODE.md`. It is not part of the language definition. The implementation baseline is Ode `1dab0e3`; the design is ahead of it. No new verifier rule is being asserted here.

## Three observations, not one score

| Observation | First entry | What to compare next time |
|---|---|---|
| How much language is there to read? | 5 rendered pages. Use `pypy3 render-paper.py ODE.md ODE.pdf` and `pdfinfo ODE.pdf`. | Use the same renderer, page size and type. Name any rule moved to another document. Do not count moving detail a reader still needs as a reduction. |
| What does verifying cost? | No self-verification timing yet: there is no verifier written in Ode. No single baseline yet for a fixed basket with a recorded input list. | Keep the basket stable across revisions; publish its identities, host role, elapsed time, and retired instructions separately. Retired instructions are particularly useful when load changes, but are not interchangeable with user wait time. |
| Who relies on what, for what? | The routes below. They are alternatives for a specified conclusion, not a count of components. | List added and removed dependencies, new alternatives, and dependencies that used to be independent but now coincide. |

The report is a design draft, not a standalone grammar or machine specification. The precise instruction meanings, byte encodings and full contract definitions still have to be read for an audit. The first page count is **not** the size of Bob's total reading list.

## Reliance sets at this revision

**Conclusion A:** acceptance by the mathematical verifier implies that the modeled function meets the modeled contract. The current theorem is `Ode.verify_all_sound`; it assumes `Linked`, which relates the programs in its world to the instructions given to the verifier. The separate `Ode.verify_all_trace` theorem states what two executions have in common. A proof of either theorem about a different machine or a different contract would not answer the same question.

| Reader and route | What is needed for A | What is available |
|---|---|---|
| Bob, via Lean | Bob must recognize the theorem he means and the definitions it names. He relies on a way of validating its proof, including the axioms used. If he already relies on Lean4Lean for that purpose, count it in the full set, not as an entirely new cost. | The Lean theorem exists. Successful independent replay of this theorem by Lean4Lean is not a result we have. |
| Barry, via Metamath Zero | Barry would need a statement about the same verifier, a proof accepted by the kernel he knows, and grounds for identifying its statement with A. | A possible route. No such proof is supplied. |
| Brenda, by reading | Brenda can examine the machine, contract semantics and verifier rules, including the arithmetic rule, and decide whether each acceptance step is sound. This route depends on her own reasoning, not on a Lean proof. | The definitions and rules are available. Whether this is less work for Brenda than learning a proof kernel is her decision. |
| A second verifier written in Ode | For agreement to add independent evidence, identify the components shared by both implementations, particularly readers and machine semantics. Self-verification alone does not break the circle. | Proposed, not available. |

**Conclusion B:** a particular binary, as loaded on a real processor, meets the contract the reader selected. None of the routes to A by itself yields B. Today the additional dependencies include reading the binary, decoding its instructions, binding call targets and constants, parsing the contract, reading the verifier input, running an executable that implements the mathematical verifier, loading the intended program, and how accurately the machine model describes the processor for the property in question. For example, an error in a decoder shared by two otherwise independent verifiers could give them the same wrong instruction list. The maker's compiler and proof search need not be correct for B **if the actual binary is what gets checked**.

A reader may separately judge whether the selected contract meets a practical need. Matching a vague intent is not a theorem about bytes. Keep dependencies for A, for B, and for that judgment on separate lines.

## What we have, and the two tests that could change the design

- The existing x86 verifier covers 8 of the 14 functions in the Ode hash and 1,470 of its 3,062 instructions. That is not a proof of the production library or of the complete Ode hash. In the small `ode_sum` example, the contract says `returns 14`, with a 16-byte stack budget. Its existing proof file is 12 bytes (`for ode_sum` and a newline); that short file does not include the verifier's rules, object code, contracts or the other functions' proofs.
- The existing `ode_quad32` example uses a 32-address table and calls a kernel with a contract. Its existing stack budget is 6,432 bytes. The new frame notation, per-use choice of inlining, early feedback, finer return rule, second processor and verifier in Ode are proposals, not features of `1dab0e3`.
- **Hash test:** compare the two-instruction macro with an inline use under identical register assignments. Assemble and disassemble each target, prove the operation on lanes, count bytes across repeated copies, and compare proof work and what the coder must repeat. The two example instruction pairs in section 4 have been assembled and disassembled as x86-64 and Arm64 respectively. That validates the encodings, not the whole function, its performance, or Arm soundness.
- **Verifier test:** start with the zero-coefficient predicate from `proof-core/Arithmetic.lean`. Include empty input, all zero, and a nonzero last word. A deliberately shortened scan must fail the contract on the last case. Then use the predicate within the arithmetic rule. Do not call successful tests on words a proof for arbitrary integers. The first end-to-end goal is to approve `ode_sum` and refuse a false change to it, using the existing proof format.

After each change, revisit this sheet and the report together. A proof file can shrink while the verifier gets harder to understand; inlining can make a loop faster while more instruction lines compete in a caller. None of the three observations substitutes for the others.
