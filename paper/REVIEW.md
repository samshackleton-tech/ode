# Reading the Ode design report

This sheet accompanies `ODE.md` (revision 2, 22 November 2026). It is not part of the language definition. The implementation baseline is Ode `c407eb6` (same verifier code as `1dab0e3`: `Core.lean` SHA-256 `cf09a130adea315c`, `core/x86.tab` SHA-256 `825f760819bfe872`); the design is ahead of it. No verifier rule has changed since `1dab0e3`.

## Three observations, not one score

| Observation | Revision 1 | Revision 2 (current) | What to compare next time |
|---|---|---|---|
| How much language is there to read? | 5 rendered pages (2,160 words). | 5 rendered pages (2,393 words). Use `pypy3 render-paper.py ODE.md ODE.pdf` and `pdfinfo ODE.pdf`. | Use the same renderer, page size and type. Name any rule moved to another document. Do not count moving detail a reader still needs as a reduction. |
| What does verifying cost? | No self-verification timing yet; no fixed-basket baseline recorded. | Fixed 14-job basket (`basket v1`, below): **35,173.96 M retired user instructions** and **2.43 s** median wall time on the x86-64 Linux work machine; **2.04 s** median wall time on the Apple M6 macOS build machine (quiet). Still no verifier written in Ode. | Keep the 14-job basket stable across revisions; report input identities, host role, elapsed time, and retired instructions separately. Retired instructions resist host load changes, but do not replace user wait time. |
| Who relies on what, for what? | The routes below. | Same routes; no new dependency added or removed. | List added and removed dependencies, new alternatives, and dependencies that used to be independent but now coincide. |

The report is a design draft, not a standalone grammar or machine specification. The precise instruction meanings, byte encodings and full contract definitions still have to be read for an audit. The page count is **not** the size of Bob's total reading list.

## Fixed verification-basket baseline (`basket v1`)

All 14 jobs ran the current `odeverify` against the repository's stored proofs at `c407eb6` (`Core.lean` `cf09a130adea315c`, `core/x86.tab` `825f760819bfe872`). Every job returned `shown`, with identical statement and proof SHA-256 digests on both hosts. Retired instructions are the minimum of 5 `perf stat -e instructions:u` runs on the x86-64 Linux work machine (Threadripper PRO 7975WX); wall times are medians of 11 runs.

| Job | Statement (B) | Proof (B) | Retired instr. (M, x86-64) | Median (ms, x86-64) | Median (ms, Apple M6) |
|---|---:|---:|---:|---:|---:|
| `ode_sum` (+ `ode_third`) | 465 | 26 | 19.22 | 3.69 | 3.62 |
| `ode_equal` (+ `ode_common`) | 2,262 | 723 | 29.23 | 4.31 | 3.78 |
| `ode_adler32` | 2,493 | 2,967 | 42.80 | 5.07 | 4.31 |
| `ode_adler32_blocks4` | 6,722 | 22,656 | 404.05 | 27.42 | 23.69 |
| `ode_varint` | 1,463 | 453 | 39.30 | 5.52 | 4.43 |
| `compress_avx512` | 9,046 | 131 | 58.82 | 6.28 | 5.12 |
| `compress_sse41` | 9,512 | 137 | 67.18 | 7.01 | 5.52 |
| `b3l_node_out` (+ 2 kernels) | 13,031 | 306 | 101.60 | 9.27 | 7.00 |
| `b3l_pad` | 8,129 | 451 | 36.31 | 4.98 | 3.91 |
| `b3l_chunk_node` (+ 3 callees) | 17,376 | 6,107 | 2,443.70 | 162.22 | 162.70 |
| `p16` | 27,006 | 2,361 | 2,082.77 | 136.31 | 109.11 |
| `p32` | 78,240 | 4,178 | 9,759.74 | 665.32 | 561.13 |
| `k32` | 78,858 | 4,331 | 9,600.23 | 651.60 | 548.04 |
| `quad32+p32` | 84,641 | 4,193 | 10,489.03 | 739.67 | 602.18 |
| **Total (14 jobs)** | **339,244** | **49,020** | **35,173.96** | **2,428.65** | **2,044.54** |

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

## What we have, and results of the first two design tests

- The existing x86 verifier covers 8 of the 14 functions in the Ode hash and 1,470 of its 3,062 instructions. That is not a proof of the production library or of the complete Ode hash. In the small `ode_sum` example, the contract says `returns 14`, with a 16-byte stack budget. Its existing proof file is 12 bytes (`for ode_sum` and a newline); that short file does not include the verifier's rules, object code, contracts or the other functions' proofs.
- The existing `ode_quad32` example uses a 32-address table and calls a kernel with a contract. Its existing stack budget is 6,432 bytes. The new frame notation, per-use choice of inlining, early feedback, finer return rule, second processor and verifier in Ode are proposals, not features of `c407eb6`.

### Test 1: Hash operation (`d := (d ^ a) ror 16`, inline vs. macro vs. call, x86-64 and AArch64)

- **x86-64 AVX-512 (verified by the current `odeverify`, executed on x86-64 AVX-512 hardware):** across `N = 1, 4, 16, 56` alternating copies (56 matches 7 BLAKE3 rounds), raw instructions and the `def` text macro emit byte-identical code (`35, 74, 230, 750` bytes; 13 bytes per added copy: 6-byte `vpxord` + 7-byte `vprord`, matching `clang`). The current `odeverify` approves all four with constant proof size (`16` to `17` bytes) and linear work: `19.54, 20.87, 26.31, 44.81` M retired instructions (`3.69` to `5.25` ms median, `+0.46` M instructions per 16-lane copy). Checking `ode_mix16_step` standalone takes `19` proof bytes and `19.54` M instructions (`3.59` ms). Both false controls at `N = 4` (changing one rotate from `16` to `15`, and omitting one `vpxord`) are refused by `odeverify`.
- **AArch64 NEON (assembled, disassembled, and executed on Apple M6 hardware; execution testing, not formal Arm verification):** `eor v0.16b, v0.16b, v1.16b` + `rev32 v0.8h, v0.8h` (`8` bytes per copy; total `24, 48, 144, 464` bytes for `N = 1, 4, 16, 56`) matches both the mathematical specification and the x86-64 AVX-512 outputs on the first four lanes across all 16 test vectors. Omitting the final `rev32` is caught (`9ae1faa3 != faa39ae1`).
- **Call vs. inline:** calling a memory-passing C-ABI `ode_mix16_step` never breaks even in code size (`121, 187, 451` bytes at `N = 1, 4, 16` vs. `35, 74, 230` inline, plus stack frame traffic) and hits a missing unaligned 64-byte frame store rule in `proof-core`. An Ode register call breaks even in code bytes at `N = 2` on x86-64 (`14 + 5N` vs. `13N`) and `N = 4` on AArch64 (`12 + 4N` vs. `8N`) only when register assignments match across call sites without register moves.
- **Concrete macro hazard exposed by the second processor:** on AArch64 NEON, `(d ^ a) ror 12` needs a third scratch register (`eor`, `ushr`, `shl`, `orr` = 16 B in place, or `eor`, `ushr`, `sli` = 12 B into a renamed output). Passing `tmp == d` in a text macro assembles without error on Apple M6 and silently corrupts all four lanes (`99e00000 00000000 fff00000 00000000` instead of `897cc99e 00300000 ffffffff 00180000`). A contract-bearing inline function with a distinct-register check catches this at the source line with zero byte or runtime penalty. Keep `for` for constant unrolling, and keep `def` until real kernels run on the new front end.

### Test 2: Verifier component (`allZero` and exact arithmetic from `proof-core/Arithmetic.lean`)

- **First verifier component verified by the current `odeverify`:** `ode_all_zero` (early-exit x86-64 byte scan, `40` bytes, `0` stack) is proved and approved by the current Lean `odeverify` against `returns all_zero(xs)` with `trace depends on xs, n` (`770` B statement, `463` B proof, `21.57` M retired instructions, `3.78` ms median). Both false controls are refused: a deliberately shortened scan skipping the last element (which passes empty, all-zero, first-nonzero, and middle-nonzero tests while failing nonzero-final tests) is refused by `odeverify`, and dropping `xs` from `trace depends on` is directly refused (`refused: a jump on a flag that may depend on a secret`).
- **Four concrete gaps in the current verifier/decoder exposed by the second program:**
  1. Variable-length word loads: a 32-bit word OR-accumulator scan (`41` B on x86-64; `36` B and fully branchless on data via `ldr w2, [x0], #4` and `cset x0, eq` on AArch64, both passing empty, all-zero, LSB/MSB/signed `-1`, and nonzero-final tests with shortened-scan negative controls caught) is refused by `proof-core/Core.lean`'s `symLoad` (`a read of a run of bytes that is not one byte: not here yet`).
  2. Bitwise OR linear upper bound: `symOrKnown` in `Core.lean` records `v >= x` and `v >= y` without `v <= x + y`, so linear arithmetic cannot prove `(x == 0 and y == 0) -> (x | y == 0)` for symbolic operands.
  3. Branchless loop case split: proving a branchless OR-accumulator against a boolean prefix specification requires a proof-file case split (`acc == 0` vs. `acc > 0`) where the machine code itself does not branch.
  4. Multi-`ret` decoding: `kdecode.py` stops decoding at the first `ret`, truncating a function that places a second `ret` after an early return. Soundness held because `odeverify` refused the jump to the missing label, but early-exit code must share one final `ret` until the decoder follows all reachable code in the symbol.
- **Exact arithmetic vs. wraparound overflow (`Arithmetic.lean`'s `derive`):** two concrete 64-bit signed inputs from TRUE rows (`0*x + 2^62 >= 0` added to itself wraps to `-2^63 < 0`; `2^62*x + 0 >= 0` and `2^62*x - 1 >= 0` scaled by 2 wrap the coefficient sum to `0` with constant `-2 < 0`) forge a contradiction in 64-bit arithmetic without overflow checks. Checked implementations on x86-64 (`imul`+`jo`, `add`+`jo`: `29` bytes) and AArch64 (`mul`+`smulh`+`cmp asr #63`+`b.ne`, `adds`+`b.vs`: `60` bytes) decline both wraparound forgeries while approving exact refutations including floor division on negative constants.

### Next tests

1. Build the first single-tool higher-level Ode trial on `ode_quad32` (named registers, checked frame slots, checked call) and `ode_all_zero`, plus `p16`'s loop invariant written on the loop, emitting bytes and running the current `odeverify`.
2. Write the Arm formal-model proposal comparing Google's `arm64-semantics` with a small table-driven Arm model before verifying the first Arm function.

After each change, revisit this sheet and the report together. A proof file can shrink while the verifier gets harder to understand; inlining can make a loop faster while more instruction lines compete in a caller. None of the three observations substitutes for the others.
