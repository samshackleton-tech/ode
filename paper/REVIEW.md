# Reading the Ode design report

This sheet accompanies `ODE.md` (revision 3, 22 November 2026). It is not part of the language definition. The implementation baseline is Ode `c407eb6` (same verifier code as `1dab0e3`: `Core.lean` SHA-256 `cf09a130adea315c`, `core/x86.tab` SHA-256 `825f760819bfe872`); the design is ahead of it. No verifier rule has changed since `1dab0e3`. The AArch64 formal-model proposal sits beside this sheet in [`ARM-PROPOSAL.md`](ARM-PROPOSAL.md).

## Three observations, not one score

| Observation | Revision 1 | Revision 2 | Revision 3 (current) | What to compare next time |
|---|---|---|---|---|
| How much language is there to read? | 5 rendered pages (2,160 words). | 5 rendered pages (2,393 words). | 5 rendered pages (2,416 words). Use `pypy3 render-paper.py ODE.md ODE.pdf` and `pdfinfo ODE.pdf`. | Use the same renderer, page size and type. Name any rule moved to another document. Do not count moving detail a reader still needs as a reduction. |
| What does verifying cost? | No baseline yet. | Fixed 14-job basket (`basket v1`): **35,173.96 M retired user instructions**, **2.43 s** x86-64 / **2.04 s** Apple M6. | Same 14-job Lean baseline; plus first V1 Ode verifier written in Ode runs `ode_sum` in **0.14 M instructions / 0.52 ms** (stage 1, narrow subset; not yet full verifier or self-verified). | Keep the 14-job basket stable across revisions; report input identities, host role, elapsed time, and retired instructions separately. Retired instructions resist host load changes, but do not replace user wait time. |
| Who relies on what, for what? | The routes below. | Same routes. | Same routes; `ARM-PROPOSAL.md` compares reliance sets for AArch64 options before any model is built. | List added and removed dependencies, new alternatives, and dependencies that used to be independent but now coincide. |

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

### Test 3: Single-tool prototype front end (`ode2.py`, 320 lines, x86-64 and AArch64)

Built and tested one small prototype front end implementing `target x86_64 | aarch64`, named registers, checked `frame` declarations with typed slot bounds, `inline fn` with typed register parameters, `distinct(...)` and `changes` checking, constant `for` unrolling, explicit `:=` store notation, and loop `place { ... }` blocks with automatic byte-offset computation:

- **`ode_quad32` (hash caller):** dropped from 157 lines (with 68 raw `[rsp + N]` byte offsets and two manual `2312` constants) to 66 lines with zero raw stack offsets and bounds-checked `table[i]` / `r2.qword[w]` accesses. Emitted an ELF object **byte-for-byte identical** to `proof-core/examples/quad/odequad32.o`, approved by the current Lean `odeverify` using the exact stored 15-byte `ode_quad32.proof`.
- **`blake3_servil_avx512_p16` (16-way BLAKE3 kernel):** replaced the `def g4(...)` text macro with a typed `inline fn g4(...: zmm) changes a0..d3` (zero text macros) and moved the loop invariant directly onto the loop (`place { ... }`). Emitted **byte-for-byte identical** `.text` (`2,768` B) and `.rodata` (`16` B), auto-computed the exact `+0x9a7` loop offset, was approved by `odeverify` with the stored proof, and reproved from scratch to the exact same `2,361`-byte proof. Across the entire repository only three `def` text macros exist (`p16.ode` and two in `one.ode`), and typed `inline fn` plus `for` replaces all three cleanly.
- **`ode_all_zero` (verifier component):** loop invariant written directly on `@loop:` auto-computed `+0x2` and verified (`463` B proof, `odeverify -> shown`). Inserting `nop` before `@loop:` auto-shifted the offset to `+0x3` with zero edits to the invariant and still verified (`463` B proof, `shown`).
- **AArch64 (`target aarch64`):** the same front end compiled `arm_mix16_4`, `arm_mix12` (with `distinct(d, tmp)`), and `arm_all_zero_words` (with named registers `xs/n/w/acc`), assembled with `clang` and passed native execution checks on Apple M6 hardware (execution testing, not Arm verification).
- **Nine negative source-line diagnostics verified:** frame upper/negative/view out-of-bounds (`table[32]`, `table[-1]`, `r2.qword[128]`), unknown frame field (`&missing_slot`), AArch64 `mix12(v0, v1, v0)` (`distinct(d, tmp)` violated), register writes not listed in `changes` inside `inline fn` on x86-64 (`zmm2`, and `zmm30` inside `p16`'s `g4`) and AArch64 (`v5`), and register-kind mismatch (`rax` where `zmm` is required). Each reported the exact source file, line number, and violated rule before assembling.

### Test 4: First V1 verifier written in Ode (`v1_verify.ode2`, Stage 1 milestone)

Built a first narrow verifier in pure Ode (`v1_verify.ode2`, 8 functions, `1,118` x86-64 instructions, `4,726` bytes `.text`), compiled through `ode2.py` and `core/asm.py` with **100% of its instructions decoded by Ode's `kdecode`**. It takes `(stmt, stmt_len, proof, proof_len, work, work_len)` over raw byte buffers with zero heap allocation (requires an 8,192-byte caller-supplied workspace; smaller workspaces cannot return approval) and reads the exact statement and proof files used by Lean `odeverify`:

- **Positive cases (`4/4` approved):** `ode_third` + `ode_sum` (with the stored 12-byte `ode_sum.proof`), `ode_third` + `ode_twice`, and both `STILL_TRUE` variants from `proof-core/test_sum.py`.
- **Negative controls (`22/22` refused, 0 false approvals):** all 8 mutated-source cases and all 5 mutated-contract cases from `proof-core/test_sum.py`, plus 9 guards (`data` after instruction, missing piece index, `lea_data` past piece end, wrong/missing/trailing proof headers, insufficient workspace `0` B and `4,096` B, unknown instruction).
- **Speed on `ode_sum` (x86-64 Linux work machine, whole process including startup and file I/O):** `136,827` retired user instructions (`0.14` M, 140× fewer than Lean `odeverify`'s `19.22` M) and `0.52` ms median wall time (vs. `3.69` ms for Lean `odeverify`).
- **Two actual compiled V1 helper objects formally verified by Lean `odeverify`:** `v1_hex_nibble.o` (`22` insns, `67` B, `300` B proof, `shown`; false spec `ch - 54` refused) and `v1_mem_eq.o` (`17` insns, `50` B, `532` B proof, `shown`; false spec returning `1` on mismatch refused).
- **What this does and does not establish:** Stage 1 demonstrates an Ode-written verifier running over real statement and proof bytes on a tiny straight-line subset (`ode_sum`/`ode_twice`/`ode_third`), and Stage 2 has started on two helper objects. It is **not** a full verifier for loops or vectors, and it does **not** yet have a whole-verifier soundness proof.

### Next steps (awaiting Sam's word on proposals where noted)

1. **AArch64 formal model ([`ARM-PROPOSAL.md`](ARM-PROPOSAL.md)):** awaits Sam's choice among Option A (direct `arm64-semantics`), Option B (standalone `core/arm64.tab`), and Option C (recommended: `core/arm64.tab` + optional Lean equivalence bridge to Google's `arm64-semantics`).
2. **Finer returned-number rule (`ODE.md` section 3):** awaits Sam's confirmation of the two-sentence rule before changing the formal model.
3. **Continue V1 -> V2 Ode verifier + small verifier enablers:** formally verify `v1_match_lit.o`, `v1_parse_dec.o`, `v1_parse_hex.o`, and `v1_parse_reg.o` under Lean `odeverify`, add `Arithmetic.lean` refutation verification (`all_zero` + checked 64-bit `derive`) to the Ode verifier, and tighten `symOrKnown` (`v <= x + y`) / variable-length word loads / multi-`ret` decoding.
4. **Promote the `ode2.py` front-end constructs into `lang/odec.py`** once the Arm target shape is approved, deleting `def` text macros in the same round.

After each change, revisit this sheet and the report together. A proof file can shrink while the verifier gets harder to understand; inlining can make a loop faster while more instruction lines compete in a caller. None of the three observations substitutes for the others.
