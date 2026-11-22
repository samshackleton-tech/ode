# Reading the Ode design report

This sheet accompanies `ODE.md` (revision 4, 22 November 2026). It is not part of the language definition. It keeps three observations from one revision to the next: how much there is to read, what verifying costs, and who relies on what. It also says what a first trial of the proposed notation showed and what it did not show.

The verifier is that of commit `1dab0e3`: nothing proposed in `ODE.md` has been added to it. Its two main inputs, by BLAKE3:

- `proof-core/Core.lean`: `cc0f1279bc6a3787317b8e6252f468605cad93489a5b400218569c3d58624eea`
- `core/x86.tab`: `66743ef5b540a00ac933537d3d56d0b56ab954ce5ae8d594bc2f9165e2b780d2`

A proposal for a model of AArch64 is in [`ARM-PROPOSAL.md`](ARM-PROPOSAL.md).

## Three observations, not one score

| Observation | At this revision | How to compare next time |
|---|---|---|
| How much language is there to read? | 5 pages, 2,430 words. (Revisions 1 to 3: 5 pages each; 2,160, 2,393 and 2,416 words.) Made by `pypy3 render-paper.py ODE.md ODE.pdf`, counted by `pdfinfo ODE.pdf`. | The same renderer, page size and type. Name any rule moved to another document: detail a reader still needs is not a reduction. |
| What does verifying cost? | The 14 kept proofs of the table below: 35,174 million retired instructions on x86-64. The verifier has not changed since the count. | The same 14 jobs. Give the inputs' hashes, the machine's role, the retired instructions and the elapsed time separately. |
| Who relies on what, for what? | The routes below. None was added or removed since revision 1. | List dependencies added and removed, new alternatives, and dependencies that were independent and now coincide. |

The report is a design draft, not a grammar or a machine specification. For an audit the instruction meanings, the encodings and the full contracts still have to be read. The page count is not the size of Bob's reading list.

## The verification basket

Each of 14 jobs gives `odeverify` a statement made from the repository's objects and contracts, and the proof kept in `proof-core/proofs/`. Every job ended `shown`. The statements and proofs had the same digests on both machines.

Retired instructions are user-space instructions counted by `perf stat`, the least of 5 runs, on an x86-64 Linux work machine (Threadripper PRO 7975WX). They are the measure to compare. The times are medians of 11 runs on that machine and on an Apple M6. Both machines are shared and no lock was held, so the times show the order of magnitude and no more.

| Job | Statement (bytes) | Proof (bytes) | Retired instructions (millions) | Time, x86-64 (ms) | Time, Apple M6 (ms) |
|---|---:|---:|---:|---:|---:|
| `ode_sum` (with `ode_third`) | 465 | 26 | 19.22 | 3.69 | 3.62 |
| `ode_equal` (with `ode_common`) | 2,262 | 723 | 29.23 | 4.31 | 3.78 |
| `ode_adler32` | 2,493 | 2,967 | 42.80 | 5.07 | 4.31 |
| `ode_adler32_blocks4` | 6,722 | 22,656 | 404.05 | 27.42 | 23.69 |
| `ode_varint` | 1,463 | 453 | 39.30 | 5.52 | 4.43 |
| `compress_avx512` | 9,046 | 131 | 58.82 | 6.28 | 5.12 |
| `compress_sse41` | 9,512 | 137 | 67.18 | 7.01 | 5.52 |
| `b3l_node_out` (with 2 kernels) | 13,031 | 306 | 101.60 | 9.27 | 7.00 |
| `b3l_pad` | 8,129 | 451 | 36.31 | 4.98 | 3.91 |
| `b3l_chunk_node` (with 3 called functions) | 17,376 | 6,107 | 2,443.70 | 162.22 | 162.70 |
| `p16` | 27,006 | 2,361 | 2,082.77 | 136.31 | 109.11 |
| `p32` | 78,240 | 4,178 | 9,759.74 | 665.32 | 561.13 |
| `k32` | 78,858 | 4,331 | 9,600.23 | 651.60 | 548.04 |
| `quad32` with `p32` | 84,641 | 4,193 | 10,489.03 | 739.67 | 602.18 |
| **All 14** | **339,244** | **49,020** | **35,173.96** | **2,428.65** | **2,044.54** |

## Reliance sets

**Conclusion A:** acceptance by the mathematical verifier implies that the modeled function meets the modeled contract. The current theorem is `Ode.verify_all_sound`; it assumes `Linked`, which relates the programs in its world to the instructions given to the verifier. The separate `Ode.verify_all_trace` theorem states what two executions have in common. A proof of either theorem about a different machine or a different contract would not answer the same question.

| Reader and route | What is needed for A | What is available |
|---|---|---|
| Bob, via Lean | Bob must recognize the theorem he means and the definitions it names. He relies on a way of validating its proof, including the axioms used. If he already relies on Lean4Lean for that purpose, count it in the full set, not as an entirely new cost. | The Lean theorem exists. Successful independent replay of this theorem by Lean4Lean is not a result we have. |
| Barry, via Metamath Zero | Barry would need a statement about the same verifier, a proof accepted by the kernel he knows, and grounds for identifying its statement with A. | A possible route. No such proof is supplied. |
| Brenda, by reading | Brenda can examine the machine, contract semantics and verifier rules, including the arithmetic rule, and decide whether each acceptance step is sound. This route depends on her own reasoning, not on a Lean proof. | The definitions and rules are available. Whether this is less work for Brenda than learning a proof kernel is her decision. |
| A second verifier written in Ode | For agreement to add independent evidence, identify the components shared by both implementations, particularly readers and machine semantics. Self-verification alone does not break the circle. | Proposed, not available. Test 4 below is a first exercise toward it and is evidence for nothing yet. |

**Conclusion B:** a particular binary, as loaded on a real processor, meets the contract the reader selected. None of the routes to A by itself yields B. Today the additional dependencies include reading the binary, decoding its instructions, binding call targets and constants, parsing the contract, reading the verifier input, running an executable that implements the mathematical verifier, loading the intended program, and how accurately the machine model describes the processor for the property in question. For example, an error in a decoder shared by two otherwise independent verifiers could give them the same wrong instruction list. The maker's compiler and proof search need not be correct for B if the actual binary is what gets verified.

A reader may separately judge whether the selected contract meets a practical need. Matching a vague intent is not a theorem about bytes. Keep dependencies for A, for B, and for that judgment on separate lines.

## What exists today

The x86-64 verifier covers 8 of the 14 functions of the Ode hash and 1,470 of its 3,062 instructions. That is not a proof of the production library or of the whole Ode hash. In the small `ode_sum` example the contract says `returns 14` with a stack budget of 16 bytes, and the proof file is 12 bytes (`for ode_sum` and a newline); the rules, the object code, the contracts and the other functions' proofs are not in those 12 bytes. `ode_quad32` fills a table of 32 addresses and calls a kernel through its contract; its stack budget is 6,432 bytes.

The frame notation, the choice of inlining at each use, the finer return rule, a second processor and a verifier written in Ode are proposals. None is in the repository's tools.

## The trial

The trial took two programs (a step of the hash, a piece of the verifier) and two processors (x86-64, AArch64), as far as today's tools and a prototype front end reach. Its programs and result files are kept outside this repository for now; they are to be added under `paper/trial/` so that every figure below can be made again.

Four words are used exactly:

- **Shown:** `odeverify` printed `shown` for a statement and a proof file.
- **Refused with a proof:** `odeverify` printed `refused` for a statement and that proof file. A sound verifier refuses a false statement whatever the proof; one refusal does not demonstrate that.
- **No proof found:** the prover gave up. The prover is relied on for nothing, so this is not a verdict.
- **Run:** the code was executed on a processor and its results compared with a model written for the test, on the inputs named. A run is a test, not a proof.

Ode has no model of AArch64. Everything said of AArch64 below is a run.

### Test 1: one step of the hash, written three ways

The step is `d := (d ^ a) ror 16` in every 32-bit lane. A function applies it N times, the two registers changing roles each time, for N = 1, 4, 16 and 56 (seven rounds of BLAKE3 have 56 G functions).

On x86-64 with AVX-512 (16 lanes), with today's `odec.py` and verifier:

- The source that writes the two instructions out and the source that uses a `def` text macro give the same object file, byte for byte, at each N. The code is 35, 74, 230 and 750 bytes: 13 bytes a copy (`vpxord` 6, `vprord` 7). clang gives the same code bytes for the assembly that `odec.py` prints.
- Each function is shown. Its proof file is its name alone (16 or 17 bytes): the function has no loop and no call, so the verifier needs no hint. The verifier's work grows with the code: 19.54, 20.87, 26.31 and 44.81 million retired instructions, about 0.46 million a copy.
- Each object, run on 16 inputs, agrees with a Python model of the formula in all 16 lanes.
- Two false controls at N = 4, both in the third step, which makes the output: a rotate by 15 in place of 16, and the step without its `vpxord`. Each differs from the model when run. Each is refused with the proof of the correct function ("the specification's words are not followed on the terms the function made"), and no proof of either is found.
- One true statement is refused: the fourth step without its `vpxord`. That step writes a register nothing reads afterwards, so the function still meets the contract, and it agrees with the model when run. It is refused with the same words. The specification written for the test names the fourth step's value in a `let` that nothing uses, and the verifier follows every `let`. Without that line the same function is shown.

On AArch64 with NEON (4 lanes), assembled by clang and run on an Apple M6:

- `eor` and `rev32`, 8 bytes a copy: 24, 48, 144 and 464 bytes for the four N. The results agree with the Python model on 16 inputs, and with the first four lanes of the x86-64 run on the one input compared.
- At N = 3 without the last `rev32`, the run gives `9ae1faa3` where the model gives `faa39ae1`.
- A rotate by 12 has no single NEON instruction. Two sequences were run and agree with the model: `eor`, `ushr`, `shl`, `orr` (16 bytes) with a scratch register, and `eor`, `ushr`, `sli` (12 bytes) into another register. With the scratch register the same as the destination, the first sequence still assembles, and all four lanes come out wrong (`99e00000 00000000 fff00000 00000000` for `897cc99e 00300000 ffffffff 00180000`). Text substitution has no rule that could refuse this; the prototype of Test 3 refuses it at the line of the use.

A call in place of the inline copies, on x86-64:

- A helper that takes `d`, `a` and the result through memory, called N times, takes 121, 187 and 451 bytes (caller and helper) at N = 1, 4 and 16, against 35, 74 and 230 inline.
- These callers are not shown. No proof is found, and the verifier's last message is "sixty-four bytes written to what is no run given to write". Reading `Core.lean`: the store `vmovdqu32` has a rule only for memory that the contract gives to write, and the frame takes the aligned store `vmovdqa32`. The callers were not written again with an aligned frame, so it is not known whether they would then be shown.
- A call that passes its operands in registers was not built or measured.

### Test 2: a piece of the verifier

The verifier's arithmetic rule ends a contradiction by finding every coefficient zero. `ode_all_zero(xs, n)` returns 1 if the `n` bytes at `xs` are all zero, and 0 if not. Its contract says `returns all_zero(xs)`, `trace depends on xs, n` and `stack 0`.

- A scan that leaves at the first byte that is not zero (x86-64, 40 bytes) is shown. The statement is 770 bytes and the proof 463 bytes; verifying takes 21.57 million retired instructions. The loop's invariant is `all_zero_from(xs, i) == all_zero(xs)` with `i <= n`.
- The same code against a contract whose trace may depend on `n` alone is refused with the proof above: "a jump on a flag that may depend on a secret: which instructions run would depend on it". No proof of it is found.
- A scan that stops one byte early returns 1, when run, for bytes of which only the last is not zero. No proof of it is found.

Three things are true and not shown today:

1. A scan that ORs every byte into one register and tests it once at the end (46 bytes; it passes the same runs). No proof was found with the invariant tried: the register is zero exactly where the bytes so far are all zero. Reading `symOrKnown` in `Core.lean`: of `x | y` the verifier knows that it is no less than `x`, no less than `y`, and below 2^8, 2^16 or 2^32 where both are. Where facts say that both are zero, nothing lets it conclude that `x | y` is zero. That reading was not put to a test by adding a rule.
2. A scan of 32-bit words (41 bytes on x86-64; 36 bytes on AArch64 with `ldr w2, [x0], #4` and `cset`; both pass their runs, with a last word that alone is not zero among them). The verifier has no rule for a load of four bytes from a run of bytes of variable length ("a read of a run of bytes that is not one byte: not here yet"). The contract given was a stand-in, written only to reach that message.
3. A function with a second `ret` after an early return. By its design the reader of a function (`kcheck/kdecode.py`) stops at the first `ret`. Such a scan has 14 instructions and its statement has 12. With the proof of the scan that has one `ret` it is refused ("no instruction at 36"), and no proof is found. So the scan that is shown ends in one `ret` that both paths reach.

Exact arithmetic. The rule adds multiples of inequalities over the integers. A model of the rule in C with wrapping 64-bit arithmetic accepts two derivations that are false. Adding `0*x + 2^62 >= 0` to itself gives a constant that wraps below zero. Doubling and adding `2^62*x >= 0` and `2^62*x - 1 >= 0` gives a coefficient that wraps to zero and the constant -2. With every product and sum tested for overflow, both are declined, and two correct derivations (one needs a negative constant divided and rounded down) are still accepted. The tested code is 29 bytes on x86-64 (`imul` and `add`, each followed by `jo`) and 60 bytes on AArch64 (`mul` with `smulh`, `adds` with `b.vs`); both were run. `imul` and `jo` are not rows of `core/x86.tab`, so Ode cannot verify the x86-64 code today.

### Test 3: a prototype front end

`ode2.py` (420 lines of Python) reads a source in the notation of `ODE.md` sections 4 and 5. For x86-64 it hands plain instructions to the existing assembler (`core/asm.py`); for AArch64 it prints assembly for clang. It has a `target` line; names for registers; a `frame` of named fields, with every slot tested against the field's count; `inline fn` with register parameters of a stated class, `distinct(a, b)` and a `changes` list; `for` over a constant range, with arithmetic on the loop's variable; `:=` for moves, loads and stores (x86-64 only); and a `place` written at the loop it describes, whose offset in the code the tool works out. It chooses no register and adds no instruction.

- `ode_quad32`. The kept source has 156 lines, 135 of them code. Its code writes `[rsp + N]` 73 times and the frame's size twice, and it writes its 64 stores into the table one by one: today's `for` substitutes text, and the assembler takes no arithmetic in an operand. In the prototype's notation the function has 67 lines, 56 of them code, and writes no stack offset and no frame size. Its object file is `proof-core/examples/quad/odequad32.o` byte for byte, and it is shown with the kept proof.
- The repository's Ode sources have three `def` text macros: `g4` of the 16-way kernel and the two `g` of the one-block kernels. Written as inline functions, all three give the code that `odec.py` gives for the macros: the 16-way kernel's 2,768 bytes of code and 16 bytes of constants, and the whole object files of the two one-block kernels (373 and 437 bytes of code).
- The 16-way kernel's invariant, written at its loop: the tool works out the offset `+0x9a7`, which is the kept one. The object is shown with the kept proof, and the prover, given the place the tool printed, finds the same 2,361 bytes of proof again.
- `ode_all_zero` with its invariant at the loop: offset `+0x2`, shown, proof 463 bytes. With a `nop` put before the loop the tool gives `+0x3`, the invariant's text is the same, and the function is shown again.
- AArch64: three small functions (four copies of the step of Test 1; the rotate by 12 with `distinct`; the scan of words) become assembly that clang assembles and that passes its runs on an Apple M6.
- Nine faults are refused before anything is assembled, each with the number of the line the fault is on: a frame slot past its count, a slot below zero, a view of a field past its end, a field that is not declared, a scratch register that is the destination (AArch64), a general register where a vector register is asked, and a write to a register that `changes` does not list (x86-64, AArch64, and inside `g4`).

What the prototype does not do. An `inline fn` has no contract of its own: each copy is verified as part of the function that uses it. The `changes` rule reads the first operand of each instruction as text, not the instruction table, so it does not see a second register or a flag that an instruction writes. A frame's slots are offsets from `rsp`; nothing tests that `rsp` is where the frame takes it to be.

### Test 4: a first exercise toward a verifier written in Ode

`v1_verify.ode2` (1,384 lines in the prototype's notation; 8 functions, 1,118 instructions, 4,726 bytes of code) reads the statement and proof files that `odeverify` reads. It does not implement the verifier's rules. It knows eight instruction forms (`push`, `pop`, the address of a constant, a load of four bytes of a constant, a move and an add between registers, `call`, `ret`), follows a function that has no branch, works with constants, and compares the number returned and the stack used with the contract. It has no proof of soundness, and no argument for one is written. Its working memory comes from the caller (8,192 bytes); given less, it refuses at entry.

- It approves the four true cases tried (`ode_sum`, `ode_twice`, and the two changed and still true cases of `proof-core/test_sum.py`). It refuses the 22 false or malformed cases tried: the 8 changed sources and 5 changed contracts of `test_sum.py`, and 9 malformed statements, proofs and sizes of working memory.
- Every instruction of it is a row of `core/x86.tab`: the table's reader reads every byte of the eight functions.
- For scale: on `ode_sum` its whole process retires 0.14 million instructions, where `odeverify` retires 19.22 million. The two do different work, so this compares no speeds.
- Two of its helpers are shown by `odeverify` against contracts written for them: `v1_hex_nibble` (22 instructions, proof 300 bytes) and `v1_mem_eq` (17 instructions, proof 532 bytes). For each, a false contract is refused with the proof of the true one, and no proof of it is found.

## What comes next

1. Zooko's choice of a model for AArch64 ([`ARM-PROPOSAL.md`](ARM-PROPOSAL.md)), before the first function is verified there.
2. Zooko's word on the rule for a returned number (`ODE.md` section 3), before the formal model changes.
3. The trial's programs into `paper/trial/`, with the same functions in each notation as files to read.
4. The five things the trial found that the verifier does not do, each to be weighed before it is built: conclude that `x | y` is zero where both are; load more than one byte from a run of bytes; store a vector to the frame with `vmovdqu32`; read a function past its first `ret`; pass over a `let` that nothing uses.
5. The front end's forms into `lang/odec.py`, once the shape of a second target is decided; the three `def` macros go in the same change.

After each change, return to this sheet and the report together. A proof file can shrink while the verifier gets harder to understand; inlining can make a loop faster while more instruction lines compete in a caller. None of the three observations stands in for the others.
