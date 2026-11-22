# Ode: a language for code that comes with a proof

Design report, revision 4 for discussion, 22 November 2026. This describes the intended language, not a release. The companion review gives implementation status, experimental measurements, and reliance sets. Example source that uses the new notation is a proposal.

## 1. What the reader gets

Suppose you need a routine that hashes a message without branching on the key. An example digest helps you recognize the hash. It tells you nothing about branches. An Ode contract can say both what the result is and what may influence the branches and memory addresses. You choose the contract. The maker supplies the binary and a separate proof. You need not read the source to verify the binary against that contract.

A specification defines values. A contract says what a function requires and what it does. Ode source selects the instructions that do it. A proof supplies information the verifier can check. These have different readers: you may care how BLAKE3 combines two child nodes without caring which register contains the left child. The register matters to the person writing the code. The verifier must check the connection.

## 2. Values and names

In a specification, an ordinary number is a nonnegative integer of any size. A word has 32 bits; adding words wraps modulo 2^32. A counter has 64 bits. A list has a length and numbered elements starting at zero. A byte is a number below 256. A record has named fields. A condition is true or false. An address and the contents at that address are not the same value.

`xs[a .. b]` includes a and excludes b. `words(xs)` reads groups of four bytes, least significant first; `bytes_of` does the reverse. Out-of-range indexing, an ordinary subtraction below zero, and a search with no result do not silently produce values. A definition may explicitly fail with a reason. A proof using an expression must establish that it has the required value on the path in question.

`const` gives a value a name; `let` names part of a definition. Neither writes memory. Equations may define a sequence by its first element and its next element, or define a tree in terms of smaller trees. A definition need not describe how the implementation computes its result. The reader may evaluate it on examples, but an example is not a proof. The ability to prove arbitrary mathematics is neither required nor forbidden.

`:=` means store, in a register or in memory. `==` means equality and has no effect on its operands. In this draft a bare `=` introduces a definition, as in `let size = 64`; it is not a comparison or an instruction. A machine operation has no implied mathematical precision beyond the instruction the coder selects.

A full contract includes every definition it uses, directly or indirectly. The maker's names are not its identity. In the intended exchange format the tool replaces chosen names with local identifiers before hashing the full text with BLAKE3. A glossary associates a person's words with those identifiers. A contract names no implementation: two binaries can meet the same contract. A different hash means different text, not necessarily a different promise. To decide whether one promise suffices for another, reason about the contracts, not their hashes.

## 3. What a function promises

If the caller meets the preconditions, the function returns, its result satisfies the postconditions, and its effects stay within the contract. There is no promise for a call outside the preconditions. For example, `quad32` computes a BLAKE3 parent from two blocks. Here is the functional part in proposed notation; `child` abbreviates the specification's compression of one parent block, not a call in the binary.

```
contract quad32(out: cv, a: block, b: block, kf: keyed) {
    requires no_overlap(out, a, b, kf)
    ensures out == parent(kf.key, kf.flags, child(kf,a), child(kf,b))
}
```

Here `cv` represents eight words and `block` represents 64 bytes. The kind says how numbers are represented in memory; a register declaration in the code cannot change that meaning. In an output equation, the left side denotes the bytes on return. Names in the expression on the right denote the arguments at entry. `returns` specifies a returned number. `writes` permits a change without promising a particular result. Bytes outside the permitted writes keep their values.

A piece of memory is a range of bytes together with permission to read it or to read and write it. `no_overlap` means that no two of the named ranges have a byte in common. A caller can lend part of a piece for a call, but not more bytes or greater permission than it has. On return it may use the callee's promise about the lent bytes and retain what it knew about the rest. Stack space belongs to the call; an address into it does not outlive it. Read-only constants belong to the loaded program, not to an individual function's argument list. No permitted write may change them or the code.

The contract need not repeat machine details that the tool can derive and check. But hiding them from the usual display must not hide an obligation from the caller. For the existing x86 implementation of `quad32`, the caller needs AVX-512 and a stack budget of 6,432 bytes including calls. A caller with only 4,096 bytes cannot use that implementation on this contract. A summary that displays only the digest equation must not answer that it can.

`trace depends on` names inputs, besides the permitted addresses, that may influence which instructions run or which addresses they touch. An omitted input may still affect the result. In particular, `quad32` needs no permission to branch on the key merely because the result uses it. This describes an architectural trace, not elapsed time, speculative execution, or every observation a real processor permits.

Proposed return rule: if a contract hides an input from the trace, a caller must treat its returned number as possibly depending on that input; it may use the number as data but not directly as a branch condition or an address. If the contract hides no input, the verifier still checks that the result does not depend on other hidden entry state before allowing the caller to use it in the trace. This conservative rule does not promise that every permitted trace dependency actually occurs.

## 4. Choosing instructions

A source file names its target. A raw instruction is valid Ode. A higher-level form denotes either a specified instruction or a visible sequence chosen by the coder. The listing gives the instructions, bytes and source location. If the requested form cannot be encoded with the stated registers, the compiler reports that fact. It does not insert a move, spill a register or substitute a slower sequence in order to succeed.

For example, name two distinct vector registers `d` and `a`. To compute `d := (d ^ a) ror 16` independently in each 32-bit lane, the coder can select these expansions:

```
x86-64, 16 lanes          AArch64, 4 lanes
vpxord zmm0,zmm0,zmm1     eor   v0.16b,v0.16b,v1.16b
vprord zmm0,zmm0,16       rev32 v0.8h,v0.8h
```

The Arm instruction exchanges the two halfwords of each word: specifically for 16 bits, that *is* a rotate. For a 12-bit rotate, x86-64 still uses two registers (`vpxord` and `vprord`), while the NEON sequences tried so far use a third (`eor`, `ushr`, `shl`, `orr` in place, or `eor`, `ushr`, `sli` into a new register). Nothing here says the two targets use the same lane count or the same number of registers. The word equation is common; lane counts, scratch registers, and instruction selection are local to the implementation. The coder names each scratch register, and where two registers must differ the tool refuses, at the source line, a use that gives them the same one.

A frame declaration names pieces in order with sizes and alignments. Bounds and alignment statements are proof obligations, not permission to read extra bytes. In `quad32`, the first 256 bytes of the x86 frame hold 32 eight-byte addresses. An array of 32 results, each 32 bytes, follows. A source-level store to `table[i]` must land inside that first piece; writing slot 32 would instead overwrite a result. The error should name the slot, the declared bound and the source line.

At a loop, the coder writes the invariant where it must hold. For a loop that has consumed k blocks of 64 bytes, an invariant might say that the offset equals `64 * k` and that a register contains the specification's result after k blocks. The verifier must establish it on entry and after each iteration, show progress toward exit, and use the exit condition to derive the result. The compiler supplies the instruction location; the coder does not maintain a second copy keyed by an offset in yesterday's binary.

## 5. Calls, inline uses and advice

A call between Ode functions need not use C's register assignments. The coder selects where inputs and results go; the tool checks which registers and bytes can change. Other registers need no save and restore merely because a C compiler would expect it. If code uses x86 `call`, the processor writes a return address to the stack. If it uses Arm `bl`, the processor writes the link register. The respective proof must account for that effect. Neither instruction dictates the interface between two Ode functions. Calls to and from other languages use an adapter wherever their conventions differ.

At a use site the coder selects a call, a tail jump when its conditions hold, or an inline body. Using a body inline emits its instructions at that site; it does not emit a call and return. The verifier must approve those actual instructions with the actual registers. For reasoning after the use the caller gets the contract, not an accidental property of that copy. A different encoding can require different proof bytes without changing the caller's logical argument.

An inline function is meant to replace the text macro. It states the class of each register it takes, which of them must differ and which it changes, and the tool refuses a use that breaks one of these at its source line. It carries a contract, from which the caller reasons as after a call. A text macro can do none of this: on AArch64 a rotate by 12 written with its scratch register equal to its destination assembles and computes wrong values. An inline use emits the body's instructions and nothing more, so it costs no byte that the macro would not. The loop form `for`, which repeats lines over a constant range, does a different job and stays. Whether a call or inline copies take fewer bytes depends on how the operands are passed and how often the body is used; the coder chooses, and the listing shows the bytes of either.

Advice is not semantics. With a final layout the tool can count instruction bytes and, for a given line size, identify the lines a loop occupies. A profile may say which paths ran; a timing run may say one variant was faster. Neither proves that a line will miss in cache. If a precondition proves the block count is one, a tool may offer a source edit removing loop control and show its bytes and proof. If it merely observes that the count is usually one, it may not delete the other case. Ignoring advice must not change the build.

## 6. Proofs and verdicts

One tool compiles and helps produce the proof. It may copy facts from source, search for a proof, or accept a hint written by the coder. Its last step runs the ordinary verifier. Bob's verdict does not depend on which of those produced an item. The verifier reads the next item from the proof file; a name in a coder's glossary may stand for a fact number, but does not establish that fact.

Consider the verifier itself as the second Ode program. One of its arithmetic rules checks a step built from two inequalities already known to hold. For example, `x - 1 >= 0` and `n - x >= 0` imply `n - 1 >= 0` by addition. The proof identifies the two rows and their multipliers; it cannot invent either premise. The existing rule also permits division by a positive integer that divides every variable coefficient exactly, rounding the constant down (floor division, not hardware truncation toward zero). It is a rule about mathematical integers. A machine implementation must prove that its arithmetic is exact or detect overflow and decline; wraparound in 64-bit signed arithmetic can otherwise forge a contradiction from true rows. Checking signed 64-bit overflow also differs by target: x86-64 `imul` and `add` set the overflow flag directly for `jo`, whereas AArch64 checks `mul` with `smulh` against sign extension and checks `adds` with `b.vs`.

At the end of a contradiction proof, every coefficient must be zero and the constant negative. This gives a small first component for the two-target trial: compare a sequence of coefficients with zero. An early-exit scan branches on the first nonzero entry and therefore places the array in `trace depends on`. In a representation using one word per coefficient, a branchless scan can OR the words into an accumulator; at the loop head that accumulator is zero exactly when the consumed prefix contains only zeros, and AArch64 `cset` converts the final test to 0 or 1 without branching on data. Both targets can implement this contract with a load, an OR, and explicit loop control. The present verifier has no rule for a word-sized load from an array of variable length, so it cannot yet show the word scan. Supporting arbitrary-size coefficients additionally requires a representation and a proof about it; the word scan alone is not a verifier for general rows.

The verifier takes the contract, binary and proof as separate inputs. Success means that the function meets that contract under the stated machine and loading conditions. An unknown instruction, a step that does not follow, or insufficient work space cannot yield success. A refusal is not evidence of a wrong program. To report a false contract, give an allowed input and an execution that contradicts a specific clause.

A verifier implemented in Ode has the same obligation. Demonstrating that it reads a small proof correctly, proving its functions stay within their buffers, and proving that it never approves a false statement are three different achievements. Even the third, verified solely by that same verifier, is not an independent foundation. The companion table says which routes to confidence are available and precisely what each establishes.
