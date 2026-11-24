// The Ode Language Report — Revision 8 (November 2026)
// Co-designed prose, typography, and vector figures in one visual grammar:
//   - Niklaus Wirth's structural discipline and conciseness
//   - Edward Tufte & Robert Bringhurst's asymmetric margin grid, quiet hairlines,
//     small multiples, and restrained two-ink palette
//
// Build:
//   pypy3 paper/make_figures.py
//   typst compile paper/ode.typ paper/ODE.pdf

#let ink      = rgb("#1C1E21")
#let slate    = rgb("#5B6470")
#let muted    = rgb("#7D8590")
#let rulecol  = rgb("#CFC9BC")
#let accent   = rgb("#9E2A2B")
#let ivory    = rgb("#F7F5F0")
#let blush    = rgb("#FBF2F1")

// Asymmetric Tufte grid on US Letter (8.5in x 11in):
//   left margin  = 0.85in
//   main column  = 4.50in  (~68 characters in 10.0pt Palatino)
//   gutter       = 0.35in
//   margin notes = 1.95in
//   right edge   = 0.85in
//   full span    = 6.80in  (main + gutter + margin)
#set page(
  width: 8.5in,
  height: 11in,
  margin: (top: 0.88in, bottom: 0.88in, left: 0.85in, right: 3.15in),
  header: context {
    let pg = counter(page).get().first()
    if pg > 1 {
      let on_page = query(heading.where(level: 1)).filter(h => h.location().page() == pg)
      let prev = query(selector(heading.where(level: 1)).before(here()))
      let title = if on_page.len() > 0 {
        on_page.first().body
      } else if prev.len() > 0 {
        prev.last().body
      } else {
        [Ode]
      }
      block(width: 6.80in, below: 0pt)[
        #set text(font: "Palatino", size: 7.9pt, fill: slate, tracking: 0.08em)
        #grid(
          columns: (1fr, auto),
          [#upper[Ode · Language Report]],
          [#emph(title)],
        )
        #v(3pt)
        #line(length: 100%, stroke: 0.45pt + rulecol)
      ]
    }
  },
  footer: context {
    if counter(page).get().first() > 1 {
      block(width: 6.80in)[
        #line(length: 100%, stroke: 0.4pt + rulecol)
        #v(4pt)
        #set text(font: "Palatino", size: 8.1pt, fill: slate)
        #grid(
          columns: (1fr, auto),
          [#text(size: 7.6pt, fill: muted)[Revision 8 · November 2026]],
          [#counter(page).display()],
        )
      ]
    }
  },
)

#set text(
  font: "Palatino",
  size: 9.9pt,
  fill: ink,
  lang: "en",
)

#set par(
  justify: true,
  leading: 0.66em,
  spacing: 0.90em,
  first-line-indent: 0pt,
)

#set heading(numbering: "1.1")

#show heading.where(level: 1): it => {
  v(1.35em, weak: true)
  block(breakable: false, width: 6.80in)[
    #set par(justify: false)
    #if it.numbering != none [
      #text(fill: accent, size: 12.0pt, weight: "bold")[§ #counter(heading).display()]
      #h(0.45em)
    ]
    #text(fill: ink, size: 12.8pt, weight: "bold")[#it.body]
    #v(3pt)
    #line(length: 4.50in, stroke: 0.55pt + rulecol)
  ]
  v(0.50em, weak: true)
}

#show heading.where(level: 2): it => {
  v(1.00em, weak: true)
  block(breakable: false)[
    #set par(justify: false)
    #if it.numbering != none [
      #text(fill: accent, size: 10.0pt, weight: "semibold")[#counter(heading).display()]
      #h(0.4em)
    ]
    #text(fill: ink, size: 10.4pt, weight: "bold")[#it.body]
  ]
  v(0.32em, weak: true)
}

#show raw.where(block: false): it => text(font: "Menlo", size: 8.0pt, fill: ink)[#it.text]

// --- Co-Designed Structural Primitives ---

#let fullwidth(body) = block(width: 6.80in, breakable: false, above: 0.95em, below: 0.95em)[#body]

#let fullwidth_break(body) = block(width: 6.80in, breakable: true, above: 0.6em, below: 0.6em)[#body]

// Paragraph locked side-by-side with its Tufte sidenote (mathematically collision-free).
#let with_note(note, above: 0.90em, body) = block(width: 6.80in, breakable: false, above: above, below: 0.90em)[
  #grid(
    columns: (4.50in, 0.35in, 1.95in),
    align: (top, top, top),
    [#body],
    [],
    [
      #set par(justify: false, leading: 0.54em, spacing: 0.45em)
      #set text(font: "Palatino", size: 7.9pt, fill: slate)
      #note
    ],
  )
]

// Quiet rubric callout in the margin with a Venetian-red small-caps header.
#let with_rubric(title, note, above: 0.90em, body) = with_note(
  [
    #text(fill: accent, weight: "bold", size: 7.4pt, tracking: 0.07em)[#upper(title)]
    #v(2pt)
    #note
  ],
  above: above,
  body,
)

// Clean code block: warm ivory ground + quiet left hairline, zero heavy boxes.
#let codeblock(lang_label: none, is_ocl: false, width: 100%, body) = {
  let bg = if is_ocl { blush } else { ivory }
  let bar = if is_ocl { accent } else { slate }
  block(
    width: width,
    breakable: false,
    fill: bg,
    stroke: (left: 1.4pt + bar),
    inset: (left: 10pt, right: 8pt, top: 6.5pt, bottom: 6.5pt),
    above: 0.65em,
    below: 0.80em,
  )[
    #if lang_label != none [
      #text(font: "Palatino", size: 7.1pt, fill: if is_ocl { accent } else { slate }, weight: "bold", tracking: 0.08em)[#upper(lang_label)]
      #v(2pt)
    ]
    #set par(justify: false, leading: 0.46em)
    #set text(font: "Menlo", size: 7.8pt, fill: ink)
    #body
  ]
}

// Co-designed full-width figure with crisp quiet caption.
#let fig(num, img_path, title, caption) = fullwidth[
  #image(img_path, width: 6.80in)
  #v(4pt)
  #set par(justify: false, leading: 0.53em)
  #text(size: 8.2pt, fill: accent, weight: "bold")[Figure #num.]
  #h(0.35em)
  #text(size: 8.2pt, fill: ink, weight: "bold")[#title.]
  #h(0.25em)
  #text(size: 8.1pt, fill: slate)[#caption]
]

// Bringhurst booktabs table helper.
#let booktable(columns: auto, align: left, header, ..rows) = {
  set text(size: 8.5pt)
  set par(justify: false, leading: 0.51em)
  table(
    columns: columns,
    align: align,
    stroke: (x, y) => (
      top: if y == 0 { 0.9pt + ink } else if y == 1 { 0.55pt + slate } else { none },
      bottom: 0.4pt + rulecol.transparentize(40%),
      left: none,
      right: none,
    ),
    inset: (x: 6pt, y: 4.8pt),
    table.header(..header.map(h => text(weight: "bold", size: 8.1pt, fill: ink)[#h])),
    ..rows,
  )
}

// ============================================================================
// TITLE OPENING (Page 1 — Full-Width Monograph Opener)
// ============================================================================

#block(width: 6.80in)[
  #text(size: 8.0pt, fill: accent, weight: "bold", tracking: 0.14em)[LANGUAGE REPORT & REFERENCE · REVISION 8]
  #v(4pt)
  #text(size: 26pt, weight: "bold", fill: ink)[Ode]
  #v(2pt)
  #text(size: 12.6pt, style: "italic", fill: slate)[A Language for Native Machine Code That Carries Its Proof]
  #v(8pt)
  #line(length: 100%, stroke: 0.9pt + ink)
  #v(5pt)
  #grid(
    columns: (1fr, auto),
    [#text(size: 8.4pt, style: "italic", fill: slate)["Make the promise small, keep the machine visible, and let the reader check the bytes."]],
    [#text(size: 8.3pt, fill: slate)[November 2026]],
  )
]

#v(0.75em)

#with_rubric(
  "Two meters",
  [This report serves both as a complete definition of Ode and as our first complexity meter: every language addition must earn its lines on these pages.],
  above: 0pt,
)[
  Suppose you need a fast cryptographic hash, parser, or memory routine compiled to native x86-64 or AArch64 machine code. You did not write it, and you do not wish to read three thousand lines of assembly or rely on a compiler you cannot inspect. Running a hundred test vectors confirms that the binary gives the right answers on those hundred inputs. It tells you nothing about the next input, nothing about out-of-bounds reads, and nothing about whether a branch inside the binary depends on key material.
]

Ode separates what a routine _promises_ from how it is _built_. The promise is a short, self-contained mathematical specification called a _contract_. The maker writes native machine instructions for each target processor and produces two files: the compiled object file and a separate proof certificate. You—the auditor, whom we call _Bob_—run a small verifier on the binary's actual bytes against the contract. You need not read the source code, and the verdict does not rely on the author, the compiler, the assembler, or the prover.

#fig(
  1,
  "figures/fig1-boundary.svg",
  "The boundary between maker and auditor",
  "Alice's workshop (left) compiles Ode source and searches for proofs, but Bob's verdict relies on none of it. Bob's reliance set (right, outlined in red) contains only the canonical contract he reads, the small verifier, and the processor instruction tables.",
)

This report describes Ode as it stands today: its specification language and nameless contracts (§2–§3), its unified two-target source notation (§4), its zero-overhead Ode-to-Ode calling conventions and verified tail calls (§5), its bundling and audit format (§6), measured performance on verified BLAKE3 and breadth routines (§7), its reliance sets and open frontiers (§8), and its complete surface grammar (Appendix A).

// ============================================================================
// SECTION 1: DESIGN PRINCIPLES
// ============================================================================

#pagebreak()

= Design Principles

Four decisions govern every construct in Ode. Whenever a proposed feature conflicts with one of them, the feature gives way.

#with_rubric(
  "Why reliance sets",
  [Following Mark S. Miller's discipline, we ask _who relies on which piece, and for which conclusion_, rather than treating all actors as sharing one boundary.],
)[
  *1. Minimize Bob's reliance set.*
  A maker wants fast proof search and convenient notation; an auditor wants as little code as possible between the contract he reads and the machine bytes he runs. Ode resolves that tension by splitting _proving_ from _verifying_. Everything clever—symbolic search, arithmetic heuristics, performance advice, source syntax—lives on Alice's side. Only a small deterministic verifier reads the compiled object bytes, checks every step of the proof file, and confirms that the contract covers 100% of executable code.
]

*2. Never hide the processor.*
High-level systems languages regularly insert hidden stack frames, silent register moves, or compiler rewrites that defeat both performance engineering and timing audits. In Ode, raw processor instructions are valid source statements. Higher-level forms expand in fixed, visible ways chosen by the coder. If a requested form cannot encode with the stated registers, the compiler reports the conflict at the source line; it never inserts a move, spills a register, or substitutes a slower sequence to make compilation succeed.

#with_note([
  Every contract is a _closed world_: anything not explicitly allowed—extra writes, extra stack bytes, other CPU features, or data-dependent branches—is refused.
])[
  *3. Closed-world contracts.*
  A contract states everything a routine may assume and everything it may do: which memory ranges it may read or write, how many bytes of stack it may use (including callees), which CPU extensions it needs, why its loops and recursion terminate, and what values may influence its execution trace. Bytes outside the permitted write ranges remain equal to their entry values.
]

*4. Two architectures from the start.*
Designing a language for one processor hides accidental assumptions inside the model. Ode targets both x86-64 (System V AMD64) and AArch64 (AAPCS64) from day one, under the same verifier and the same soundness theorems. Every contract is architecture-neutral: an x86-64 binary and an AArch64 binary implementing the same specification share the exact same contract text and the exact same 52-character content hash.

// ============================================================================
// SECTION 2: VALUES, SPECIFICATIONS, AND NAMELESS CONTRACTS
// ============================================================================

= Values, Specifications, and Nameless Contracts

A specification defines mathematical values without prescribing how a processor computes them. An auditor can read a specification as pure mathematics and test it on concrete inputs with `ode spec-test`, while the verifier proves that a compiled binary satisfies it for _every_ allowed input.

#block(breakable: false, width: 6.80in)[
  == Types and Partiality
  #block(width: 4.50in)[
    Specifications distinguish exact mathematical integers from fixed-width machine words and from memory addresses. The table below lists each specification type, its value domain, and its arithmetic rules.
  ]
  #v(6pt)
  #booktable(
    columns: (1.05in, 2.25in, 3.50in),
    ([Type], [Domain], [Operations and rules]),
    [`number`], [Nonnegative integers $0, 1, 2, dots$], [Exact arithmetic; subtraction below zero is an explicit failure, not wraparound.],
    [`byte`], [Integers $0 dots 255$], [Unsigned octet; slices `a[i]` of a `bytes` piece yield a `byte`.],
    [`word`], [32-bit unsigned integers], [Wrapping arithmetic modulo $2^32$; bitwise `&`, `|`, `^`, shifts, `ror`.],
    [`counter`], [64-bit unsigned integers], [Wrapping 64-bit counter (used for block and chunk counters).],
    [`bytes` / `list`], [Finite 0-indexed sequences], [`len(xs)`, `xs[i]`, slice `xs[a .. b]` (includes `a`, excludes `b`), `words(xs)` / `bytes_of(ws)` little-endian 4-byte conversion.],
    [`record`], [Named fields with fixed offsets], [Declared via `layout`; maps byte ranges to named fields (`nd.h`, `nd.block`, `nd.flags`).],
  )
]

#with_note([
  Explicit partiality avoids a classic formal-methods trap: `xs[i]` is never silently `0` when `i >= len(xs)`. Every proof using an expression must establish that it is defined on that path.
])[
  Two symbols keep mathematics separate from machine effects throughout Ode. Equality is written `==` (a pure predicate with no effect on operands), while storing into a register or memory is written `:=`. A bare `=` appears only where a name is bound to a definition (`const`, `let`, or `reg`).
]

Definitions are pure equations introduced by `const`, `def`, and `sequence`. A `def` body may bind intermediate names with `let` (each name bound at most once) and may declare explicit error cases with `fails REASON if COND`. A `sequence` defines a recurrence by its base equation `h[0] = E0` and step equation `h[b + 1] = E1`.

== Nameless Contracts and Content Identity

In ordinary software ecosystems, names are chosen by authors and are therefore an attack surface: a misleading function name or a subtle comment can steer an auditor's eye away from a weakened condition. Ode eliminates author-chosen names from the artifact Bob audits.

#with_rubric(
  "Base-32 digests",
  [All Ode contract and binary hashes are full 256-bit BLAKE3 digests encoded in 52 lowercase RFC 4648 base-32 characters (`a`–`z`, `2`–`7`), never truncated.],
)[
  An Ode contract has _no name_. When `ode canon` produces the canonical Ode Contract Language (`.ocl`) form, it performs four deterministic steps:
  + Removes all comments and normalizes whitespace.
  + Drops every helper `def`, `const`, or `layout` not reachable from the contract.
  + Replaces every chosen identifier with a numbered slot in canonical order of first mention (`f0`, `f1`, … for definitions; `a0`, `a1`, … for contract arguments; `p0`, `p1`, … for parameters).
  + Refuses any `calling` block or register name—hardware calling details never enter an auditor's `.ocl` contract.
]

The sole identifier of that contract is the 52-character base-32 BLAKE3-256 digest of its canonical `.ocl` text. Every exported linker symbol is derived directly from that digest (`ode_<52>`), and standalone `.ocl` files carry `<52>.ocl` as their filename. Whenever `ode audit` or `ode spec-test` reads a hash-named `.ocl` file, it hashes the contents and refuses if the digest does not match the filename. A personal _glossary_ maps slots back to readable words (`a0 -> "a"`, `f0 -> "all_zero"`), belongs to its reader, and is never hashed.

#fig(
  2,
  "figures/fig2-canon.svg",
  "From author's names to canonical content identity",
  "Running ode canon on the verifier building block all_zero strips comments, drops unreachable helpers, and numbers every identifier into a 14-line nameless .ocl contract whose BLAKE3-256 digest binds both the filename and the linker symbol.",
)

// ============================================================================
// SECTION 3: MEMORY, STACK, AND ARCHITECTURAL TRACE
// ============================================================================

= What a Contract Promises: Memory, Stack, and Trace

If a caller meets every `requires` clause on entry, a verified function is guaranteed to terminate, return cleanly, satisfy every `ensures` and `returns` clause, stay within its `stack` budget and `needs` CPU features, and produce an execution trace determined solely by its `trace depends on` clause. For inputs outside `requires`, the contract makes no promise.

== Memory Pieces, Disjointness, and Lending

Every pointer argument names a _piece_ of memory: a starting address, a length (fixed, such as `32 bytes` or `block`, or parameterized by another argument, such as `a: n bytes`), and an access permission. By default, every memory parameter is read-only. Mentioning a piece on the left side of `ensures p = E` or in `writes p` grants write permission for that piece alone.

#with_note([
  Why `no_overlap` instead of `apart`? Two adjacent buffers share no byte (`no_overlap`) even though they touch at their boundary. Naming the exact property prevents misreading.
])[
  The precondition `no_overlap(p1, p2, ...)` states that no two of the listed byte ranges have any byte in common. Because Ode uses explicit ownership lending across calls, a caller may lend either a whole piece or a contiguous sub-span (such as `nd.block`, bytes `32..96` of a 120-byte `node120` record) to a callee, provided it lends no more bytes and no greater permission than it holds. On return, the verifier updates the caller's knowledge of the lent sub-span with the callee's postcondition while preserving every proven fact about the remaining bytes of the caller's memory.
]

#fig(
  3,
  "figures/fig3-memory.svg",
  "Closed-world memory pieces, disjointness, and sub-span lending",
  "The caller holds pairwise disjoint pieces and lends only nd.block (read/write) and input (read-only) to b3l_pad_fast. Other fields of nd—h, t, blen, and flags—automatically retain their proven values across the call.",
)

Stack space is strictly call-local: a function may allocate up to its declared `stack N` bytes (which may be a formula such as `18688 + 384 * bits(len / 1024)` for recursive trees), may lend slices of its stack frame to callees, and must restore the stack pointer before returning. No address inside a stack frame outlives its call. Read-only program constants (`.rodata`) belong to the loaded program and may never be written.

== Architectural Trace (`trace depends on`)

When a binary runs, the processor executes a sequence of instructions and accesses a sequence of memory addresses. That sequence of instruction addresses and memory addresses is the function's _architectural trace_. An observer who measures execution time or cache-line activity learns information about this trace, not directly about values kept in registers.

#with_rubric(
  "Scope of the trace",
  [Ode proves architectural trace equivalence: identical instruction paths and memory addresses. It does not model speculative execution, power draw, or analog side channels.],
)[
  A contract's `trace depends on` line is a two-run noninterference theorem: _given any two valid calls whose listed trace expressions and pointer addresses agree, both runs execute the exact same sequence of instructions and touch the exact same memory addresses, regardless of how other inputs differ._
]

Consider two implementations of byte-array comparison returning `same(a, b)` (`1` if equal, `0` otherwise):
- An early-exit loop (`equal`) branches on the first differing byte `a[i] != b[i]`. Its trace reveals where the arrays first differ, so the verifier insists that its contract say `trace depends on a, b, n`.
- A branchless loop (`equal_ct`) folds byte differences into an accumulator without branching on any byte. Its trace depends solely on the array length, so the verifier approves `trace depends on n`—keeping both `a` and `b` out of the trace even though the returned number is computed from them.

Crucially, `trace depends on` may list _computed expressions_, not only raw inputs. A tag-checking function compares an incoming tag against an expected tag without branching on individual bytes, and then branches once to accept or reject. Its contract writes:

#codeblock(lang_label: "Value-based trace contract")[
```
contract verify_tag(want: n bytes, tag: n bytes, n: number) {
    returns same(want, tag)
    trace depends on n, same(want, tag)
    stack 0
}
```
]

Inside each function, a branch condition or memory offset may depend only on constants, entry addresses, and values computed from what _that function's own_ `trace depends on` line lists. A function whose contract specifies `returns E` places no extra trace burden on its return register; if a caller later branches on that returned number, the _caller's_ `trace depends on` line must allow what `E` is computed from (established by a `clear` proof step when an expression equals a listed trace value). For abstract return contracts (`returns r` with `ensures`), an optional `result depends on` clause states which inputs may affect `r`.

// ============================================================================
// SECTION 4: WRITING CODE — UNIFIED .ode SOURCE
// ============================================================================

= Writing Code: Unified `.ode` Source Across Two Processors

Every Ode program is written in one source file format (`.ode`). Each `.ode` file forms a _closed local namespace_—there is no implicit cross-file symbol merging. Every callable `fn` must declare its contract directly in its header, followed by one or more explicit processor implementation blocks (`for x86_64` and `for arm64`).

== Structured Notation Without Silent Rewrites

Ode gives the coder concise ways to avoid assembly tedium while preserving complete control over emitted bytes:

- *Register aliases* (`reg name = rdi`) bind readable names to concrete architectural registers inside a function body and its `place` invariants.
- *Structured stack frames* (`frame { buf: 64 bytes; saved: 1 * u64 }`) compute byte offsets (`frame.buf`, `frame.size`) and enforce declared alignments and bounds.
- *Checked inline templates* (`inline fn`) replace raw text macros. An `inline fn` declares the register class of each operand (`gpr`, `vec`), which operands must be distinct (`distinct(dst, tmp)`), and which registers it modifies (`changes tmp`). Passing the same register for destination and scratch is refused at the source line before a single byte is assembled.
- *Constant-range unrolling* (`for i in 0..8 { ... }`) repeats a fixed block over compile-time indices.
- *Inline loop invariants* (`place { name ... fact ... decreases ... }`) sit right at the loop head where the verifier checks them on entry and across every back-edge—never in a fragile side file keyed by yesterday's byte offsets.

#with_rubric(
  "Zero hidden instructions",
  [Replacing `idx := 0` with `xor ecx, ecx` (x86-64) or `mov x2, 0` (AArch64) yields byte-for-byte identical `.text`. Any form the processor cannot encode in the named registers is rejected loudly.],
)[
  Figure 4 illustrates the unity of one contract and two processors using a real verified routine from `proof-core/examples/verifier/`: `all_zero`, which scans `a[0 .. n]` and returns `1` if every byte is zero and `0` otherwise. Both processor bodies satisfy the exact same 14-line nameless `.ocl` contract with zero stack bytes.
]

#fullwidth[
  #block(
    fill: blush,
    stroke: 0.9pt + accent,
    inset: (x: 11pt, y: 7.5pt),
    width: 100%,
  )[
    #grid(
      columns: (auto, 1fr),
      align: (left, right),
      [#text(size: 7.4pt, fill: accent, weight: "bold", tracking: 0.08em)[SHARED CANONICAL CONTRACT (.ocl)]],
      [#text(font: "Menlo", size: 7.1pt, fill: accent)[BLAKE3: jbqyjqpese4s4cq35qxlhaevjvzuaqznquqw6mtlaqleluc25ika]],
    )
    #v(4pt)
    #set par(justify: false, leading: 0.44em)
    #set text(font: "Menlo", size: 7.45pt, fill: ink)
    ```
    def zero_from(a, i) { if i == len(a) then 1 else if a[i] != 0 then 0 else zero_from(a, i + 1) }
    fn all_zero(a: n bytes, n: number)  returns zero_from(a, 0)  trace depends on a, n  stack 0
    ```
  ]
  #v(5pt)
  #grid(
    columns: (1fr, 10pt, 1fr),
    [
      #codeblock(lang_label: "for x86_64  (System V AMD64 · 36 bytes)")[
        ```
        reg base = rdi, count = rsi
        reg idx  = rcx, res   = rax
        idx := 0
        place {
          name i = idx
          fact 0 <= i; fact i <= n
          fact all_zero(a) == zero_from(a, i)
          decreases n - i
        }
        @loop:
          cmp idx, count
          jae @yes
          mov rdx, base
          add rdx, idx
          movzx edx, byte ptr [rdx]
          cmp rdx, 0
          jne @no
          add idx, 1
          jmp @loop
        @yes:  res := 1; jmp @done
        @no:   res := 0
        @done: ret
        ```
      ]
    ],
    [],
    [
      #codeblock(lang_label: "for arm64  (AAPCS64 · 48 bytes)")[
        ```
        reg base = x0,  count = x1
        reg idx  = x2,  addr  = x3
        idx := 0
        place {
          name i = idx
          fact 0 <= i; fact i <= n
          fact all_zero(a) == zero_from(a, i)
          decreases n - i
        }
        @loop:
          cmp idx, count
          b.hs @yes
          add addr, base, idx
          ldrb w4, [addr, 0]
          cmp x4, 0
          b.ne @no
          add idx, idx, 1
          b @loop
        @yes:  x0 := 1; b @done
        @no:   x0 := 0
        @done: ret
        ```
      ]
    ],
  )
  #v(2pt)
  #set par(justify: false, leading: 0.53em)
  #text(size: 8.2pt, fill: accent, weight: "bold")[Figure 4.]
  #h(0.35em)
  #text(size: 8.2pt, fill: ink, weight: "bold")[One contract, two processors (small multiples).]
  #h(0.25em)
  #text(size: 8.1pt, fill: slate)[The top band holds the shared semantic contract. Below it, the x86-64 and AArch64 implementations share the same `place` invariant while choosing native registers and encodings. Both verify `shown` under the same Lean-proved verifier and share the exact same 52-character contract hash.]
]

// ============================================================================
// SECTION 5: CALLS BETWEEN ODE FUNCTIONS
// ============================================================================

= Calls Between Ode Functions

C and Rust callers expect the platform C calling convention: System V AMD64 on x86-64 (`rdi..r9` in, `rax` out, `rbx/rbp/r12..r15` preserved) and AAPCS64 on AArch64 (`x0..x7` in, `x0` out, `x19..x29` and vector registers `v8..v15` preserved). Every exported (`STB_GLOBAL`) Ode entry point strictly enforces this C ABI—including `v8..v15` preservation on AArch64—so legacy code can call Ode safely without adapters.

Inside an Ode program, however, forcing internal helper calls (`STB_LOCAL`) through C's register conventions wastes dozens of instructions per call on short inputs. Ode provides three complementary mechanisms for zero-overhead internal calls, all proved sound in Lean 4 without adding a single row to the processor instruction tables.

== Custom Internal Calling Conventions (`calling`)

An internal helper may declare a `calling` block inside its target block, stating the exact input register for each parameter, the return register (`out`), and the exact general-purpose and vector registers it promises to preserve (`preserves`, `preserves_vec`):

#with_rubric(
  "Soundness invariants",
  [`odeverify` refuses any malformed convention directly: out-of-range registers, duplicate inputs, `rsp`/`sp`/`x30` as parameter or return registers, or a return register also listed in `preserves`.],
)[
  #codeblock(lang_label: "Internal helper with custom calling convention (x86-64)")[
  ```
  fn pad_fast(block: 64 bytes, src: n bytes, n: number)
      requires no_overlap(block, src)
      requires n <= 64
      ensures block = padded(src)
      trace depends on n
  {
      for x86_64 stack 0 calling {
          in block = r10, src = rsi, n = rdx
          preserves rdi, rsi, rdx, rbx, rbp, r12, r13, r14, r15
      } { ... }
  }
  ```
  ]
]

The caller keeps its live pointers in `rdi`, `rsi`, `rdx` across `call pad_fast` without spilling a single callee-saved register. On AArch64, internal helpers may also pass an empty `preserves_vec` list to use `v8..v15` freely when their caller does not need them—while any exported C-ABI caller that forgets to protect `v8..v15` across such a call is refused by the verifier.

== Zero-Stack Non-Leaf AArch64 Callers

On AArch64, the `bl` instruction always overwrites `x30` (the link register). Under the C ABI, every non-leaf function must allocate a 16-byte stack frame just to store and reload `x30`. With custom calling conventions, a non-recursive AArch64 caller avoids the stack completely: move `x30` into a caller-saved scratch register such as `x15`, list `x15` in the internal helper's `preserves` set, execute `bl helper`, restore `mov x30, x15`, and return—verified at `stack 0` with zero memory writes.

== Verified Tail Calls (`jmp` and `b`)

#with_note([
  Because the callee must appear strictly earlier in topological verification order, a tail jump cannot silently create an infinite loop that bypasses `decreases`.
])[
  When a function finishes by handing control directly to another function, it can tail-jump (`jmp callee` on x86-64, emitting `E9` with `R_X86_64_PLT32`; `b callee` on AArch64, emitting `0x14000000` with `R_AARCH64_JUMP26`). The verifier recognizes named tail targets without any new instruction-table rows and checks six conditions at the jump:
]

+ The stack pointer has returned to its entry offset (`sp == 0`), and on AArch64 the link register `x30` holds its entry value.
+ The callee's declared stack budget fits within the caller's declared stack budget.
+ Every general-purpose and vector register in the caller's preserved set still holds its entry value and is also preserved by the callee.
+ The callee precedes the caller in the topological verification order.
+ Every precondition, disjointness condition, writable span, and trace condition of the callee holds at the jump.
+ The state produced upon the callee's return satisfies every postcondition and trace rule of the caller.

#fig(
  5,
  "figures/fig4-calling.svg",
  "Three ways to transfer control in Ode",
  "C-ABI calls (left) protect foreign boundaries; custom calling conventions with x30 saved in x15 (center) allow zero-stack non-leaf AArch64 callers; verified tail calls (right) eliminate the call/return round-trip completely.",
)

// ============================================================================
// SECTION 6: PACKING, AUDITING, AND VERDICTS
// ============================================================================

= Packing, Auditing, and the Four Verdicts

A single command-line tool (`ode`) handles both halves of the workflow while keeping Alice's tools and Bob's verifier strictly separated.

== Bundling and Auditing an ELF Object

Alice builds a deployable object file and separate proof certificate with `ode pack`:
- Compiles the entry function and all reachable internal callees in topological order.
- Merges them into one relocatable ELF64 object (`.o`) in which _only_ the entry point is `STB_GLOBAL` under its content-hash symbol `ode_<52>`, while every internal helper is `STB_LOCAL`.
- Embeds the exact canonical `.ocl` contract in a non-executable `.ode.ocl` section and writes internal helper contracts, calling blocks, topological `order:`, and proof steps into the separate `.proof` file.

Bob audits the delivered binary with one command: `ode audit bundle.o --proof bundle.proof`. The auditor checks that the embedded `.ode.ocl` is canonical and matches the exported `ode_<52>` symbol, that 100% of `.text` bytes belong to verified functions, that no `.init_array` or `.fini_array` startup hooks or undefined symbols exist, and that `odeverify` approves every function's machine bytes against the instruction tables (`core/x86.tab`, 94 rows; `arm64/arm64.tab`, 54 rows).

#fig(
  6,
  "figures/fig5-bundle.svg",
  "Anatomy of a packed and audited ELF object bundle",
  "Bob's audit binds the exported linker symbol directly to BLAKE3(.ode.ocl) and checks 100% of .text bytes against the separate .proof file—leaving no room for hidden helper code or startup hooks.",
)

== The Four Exact Verdicts

Ode tools never blur proof with testing or absence of proof with falsehood. Every check reports one of four exact verdicts, summarized in the table below.

#fullwidth[
  #booktable(
    columns: (1.40in, 2.55in, 2.85in),
    ([Verdict], [What it establishes], [What it does not establish]),
    [`shown`], [The verifier checked the proof directly against the binary bytes and proved every clause of the contract for every valid input.], [Properties outside the contract (for example, speculative side channels or faults in the hardware processor itself).],
    [`refused with a proof`], [A concrete valid input was produced on which the binary contradicts a named clause of the contract (a genuine bug).], [That no other inputs also fail.],
    [`no proof found`], [The prover failed to construct an accepted proof, or the verifier rejected a malformed step.], [That the binary is wrong—the proof may simply be incomplete or missing a loop invariant.],
    [`run`], [Concrete test vectors executed against the specification or native binary matched expected outputs.], [A proof for inputs outside the tested vectors.],
  )
]

== Advisory Microarchitectural Feedback (`budget`)

A coder may include an optional `budget { max_bytes ...; max_icache_lines ...; max_frame_bytes ... }` block or invoke `ode advice` (`advice/estimate.py`) to inspect instruction byte counts, loop cache-line footprints, store-to-load forwarding hazards, and branch layouts across x86-64 and AArch64. Advice is strictly non-semantic: ignoring or changing an advisory budget never alters emitted bytes or verification soundness.

// ============================================================================
// SECTION 7: PROOF BY CONSTRUCTION — VERIFIED BLAKE3 AND BREADTH
// ============================================================================

= Proof by Construction: Verified BLAKE3 and Breadth

A language for verified native code must prove its worth on real, performance-critical software. Our primary benchmark is single-threaded BLAKE3 hashing (`b3l_hashr`), verified end-to-end against a 95-line canonical BLAKE3 specification (`7jb2pyzuwz6tqd3qmjsra3mk36tl4547sfpy3at5scbk772lbila`) and linked into `blake3-servil-core` via `--features ode-verified`.

== Fast Short-Input and Large-Input x86-64 BLAKE3

Our verified x86-64 BLAKE3 bundle consists of 17 functions (3,202 machine instructions, 17,278 bytes of `.text`, 1 exported symbol, 0 hooks) audited in one `ode audit` pass as `shown`. Applying custom calling conventions and verified tail calls transformed short-input performance without changing a single byte of the canonical contract:
- *64-byte inputs:* a 12-instruction zero-copy, zero-stack path in `b3l_hashr` loads the key, sets flags, and tail-jumps (`jmp`) directly into `blake3_servil_compress_in_place_avx512` (or `sse41`)—raising Zen 5 throughput from `0.670 GiB/s` (C-ABI baseline) to *`1.286 GiB/s`* (`98.9%` of hand-tuned `next`, `110.8%` of official `blake3 1.8.7`).
- *Single-block chunks (`<= 64 B`):* `b3l_chunk_node_fast` uses zero callee-saved spills and tail-jumps directly into custom-calling `b3l_pad_fast` (`stack 0`).
- *Inputs above 1 KiB:* a single-instruction `jmp b3l_hashr_long` enters the verified AVX-512 32-way tree, reaching *`16.336 GiB/s`* at 256 KiB (`98.4%` of `next`, `131.7%` of official).

#fig(
  7,
  "figures/fig6-blake3-perf.svg",
  "Verified BLAKE3 throughput on Zen 5 (64 B to 1 MiB)",
  "Verified pinned-run medians (45 interleaved trials per size). Short inputs (left) jumped from 0.67 to 1.29 GiB/s via custom calling and tail calls; large inputs (right) match 98.4–98.9% of hand-tuned next and beat official BLAKE3 by 28–32%. Medium sizes (4–32 KiB) remain slower because 4/8/16-way AVX-512 tiers are not yet added.",
)

#block(breakable: false, width: 6.80in)[
  == AArch64 BLAKE3 and Program Breadth
  #block(width: 4.50in)[
    The table below summarizes our verified programs across both x86-64 and AArch64, giving each routine's verified scope and measured silicon throughput.
  ]
  #v(6pt)
  #booktable(
    columns: (1.75in, 1.05in, 1.50in, 2.50in),
    align: (left, left, left, left),
    ([Program], [Target], [Verified scope], [Measured performance & status]),
    [`b3l_hashr` (BLAKE3)], [x86-64], [17 fns · 3,202 insns], [`1.286 GiB/s` (64 B, `98.9%` next); `16.336 GiB/s` (256 KiB, `98.4%` next). 4 SIMD kernels checked from `.S` bytes.],
    [`b3l_hashr_arm64` (BLAKE3)], [AArch64], [7 fns · 1,832 insns], [100% Ode source (4-way NEON): `2.194 GiB/s` (16 KiB, Apple M6, `84.4%` official); short/4 KiB speedup next.],
    [20-round ChaCha20], [x86-64 & Arm], [4-way / 16-way SIMD], [`9.412 GiB/s` on Zen 5; `1.701 GiB/s` on Apple M6. Full RFC 8439 verification.],
    [Spec-First Factory], [x86-64 & Arm], [38 verified functions], [Base64, UTF-8, DER, Adler-32, LZ4, SHA-256, varint, and verifier building blocks—all verified `shown`.],
  )
]

// ============================================================================
// SECTION 8: RELIANCE SETS, VERIFICATION ROUTES, AND FRONTIERS
// ============================================================================

= Reliance Sets, Verification Routes, and Open Frontiers

Ode is designed so that Bob does not have to accept the verifier's soundness without checking, and does not have to rely on any single foundation. Instead, the architecture supports four independent routes to justified confidence in `odeverify`:

#fullwidth[
  #booktable(
    columns: (1.55in, 2.85in, 2.40in),
    ([Route for Bob], [What it establishes], [Current status]),
    [*1. Lean 4 soundness proof*], [Machine-checked proof that if `odeverify` returns `shown`, the binary satisfies its contract and trace rule under standard axioms (`propext`, `Classical.choice`, `Quot.sound`).], [Complete: 11 top-level theorems in `test_sound.py`, zero `sorry`, covers x86-64, AArch64, calling conventions, and tail calls.],
    [*2. Instruction-table validation*], [Confirms that `x86.tab` (94 rows) and `arm64.tab` (54 rows) match real processors and external formal ISA models.], [All 54 `arm64.tab` rows cross-checked on Apple M6 silicon _and_ proved in `arm64/agree/Agree.lean` against Google DeepMind's `arm64-semantics`.],
    [*3. Read or re-implement the kernel*], [Bob reads a small verifier himself or checks the same `.proof` file with an independent second verifier written in another language.], [Open: `proof-core/Core.lean` is currently 5,123 lines (9,651 lines across verifier + model files). Shrinking it is a top priority.],
    [*4. Self-verifying Ode verifier*], [The verifier itself is written in Ode and verified against its own specification, breaking circularity via any one outside check.], [Early building blocks verified on both x86-64 and AArch64 (`examples/verifier/`: `all_zero`, `xor64`, `fold32`, `arith`).],
  )
]

#with_rubric(
  "The two discipline meters",
  [Meter 1 is this report's length and grammar; Meter 2 is the verifier's size and speed. Both are tracked openly as the language evolves.],
)[
  Four concrete engineering frontiers remain open and deliberately staged:
  + *Short-input and 4 KiB AArch64 BLAKE3* applying zero-copy 64-byte tail jumps (`b`) and `stack 0` link-register-in-`x15` callers on Apple Silicon.
  + *Explicit linked local namespaces* (`use alias = "file.ode"` and `alias.name`) so multi-file programs pack with plain `ode pack` instead of bespoke build scripts, without ever merging global namespaces.
  + *Shrinking `Core.lean` and building an independent second verifier* alongside wiring `ode audit` directly into `blake3-servil-core`'s build script.
  + *Full single-threaded `blake3-servil-core` coverage* (incremental `Hasher`, keyed and derive-key modes, intermediate x86-64 4/8/16-way tiers) and settling whether x86-64 AVX-512 kernels are rewritten in Ode source or kept as byte-verified assembly.
]

#v(0.5em)

#block(breakable: false, width: 6.80in)[
  == Revision 8 Meter Baseline
  #block(width: 4.50in)[
    The table below records exact counts for both discipline meters at Revision 8, so future simplification and feature rounds can be measured against an explicit baseline.
  ]
  #v(6pt)
  #booktable(
    columns: (1.85in, 1.35in, 3.60in),
    align: (left, right, left),
    ([Measurement], [Revision 8 value], [What it counts]),
    [*Meter 1 — Report length*], [14 pages], [Complete language definition, 7 figures, 5 tables, and 1-page EBNF appendix.],
    [*Meter 1 — Surface grammar*], [40 productions], [24 `.ocl` specification/contract productions + 16 `.ode` source productions (Appendix A).],
    [*Meter 2 — Verifier core*], [5,123 lines], [`proof-core/Core.lean` (`9,651` lines including Machine, Contract, Trace, Plain, Reader, Table, Arithmetic).],
    [*Meter 2 — Soundness proofs*], [32,684 lines], [`proof-core/Sound*.lean` proving 11 top-level theorems (standard Lean axioms only; zero `sorry`).],
    [*Instruction tables*], [94 + 54 rows], [`core/x86.tab` (94 rows) and standalone `arm64/arm64.tab` (54 rows, 54/54 proved against Google's model).],
    [*Full BLAKE3 audit*], [17 fns · 3,202 insns], [Verified `shown` in one `ode audit` pass against a 95-line `.ocl` contract (`455 KiB` combined proof).],
  )
]

// ============================================================================
// APPENDIX A: COMPLETE SURFACE GRAMMAR (WIRTH-STYLE REFERENCE)
// ============================================================================

#pagebreak()

#heading(level: 1, numbering: none)[Appendix A · Complete Surface Grammar of Ode and `.ocl`]

#v(0.15em)

#block(width: 6.80in)[
  #text(size: 8.6pt, fill: slate, style: "italic")[
    Extended Backus–Naur Form (EBNF) of the unified `.ode` source language and its canonical `.ocl` contract subset. Brackets `[ ... ]` denote optional items; braces `{ ... }` denote zero or more repetitions; quoted strings denote literal tokens. An `.ocl` file contains only `const`, `def`, `sequence`, `layout`, `kind`, and one nameless `contract`—never `fn`, `data`, `inline fn`, `calling`, or register names.
  ]
]

#v(0.55em)

#fullwidth_break[
  #set par(justify: false, leading: 0.46em)
  #set text(font: "Menlo", size: 6.8pt, fill: ink)
  #grid(
    columns: (1fr, 12pt, 1fr),
    [
      #block(fill: ivory, stroke: (left: 1.3pt + accent), inset: (x: 9pt, y: 7pt), width: 100%)[
        #text(font: "Palatino", size: 7.4pt, fill: accent, weight: "bold", tracking: 0.08em)[SPECIFICATION & CANONICAL `.ocl` SUBSET]
        #v(4pt)
        ```
        OclFile     = { SpecDecl } NamelessContract .
        SpecDecl    = ConstDecl | DefDecl | SeqDecl
                    | LayoutDecl | KindDecl .

        ConstDecl   = "const" ident "=" Expr .
        DefDecl     = "def" ident "(" [ IdList ] ")"
                      [ ":" Kind ] "{" { LetOrFail } Expr "}" .
        LetOrFail   = "let" ident "=" Expr
                    | "let" ident "[" "0" "]" "=" Expr
                    | "let" ident "[" ident "+" "1" "]" "=" Expr
                    | "fails" Expr "if" Expr .

        SeqDecl     = "sequence" ident "(" [ IdList ] ")" "{"
                      ident "[" "0" "]" "=" Expr
                      ident "[" ident "+" "1" "]" "=" Expr
                      [ "for" ident "in" "0" ".." Expr ] "}" .

        LayoutDecl  = "layout" ident num
                      "{" Field { "," Field } "}" .
        Field       = ident [ "[" num "]" ] ":" Kind
                      "at" num [ "below" num ] .
        KindDecl    = "kind" ident ":" Kind .
        Kind        = "number" | "byte" | "word" | "counter"
                    | "any" | ident | ( num | ident ) "bytes" .

        NamelessContract = "contract" "(" [ ParamList ] ")" "{"
                           { ContractClause } "}" .
        ParamList   = Param { "," Param } .
        Param       = ident ":" Kind .

        ContractClause = "requires" Expr
                       | "ensures" ident "=" Expr
                       | "returns" Expr
                       | "writes" ident
                       | "trace" "depends" "on" ExprList
                       | "result" "depends" "on" ExprList
                       | "stack" Expr
                       | "decreases" Expr
                       | "needs" ident [ "if" Expr ] .

        Expr        = "if" Expr "then" Expr "else" Expr
                    | "[" Expr "for" ident "in" Expr ".." Expr "]"
                    | OrExpr .
        OrExpr      = AndExpr { "||" AndExpr } .
        AndExpr     = RelExpr { "&&" RelExpr } .
        RelExpr     = AddExpr [ RelOp AddExpr ] .
        RelOp       = "==" | "!=" | "<" | "<=" | ">" | ">=" .
        AddExpr     = MulExpr { ("+"|"-"|"|"|"^") MulExpr } .
        MulExpr     = Unary { ("*"|"/"|"%"|"&"|"<<"|">>"|"ror")
                              Unary } .
        Unary       = ("-" | "!" | "~") Unary | Postfix .
        Postfix     = Primary { "[" Expr [ ".." Expr ] "]"
                              | "." ident | "(" [ ExprList ] ")" } .
        Primary     = num | ident | "(" Expr ")"
                    | "[" [ ExprList ] "]" .
        ```
      ]
    ],
    [],
    [
      #block(fill: ivory, stroke: (left: 1.3pt + slate), inset: (x: 9pt, y: 7pt), width: 100%)[
        #text(font: "Palatino", size: 7.4pt, fill: slate, weight: "bold", tracking: 0.08em)[UNIFIED `.ode` SOURCE & TARGET IMPLEMENTATIONS]
        #v(4pt)
        ```
        OdeFile     = { SpecDecl | DataDecl | InlineFn | FnDecl } .

        DataDecl    = "data" ident "{" { num | string } "}" .

        InlineFn    = "inline" "fn" ident "(" [ RegParamList ] ")"
                      { "distinct" "(" IdList ")"
                      | "changes" IdList }
                      "{" { AsmStmt } "}" .
        RegParam    = ident ":" ( "gpr" | "vec" ) .

        FnDecl      = "fn" ident "(" [ ParamList ] ")"
                      [ "as" string ]
                      { ContractClause }
                      "{" TargetBlock { TargetBlock } "}" .

        TargetBlock = "for" ( "x86_64" | "arm64" )
                      { "stack" Expr
                      | "needs" ident [ "if" Expr ]
                      | CallingBlock }
                      "{" { BodyItem } "}" .

        CallingBlock = "calling" "{"
                       [ "in" Bind { "," Bind } ]
                       [ "out" "=" Reg ]
                       [ "preserves" [ RegList ] ]
                       [ "preserves_vec" [ RegList ] ]
                       "}" .
        Bind        = ident "=" Reg .

        BodyItem    = BudgetBlock | FrameBlock | RegAlias
                    | PlaceBlock  | ForUnroll  | Label | AsmStmt .

        BudgetBlock = "budget" "{" { ident num } "}" .
        FrameBlock  = "frame"  "{" { ident ":" FrameField } "}" .
        RegAlias    = "reg" ident "=" Reg .

        PlaceBlock  = "place" "{"
                      { "name" ident "=" Reg
                      | "fact" Expr
                      | "wrote" ident "[" Expr ".." [ Expr ] "]"
                        "=" Expr
                      | "decreases" Expr } "}" .

        ForUnroll   = "for" ident "in" num ".." num
                      "{" { BodyItem } "}" .
        Label       = "@" ident ":" .

        AsmStmt     = RawInstruction
                    | Reg ":=" Expr
                    | ident "(" [ RegList ] ")"
                    | ( "call" | "jmp" | "bl" | "b" ) ident .
        ```
      ]
      #v(8pt)
      #block(fill: blush, stroke: (left: 1.3pt + accent), inset: (x: 9pt, y: 7pt), width: 100%)[
        #text(font: "Palatino", size: 7.4pt, fill: accent, weight: "bold", tracking: 0.08em)[COMMAND SUMMARY (`lang/ode_tool.py`)]
        #v(3pt)
        ```
        ode canon     FILE [--out-dir D]   // -> <52-b32>.ocl
        ode pack      SRC --fn F -o O -p P // build + prove + audit
        ode audit     OBJ --proof P        // Bob's sole check
        ode spec-test FILE --call F ...    // test concrete inputs
        ode advice    SRC --fn F           // advisory cost metrics
        ```
      ]
    ],
  )
]
