// The Ode Language Report, Revision 10 (November 2026).
//
// Every listing in this report is read from a file that the repository's tests compile and verify, and
// the numbers that can be worked out from the repository are read from facts.json (make_facts.py).
// Build (from the repository's root):
//   pypy3 paper/render-paper.py

#let rev      = 10
#let ink      = rgb("#1C1E21")
#let charcoal = rgb("#2E343D")
#let slate    = rgb("#5B6470")
#let muted    = rgb("#7D8590")
#let rulecol  = rgb("#CFC9BC")
#let accent   = rgb("#9E2A2B")
#let ivory    = rgb("#F7F5F0")
#let sand     = rgb("#EEEBE2")

#let F = json("facts.json")
#let M = json("measured.json")

#let commas(x) = {
  let s = str(x)
  let n = s.len()
  let out = ""
  for (i, c) in s.clusters().enumerate() {
    if i > 0 and calc.rem(n - i, 3) == 0 { out += "," }
    out += c
  }
  out
}

// --- Text read from the files that are tested ---

#let excerpt(path, start, stop) = {
  let s = read(path)
  let rest = s.slice(s.position(start))
  rest.slice(0, rest.position(stop) + stop.len())
}
#let dedent4(s) = s.split("\n").map(l => if l.starts-with("    ") { l.slice(4) } else { l }).join("\n")

#let az = read("examples/all_zero.ode")
#let az_contract = az.slice(0, az.position("\n{\n")).trim(at: end)
#let az_x86 = dedent4(az.slice(az.position("    for x86_64 {"), az.position("    for arm64 {")).trim(at: end))
#let az_arm = dedent4(az.slice(az.position("    for arm64 {")).trim(at: end).slice(0, -2).trim(at: end))

#let quad = read("examples/quad.ode")
#let quad_from_step = quad.slice(quad.position("fn step("))
#let step_x86 = quad_from_step.slice(0, quad_from_step.position("    for arm64 calling {")).trim(at: end)

#let pad_contract = excerpt("/proof-core/examples/arm64/pad_arm64.spec", "contract b3l_pad_arm64(", "\n}")
#let equal_ct_contract = excerpt("/proof-core/test_trace_proposal.py", "contract t_equal_ct(", "\n}")

// --- Page: an asymmetric grid on US Letter ---
//   main column 4.50in, gutter 0.35in, margin notes 1.95in, full span 6.80in

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
          [#text(size: 7.6pt, fill: muted)[Revision #rev · November 2026]],
          [#counter(page).display()],
        )
      ]
    }
  },
)

#set text(font: "Palatino", size: 9.9pt, fill: ink, lang: "en")
#set par(justify: true, leading: 0.66em, spacing: 0.90em, first-line-indent: 0pt)
#set heading(numbering: "1.1")

#show heading.where(level: 1): it => {
  block(breakable: false, sticky: true, above: 1.75em, below: 0.85em, width: 6.80in)[
    #set par(justify: false)
    #if it.numbering != none [
      #text(fill: accent, size: 12.0pt, weight: "bold")[§ #counter(heading).display()]
      #h(0.45em)
    ]
    #text(fill: ink, size: 12.8pt, weight: "bold")[#it.body]
    #block(above: 6pt, below: 0pt, line(length: 100%, stroke: 0.55pt + rulecol))
  ]
}

#show heading.where(level: 2): it => {
  block(breakable: false, sticky: true, above: 1.45em, below: 0.70em)[
    #set par(justify: false)
    #if it.numbering != none [
      #text(fill: accent, size: 10.0pt, weight: "semibold")[#counter(heading).display()]
      #h(0.42em)
    ]
    #text(fill: ink, size: 10.4pt, weight: "bold")[#it.body]
  ]
}

// Code in the text and in listings: one typeface, the figures' own.
#show raw.where(block: false): it => text(font: "Menlo", size: 0.9em)[#it.text]
#show raw.where(block: true): set text(font: "Menlo", size: 7.5pt)

// --- Building blocks ---

#let figs = counter("figures")
#let tabs = counter("tables")

#let fullwidth(body) = block(width: 6.80in, breakable: false, above: 0.95em, below: 0.95em)[#body]

// A paragraph with a note beside it in the margin.
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

#let with_rubric(title, note, above: 0.90em, body) = with_note(
  [
    #text(fill: accent, weight: "bold", size: 7.4pt, tracking: 0.07em)[#upper(title)]
    #v(2pt)
    #note
  ],
  above: above,
  body,
)

// A listing: a quiet ground and a hairline at its left.
#let listing(label: none, strong: false, width: 100%, size: 7.5pt, body) = block(
  width: width,
  breakable: false,
  fill: if strong { sand } else { ivory },
  stroke: (left: 1.4pt + (if strong { charcoal } else { slate })),
  inset: (left: 10pt, right: 8pt, top: 6.5pt, bottom: 6.5pt),
  above: 0.65em,
  below: 0.80em,
)[
  #if label != none [
    #text(font: "Palatino", size: 7.1pt, fill: if strong { ink } else { slate }, weight: "bold", tracking: 0.08em)[#upper(label)]
    #v(2pt)
  ]
  #set par(justify: false, leading: 0.46em)
  #show raw.where(block: true): set text(size: size)
  #body
]

#let caption(kind, num, title, body) = {
  set par(justify: false, leading: 0.53em)
  text(size: 8.2pt, fill: accent, weight: "bold")[#kind #num.]
  h(0.35em)
  text(size: 8.2pt, fill: ink, weight: "bold")[#title.]
  h(0.25em)
  text(size: 8.1pt, fill: slate)[#body]
}

#let fig(num, img_path, title, body) = fullwidth[
  #figs.step()
  #image(img_path, width: 6.80in)
  #v(4pt)
  #caption("Figure", num, title, body)
]

// A table with rules above and below only, and its caption above it.
#let booktable(num, title, columns: auto, align: left, header, ..rows) = block(width: 6.80in, breakable: true, above: 0.95em, below: 0.95em)[
  #tabs.step()
  #block(sticky: true, below: 5pt)[#caption("Table", num, title, [])]
  #set text(size: 8.5pt)
  #set par(justify: false, leading: 0.51em)
  #show table.cell: set block(breakable: false)
  #table(
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
]

// ============================================================================
// Title
// ============================================================================

#block(width: 6.80in)[
  #text(size: 8.0pt, fill: accent, weight: "bold", tracking: 0.14em)[LANGUAGE REPORT · REVISION #rev]
  #v(4pt)
  #text(size: 26pt, weight: "bold", fill: ink)[Ode]
  #v(2pt)
  #text(size: 12.6pt, style: "italic", fill: slate)[A Language for Native Machine Code That Carries Its Proof]
  #v(8pt)
  #line(length: 100%, stroke: 0.9pt + ink)
  #v(5pt)
  #grid(
    columns: (1fr, auto),
    [#text(size: 8.6pt, style: "italic", fill: slate)[Make the promise small, keep the machine in view, and let the reader check the bytes.]],
    [#text(size: 8.3pt, fill: slate)[November 2026]],
  )
]

#v(1.3em)

Suppose you need a fast cryptographic hash, parser, or memory routine compiled to native x86-64 or AArch64 machine code. You did not write it, and you do not wish to read three thousand lines of assembly or to rely on a compiler you cannot inspect. Running a hundred test vectors confirms that the binary gives the right answers on those hundred inputs. It tells you nothing about the next input, nothing about reads outside a buffer, and nothing about whether a branch inside the binary depends on a key.

Ode separates what a routine _promises_ from how it is _built_. The promise is a short text called a _contract_. The maker, whom we call _Alice_, writes the machine instructions for each processor and hands over two files: the compiled object file, and a proof file beside it. The auditor, whom we call _Bob_, reads the contract and runs a small program, the _verifier_, on the object file's bytes, the contract, and the proof file. If the verifier answers `shown`, those bytes keep the promise for every input the contract allows. Bob need not read the source, and his conclusion does not rely on Alice, on her compiler or assembler, or on the program that found the proof. It relies on the verifier, and on tables that say what each processor instruction does (section 8).

#fig(
  1,
  "figures/fig1-boundary.svg",
  "What crosses from the maker to the auditor",
  [Alice's tools (left) compile the source and search for a proof; Bob's conclusion relies on none of them. What it does rely on is in the frame at the right: the contract he reads, the verifier, and the tables that say what each processor instruction does.],
)

Sections 2 and 3 say what a contract can promise. Section 4 shows how code is written, for two processors in one file, and section 5 how one Ode function calls another cheaply. Section 6 is Bob's side: the files he is given, and what the verifier's answers mean. Section 7 reports the programs verified so far and their speed. Section 8 says what Bob's conclusion relies on, and what this revision leaves out.

// ============================================================================
// 1. Design principles
// ============================================================================

#pagebreak()

= Design Principles

Four decisions govern the rest. Where a feature would conflict with one of them, the feature gives way.

#with_rubric(
  "Reliance sets",
  [A _reliance set_ is everything one party depends on for one conclusion; the term is Mark S. Miller's. Bob's set, for the conclusion `shown`, is drawn in Figure 1 and listed in section 8.],
)[
  *1. Keep what Bob relies on small.*
  Alice wants a fast search for proofs and convenient notation. Bob wants as little as possible between the contract he reads and the bytes that run. Ode serves both by splitting _finding_ a proof from _checking_ one. Everything clever (the search, the arithmetic, advice about speed, the source notation) is on Alice's side. On Bob's side is one small program that reads the object file's bytes, checks each step of the proof file, and confirms that every instruction in the file belongs to a function it has checked.
]

*2. Never hide the processor.*
Compilers for systems languages add stack frames, move registers, and rewrite code in ways the source does not show. That defeats both tuning for speed and auditing for timing. In Ode a processor instruction is a source statement, and every higher-level form stands for instructions that are fixed by what the coder wrote. Where a form cannot be encoded with the registers named, the compiler reports the line. It does not add a move, save a register on the stack, or pick a slower instruction to make the line compile.

*3. A contract is a closed world.*
A contract says everything a function may assume and everything it may do: which memory it may read and write, how much stack it and the functions it calls may use, which processor extensions it needs, why its loops end, and what its sequence of instructions and addresses may depend on. A function that does anything its contract does not allow is refused. Memory it was not given to write holds, when it returns, what it held when it was called.

*4. Two processors.*
A language designed on one processor takes that processor's habits for laws. Ode targets x86-64 and AArch64 under one verifier. A contract names no register and no instruction, so the x86-64 code and the AArch64 code of one function answer to the same contract text, under the same identifier.

// ============================================================================
// 2. Specifications and contracts
// ============================================================================

= Specifications and Contracts

To audit a binary without reading its code, Bob needs a text that says what the code must compute, and that cannot be mistaken for a description of how. Machine arithmetic wraps at 32 or 64 bits, and a read past the end of a buffer returns whatever lies there; a specification written in those terms inherits their surprises. Ode's specifications are written in exact numbers and lists, by equations. The listing that follows is one, together with the contract of a function that must compute it.

#listing(label: "A specification and a contract")[#raw(az_contract, block: true)]

The two definitions are mathematics. `zero_from(a, at)` is 1 when every byte of `a` from place `at` on is zero, and 0 otherwise; `zeros(a)` asks the same of the whole of `a`. The last four lines are the contract of a function `all_zero`. It is given the address of `n` bytes, called `a`, and the number `n`. It returns `zeros(a)`. Which instructions it runs and which addresses it touches may depend on the bytes of `a` and on `n`: a scan that stops at the first nonzero byte shows where that byte is. It uses no stack. Bob can try a definition on inputs of his own (`ode spec-test`); the verifier's answer is about every input.

== Kinds of Values

A specification speaks of six kinds of values. Table 1 gives, for each kind, the values it has and what can be done with them.

#booktable(
  1, "The kinds of values in a specification",
  columns: (1.05in, 1.95in, 3.80in),
  ([Kind], [Its values], [What can be done with them]),
  [`number`], [Whole numbers from 0 up, of any size], [`+` and `*` are exact; `/` and `%` give the whole quotient and the remainder. `a - b` where `b` is above `a` has no value: it is an error, never a wrapped result.],
  [`byte`], [0 to 255], [One byte of memory; `a[i]` of some bytes is a byte.],
  [`word`], [32 bits], [`+` wraps at $2^32$; `&`, `|`, `^` work on the bits; `x >>> k` turns the bits right by `k`.],
  [`counter`], [64 bits], [A number is added with `+`; `lo(c)` and `hi(c)` are its two words.],
  [`list`], [Finitely many values in order, counted from 0], [`len(xs)`, `xs[i]`, `xs[a .. b]` (from place `a` up to, not including, `b`), `xs ++ ys`, `[e for i in a..b]`.],
  [`bytes`], [A list of bytes (`0..255`)], [`words(bs)` reads every four bytes as a word, lowest byte first; `bytes_of(ws)` converts back.],
  [`record`], [Named fields], [`{h: a, length: b}` and `r.h`. A `layout` says where each field of a record lies in memory.],
)

Definitions are equations: `const`, `def`, and `sequence` (a list given by its first value and by each next value from the one before). A definition may use itself on something smaller, as `zero_from` does. Nothing is assigned twice, and nothing loops.

Three signs have three meanings. `==` asks whether two values are equal. `:=`, in code, stores a value into a register or into memory. `=` says what a name stands for, or what a place holds: `const ROOT = 8`, `reg idx = rcx`, `ensures out = E`.

== Contracts Have No Names

Names are chosen by authors. A function called `check_signature`, or a comment saying that a check is made, can lead an auditor's eye past a condition that is missing. So the text Bob audits has no name that an author chose, and no comment. Figure 2 shows what the tool `ode canon` makes of the example above.

#fig(
  2,
  "figures/fig2-canon.svg",
  "From the author's text to the contract's identifier",
  [The left box is the example as written. `ode canon` makes the text in the middle from it, and the identifier at the right is the BLAKE3 hash of that text. The figure is drawn from the tool's own output.],
)

`ode canon` does the same three things every time. It leaves out comments, and every definition the contract does not use. It replaces each name by a letter and a number, in the order in which names are first met starting from the contract: `a0`, `a1` for the contract's arguments, `f0`, `f1` for definitions, `p0`, `p1` for a definition's parameters. And it leaves out how arguments are passed (section 5), which names registers. The result is the _canonical contract_, kept in files of the type `.ocl` (and embedded in the `.ode.ocl` section of a packed object file). The example's canonical contract has #F.all_zero.canonical_lines lines.

The contract's only identifier is the BLAKE3 hash of that text: 256 bits, written as 52 characters (base 32: the letters `a` to `z` and the digits `2` to `7`). The function's symbol in the object file is `ode_` followed by those characters, and a canonical contract kept in a file is named by them. A tool that reads such a file hashes it first, and refuses it if its name is not its hash. A reader who wants words back keeps a _glossary_ (`a0` is `a`, `f1` is `zero_from`). A glossary is its reader's own, and is never hashed.

// ============================================================================
// 3. What a contract promises
// ============================================================================

= What a Contract Promises

If the caller makes every `requires` line true, a function that the verifier has checked against its contract returns, and when it returns every `ensures` and `returns` line holds. It has used no more stack than its `stack` line says, and no processor extension that a `needs` line does not name. Its trace (section 3.2) depends only on what its `trace depends on` line names. Of a call that does not meet `requires`, the contract promises nothing.

== Memory: Pieces, Overlap, and Lending

A machine address carries no length and no owner. If nothing said which bytes a called function may touch, a caller could keep no fact about its memory across a call. A contract therefore speaks of _pieces_ of memory: an argument that is an address comes with a length, such as `64 bytes`, or `n bytes` where `n` is another argument. Here is the contract of the function that fills the last block of a BLAKE3 chunk:

#listing(label: "A contract with two pieces of memory")[#raw(pad_contract, block: true)]

#with_note([
  Two pieces that lie end to end do not overlap: they have no byte in common.
])[
  `block` and `src` are pieces. A function may read the pieces it is given. It may write only a piece that an `ensures` line names (here `block`) or a `writes` line names. `requires no_overlap(block, src)` asks the caller to see that the two have no byte in common.
]

A caller _lends_ pieces to the functions it calls. It may lend a whole piece or a part of one: the caller of this function lends bytes 32 to 96 of a 120-byte record as `block` (Figure 3). It can lend no more than it holds: no bytes it was not given, and nothing to write that it may only read. After the call it knows what the function's `ensures` says of the part it lent, and everything it knew before of the rest.

#fig(
  3,
  "figures/fig3-memory.svg",
  "A caller lends a part of a record",
  [The caller's pieces do not overlap one another. It lends `input` to be read and one field of the record `nd` to be written. What it knew of the other fields of `nd` still holds after the call.],
)

The stack is a function's own for the length of the call. It may use the bytes its `stack` line counts: a number, or a formula such as `18688 + 384 * bits(len / 1024)` where the depth of calls grows with the input. It may lend parts of them to the functions it calls, and it must put the stack pointer back. A program's read-only data may be read and is never written.

== The Trace

A routine can compute the right answer and still give away a key, by taking longer on some keys than on others. What can be seen from outside (the time taken, the state of the cache) follows from which instructions ran and which addresses were touched. That sequence is the function's _trace_.

#with_rubric(
  "What the trace covers",
  [The trace is the sequence of instructions and addresses that the processor's manual defines. Speculation inside the processor, the power it draws, and other physical effects are outside it.],
)[
  A contract's `trace depends on` line names what the trace may depend on. Its meaning is a statement about two runs: _if two calls agree on the addresses given and on every value the line names, they run the same instructions and touch the same addresses, whatever else differs._
]

Take two functions that tell whether two runs of `n` bytes are the same. One stops at the first byte that differs. Its trace shows where that byte is, and the verifier accepts it only with `trace depends on a, b, n`. The other gathers the differences without a branch on any byte, and the verifier accepts this contract for it:

#listing(label: "The trace depends on the length alone")[#raw(equal_ct_contract, block: true)]

Its trace depends on the length alone, though the number it returns is computed from every byte.

The line can also name a computed value. A function that calls the second one and then branches once, to accept or to reject, says `trace depends on n, same_ct(want, tag)`: its trace may depend on whether the two runs of bytes agree, and on nothing else about them. A function that names its result without saying what it is (`returns r`) can say what the result is computed from, with a `result depends on` line.

The rule the verifier applies inside a function is short. Whatever a branch tests, and whatever an address is computed from, must be computed only from the addresses given and from what the function's own `trace depends on` line names.

// ============================================================================
// 4. Writing code
// ============================================================================

= Writing Code

Assembly gives its writer every choice and no help: two operands that must differ are given the same register, a slot of the stack frame is miscounted, and the x86-64 and AArch64 versions of one function drift apart. A compiler helps, and takes the choices away. Ode leaves the choices with the coder and checks the bookkeeping.

A source file (of the type `.ode`) holds definitions and functions. A function is its contract followed by its code for each processor: `for x86_64 { ... }` and `for arm64 { ... }`. Every function has a contract. A file is a closed world of names: nothing outside it is in scope.

== Notation That Chooses Nothing

In a function's code, a line is one processor instruction, written as an assembler takes it, or one of the forms below. Each form stands for instructions that are fixed by what is written.

- `reg idx = rcx`: from there on, `idx` is that register.
- `dst := src`: one `mov`, or one `lea` for the address of a field of the frame. `idx := 0` is `mov rcx, 0`. It moves as many bytes as both sides say; it never widens and never cuts.
- `frame { ... }`, with a line for each field such as `saved: 7 * u64`: the fields of the function's stack frame, in order. `saved[1] := x19` stores into the second slot of `saved`, and `frame.size` is the bytes of all the fields. A slot outside its field is refused at its line.
- `inline fn g for arm64 (a: vec, b: vec, t: vec) distinct(a, b, t) changes a, t { ... }`: a named group of instructions, put wherever `g(v0, v1, v16)` is written, with no call and no return. A use that gives one register for two that must differ is refused, and so is a line of the group that changes a register which `changes` does not list.
- `for i in 0..8 { ... }`: the lines eight times, with `$i` replaced by 0 to 7.
- `loop { ... break if ult ... }` and `if eq { ... } else { ... }`: jumps on the condition named, after a comparison that the coder wrote.
- `place { ... }`: what holds each time the code comes to the next instruction. A proof about a loop needs a statement that is true every time round; this is where the coder writes it, beside the loop. It is no part of the object file; the program that finds the proof reads it.

Figure 4 is the code of the example of section 2, for both processors.

#fullwidth[
  #figs.step()
  #grid(
    columns: (1fr, 10pt, 1fr),
    [#listing(label: "For x86-64", size: 7.2pt)[#raw(az_x86, block: true)]],
    [],
    [#listing(label: "For AArch64", size: 7.2pt)[#raw(az_arm, block: true)]],
  )
  #v(2pt)
  #caption("Figure", 4, "One contract, two processors", [The two blocks of the function `all_zero` in the example's source file: #M.all_zero.x86_64.instructions instructions (#M.all_zero.x86_64.bytes bytes) for x86-64, #M.all_zero.arm64.instructions instructions (#M.all_zero.arm64.bytes bytes) for AArch64. Both answer to the contract of section 2, whose identifier is #raw(F.all_zero.id), and the verifier's answer for both is `shown`.])
]

// ============================================================================
// 5. Calls
// ============================================================================

= Calls Between Ode Functions

Code written in C or Rust calls an Ode function by the platform's C convention. On x86-64 the arguments are passed in `rdi`, `rsi`, `rdx`, `rcx`, `r8`, `r9`, and six callee-saved registers (`rbx`, `rbp`, `r12` to `r15`) must come back as they were. On AArch64 the arguments are in `x0` to `x7`, and `x19` to `x29` and `v8` to `v15` must come back as they were. A function that other code may call keeps to that convention, and the verifier checks that it does.

Between two Ode functions of one program, the convention is a cost with no purpose: registers are saved that the caller does not use, and arguments are moved to where the convention wants them. When BLAKE3 hashes 64 bytes, the instructions around the one compression (calls, saved registers, a copy of the block) can take as long as the compression itself (section 7). Ode has three ways to cut that cost. The verifier checks each.

== A Calling Convention of the Function's Own

A function that only Ode code calls may state its own convention: which register holds each argument, which holds the result, and which registers it leaves as they were.

#fullwidth[
  #listing(label: "A function with its own convention (its x86-64 block)", width: 6.80in)[
    #raw(step_x86, block: true)
    #text(font: "Menlo", size: 7.5pt, fill: muted)[#h(2.1em)…]
  ]
]

#with_rubric(
  "What is refused",
  [An argument or a result in the stack pointer, or on AArch64 in the register that holds the return address; two arguments in one register; a result register that `preserves` also lists.],
)[
  The caller keeps what it still needs in registers that `preserves` lists, and saves nothing. Such a function is local to its object file, and the tool refuses to make it visible to C code.
]

== A Caller With No Stack on AArch64

On AArch64 a call (`bl`) puts the return address in the register `x30`. A function that calls another must first save its own `x30`, and under the C convention that takes a stack frame. A helper with a convention of its own can promise to preserve some register that the caller is free to use, say `x15`. The caller then moves `x30` there, calls, moves it back, and returns, with `stack 0`.

== Tail Calls

Where the last thing a function does is to call another and return its result, it can jump there instead (`jmp` on x86-64, `b` on AArch64). The other function then returns straight to the first one's caller, and the first needs no stack frame and no return of its own. At such a jump the verifier checks six things.

+ The stack pointer is where it was at entry, and on AArch64 `x30` holds what it held at entry.
+ The stack the other function may use is within the first one's `stack` line.
+ Every register the first function must preserve holds its entry value, and the other function preserves it too.
+ The other function was verified before this one, so no chain of such jumps can go round in a circle.
+ Everything the other function `requires` holds at the jump.
+ What the other function promises at its return is what the first one promised its caller, and its trace depends on nothing that the first one's contract does not allow.

#fig(
  5,
  "figures/fig4-calling.svg",
  "Three ways to pass control",
  [The C convention at the boundary with other code (left); a convention of the function's own, with the return address kept in a register (middle); a jump in place of a call and a return (right).],
)

// ============================================================================
// 6. Bob's side
// ============================================================================

= What Bob Is Given, and What the Answers Mean

Bob's question is about a file that will run. Two things could spoil an answer about it: code in the file that the answer does not cover (a helper nobody checked, a routine that runs when the program starts), and a contract other than the one he read. What Alice hands over is made so as to rule out both.

== One Object File, One Proof File

`ode pack` makes two files from a source file. The _object file_ holds the function named, every function it calls, and the canonical contract in a section of its own. Only the function named is visible to a linker, under the symbol `ode_` followed by its contract's 52 characters; the functions it calls are local to the file. The _proof file_ holds the contracts and calling conventions of those local functions, and the steps of each function's proof. It stays outside the object file: it is needed to check the code, and not to run it.

`ode audit` is Bob's command. It hashes the contract in the object file and checks that the symbol is that hash. It checks that every byte of code in the file belongs to a function the verifier has checked. It refuses a file that has a routine to run at the program's start or end, or that uses a symbol defined elsewhere. And it runs the verifier on each function's bytes. Given `--expect-contract` and 52 characters, it also refuses any contract but that one.

#fig(
  6,
  "figures/fig5-bundle.svg",
  "The object file and the proof file",
  [The audit ties the one visible symbol to the hash of the contract inside the object file, and accounts for every byte of code in it.],
)

== Four Words, Used Exactly

A proof is not a test, and a missing proof is not a fault found. Reports about Ode code use four words, each for one thing. Table 2 says what each means, and what it does not.

#booktable(
  2, "The four words",
  columns: (1.35in, 2.75in, 2.70in),
  ([Word], [What happened], [What it does not tell]),
  [`shown`], [The verifier read the object file's bytes, the contract and the proof file, and accepted. For every input that meets `requires`, the code keeps every line of the contract.], [Anything the contract does not say; that the processor does what its manual says.],
  [`refused with a proof`], [The verifier was given a proof file and did not accept it.], [That the code is wrong: another proof file might be accepted. (A sound verifier refuses every proof file for code that breaks its contract.)],
  [`no proof found`], [The program that searches for proofs gave up. The verifier has said nothing.], [Anything about the code.],
  [`run`], [The code, or a definition, was executed on particular inputs and gave what was expected.], [Anything about other inputs. A run is a test, not a proof.],
)

The verifier itself prints two of them: `shown`, or `refused` with its reason.

== Advice About Speed

The verifier judges what code computes, not how fast. Whether a loop is fast depends on things no contract mentions: how many cache lines its instructions span, or whether a load reads bytes that a store has just written in parts. `ode advise` reports such counts for a function, and a function may state limits for them in a `budget` block, with lines such as `max_bytes 64` and `max_icache_lines 1`. These are advice. No limit changes the bytes produced, or the verifier's answer.

// ============================================================================
// 7. Programs
// ============================================================================

= Verified Programs

The test of a language like this one is a program worth using. BLAKE3 is a cryptographic hash function. The function verified here takes a message of any length and a key, and gives the 32-byte hash, on one thread. Its contract is BLAKE3's definition written as a specification: 95 lines in canonical form. The speeds below are measured in an experimental branch of BLAKE3-Servil, a hand-tuned BLAKE3 library in Rust and assembly, where this code stands in for the library's own.

== BLAKE3 on x86-64

The x86-64 code is 19 functions, 3,837 instructions, all compiled from `.ode` source (one-block SSE4.1 and AVX-512 kernels, 16-lane and 32-lane AVX-512 wide kernels, and the tree and short-input glue). One `ode audit` of the object file answers `shown` for all 19 functions against the 95-line canonical BLAKE3 contract.

Figure 7 compares this 19-function Ode bundle against BLAKE3-Servil and the official `blake3` crate (version 1.8.7) on one core of an AMD Ryzen 7 9700X (Zen 5). The Ode bundle hashes at 1.28 GiB/s at 64 bytes (99% of BLAKE3-Servil, 160% of the official crate), 2.93 GiB/s at 4 KiB (88% of BLAKE3-Servil), 7.80 GiB/s at 16 KiB (74%), and 16.30 GiB/s at 256 KiB (99% of BLAKE3-Servil, 132% of the official crate).

#fig(
  7,
  "figures/fig6-blake3-perf.svg",
  "BLAKE3 on one core of an AMD Ryzen 7 9700X (Zen 5)",
  [Medians of 45 interleaved trials at each size, with nothing else running on the machine. The grey bars at the left are a baseline Ode build that uses the C calling convention between its own functions and copies the input block (0.67 GiB/s at 64 bytes); section 5 explains the custom-calling and tail-call difference.],
)

== BLAKE3 on AArch64, and Other Programs

The AArch64 code is 8 functions, 1,891 instructions, all written in Ode, with a kernel that hashes four chunks side by side with NEON. On an Apple M6 it hashes 1.18 GiB a second at 64 bytes and 2.28 at 4 KiB (83% and 90% of the official crate's speed), and 2.2 from 16 KiB to 1 MiB (83 to 85% of the official crate's). At 256 bytes and at 1 KiB it reaches about half the official crate's speed (55% and 49%). BLAKE3-Servil is up to 3.2 times as fast as the Ode code there, on large inputs. These figures are medians of 45 trials on a machine that was not reserved for the measurement, so they are less certain than those of Figure 7.

Table 3 lists the verified programs: for each, the processor, how much code the verifier's answer covers, and what the code is.

#booktable(
  3, "Programs for which the verifier answers shown",
  columns: (1.75in, 1.05in, 1.55in, 2.45in),
  ([Program], [Processor], [Code covered], [What it is]),
  [BLAKE3, one thread], [x86-64], [19 functions, 3,837 instructions], [All in `.ode` source; one-block, 16-way, and 32-way AVX-512 kernels.],
  [BLAKE3, one thread], [AArch64], [8 functions, 1,891 instructions], [4 unified `.ode` files with `use`; 4-way NEON kernel.],
  [BLAKE3 64-byte XOF block], [x86-64, AArch64], [115 and 125 instructions], [Baseline SSE2 and NEON, `stack 0`, `trace depends on nothing`, same contract ID.],
  [ChaCha20 block function], [x86-64, AArch64], [1,090 and 1,759 instructions], [16 blocks a call with AVX-512; 4 blocks a call with NEON.],
  [RFC 9669 eBPF virtual machine], [x86-64, AArch64], [209 and 192 instructions], [11 opcodes, 4 registers, signed relative jumps, bounded fuel; 6 functions, same contract ID.],
  [Full two-target routines], [each for both], [10 unified `.ode` builds], [RFC 1950 Adler-32, strict RFC 3629 UTF-8 validator/counter, RFC 1071 Internet Checksum, ASCII decimal parser, and constant-time `ct_bytes_eq` — all `stack 0`, same contract ID on both processors.],
  [19 smaller routines], [each for both], [38 object files], [Pieces of Base64, DER, LZ4, SHA-256 and ChaCha20; hex and varint decoders; pieces of a verifier.],
)

The verifier's answer depends only on the compiled bytes and the proof, never on who wrote the source: 36 of the 38 object files in the last row were generated from specifications by language models.

// ============================================================================
// 8. What Bob relies on
// ============================================================================

= What Bob Relies On

Bob's conclusion from `shown` relies on the verifier being sound: on its never answering `shown` for code that breaks its contract. Nobody should have to accept that on one party's word, or in one way only. Table 4 lists four ways to come to confidence in the verifier: what each rests on, and where each stands.

#booktable(
  4, "Four ways to confidence in the verifier",
  columns: (1.50in, 2.90in, 2.40in),
  ([Way], [What it rests on], [Where it stands]),
  [*A proof of soundness*], [The verifier is written in Lean 4, and Lean checks a proof that whenever the verifier answers `shown`, the code keeps its contract, its trace line included, on the model of the processor that the instruction tables give. This rests on Lean's own checker and on three standard axioms (`propext`, `Classical.choice`, `Quot.sound`).], [Done for both processors, for conventions of a function's own, and for tail calls: 11 theorems.],
  [*The tables match the processors*], [A row of a table says what one instruction does. A row is compared with a real processor on random instances. The AArch64 rows are also proved in Lean to agree with Google DeepMind's model of that instruction set.], [x86-64: #F.tables.x86_rows rows, #F.tables.x86_rows_run_on_a_processor of them compared with processors. AArch64: #F.tables.arm64_rows rows, all proved to agree with the model, #F.tables.arm64_rows_run_on_a_processor compared with an Apple M6. The rows not compared are those for calls, returns and jumps, and one for the address of data.],
  [*Reading it, or a second verifier*], [Bob reads the verifier himself, or checks the same proof files with a second verifier written apart from the first.], [Proof arithmetic steps carry explicit starting rows (`r ...`), independent of any verifier's internal fact order. An independent pure-Python verifier (`verify2.py`, ~940 lines, zero code shared with Lean) verifies the same `.statement` and `.proof` files on both processors for the scalar, byte, and loop fragment.],
  [*A verifier written in Ode*], [The verifier's own machine code, verified against its specification once another method above anchors the base.], [Small verifier building blocks are verified; the `all_zero` routine of section 2 is one pattern.],
)

== Multi-File Programs

Multi-file programs connect files through explicit linked local namespaces (`use alias = "file.ode"`), qualifying imported definitions and functions as `alias.name`. Imports are non-transitive, diamond imports are deduplicated, and splitting a program across files produces the exact same canonical `.ocl` contract and 52-character BLAKE3 identifier as a single file.

== Scope and Limits

Ode verifies pure-computation functions: they are given memory and numbers, and they return. It does not cover:

- system calls, input and output, threads, or dynamic memory allocation;
- full vector and record-layout coverage in the standalone Python second verifier (`verify2.py`);
- a complete, machine-checked grammar covering every optional clause (Appendix B summarizes the core surface syntax).

== Sizes

Two sizes are recorded with each revision, as measures of how complicated Ode is: the length of this report, and the size of what Bob relies on. Table 5 gives them.

#booktable(
  5, "Sizes at this revision",
  columns: (2.10in, 1.50in, 3.20in),
  align: (left, right, left),
  ([What], [Size], [What is counted]),
  [This report], [#context counter(page).final().first() pages], [With #context figs.final().first() figures and #context tabs.final().first() tables.],
  [The verifier and its model], [#commas(F.lean.model_lines) lines], [#F.lean.model_files Lean files: what the machine does, what a contract means, and what the verifier accepts. The largest, `Core.lean`, has #commas(F.lean.core_lines) lines.],
  [The proof of soundness], [#commas(F.lean.sound_lines) lines], [#F.lean.sound_files Lean files. Lean checks them; Bob need not read them.],
  [The instruction tables], [#F.tables.x86_rows and #F.tables.arm64_rows rows], [x86-64 and AArch64.],
)

// ============================================================================
// Appendix A: commands
// ============================================================================

#heading(level: 1, numbering: none)[Appendix A · Commands]

Table 6 lists the commands of the tool (`lang/ode_tool.py`), each with its main arguments and what it does. Bob needs only `audit`, and `spec-test` if he wishes to try a contract's definitions on inputs of his own.

#booktable(
  6, "The commands",
  columns: (3.60in, 3.20in),
  ([Command], [What it does]),
  [`canon SRC [--fn NAME] [--out-dir DIR]`], [Prints the canonical contract's 52 characters; with `--out-dir`, writes the contract into a file named by them.],
  [`pack SRC --fn NAME --target T --out OBJ --proof PROOF`], [Compiles, finds the proof, makes the object file and the proof file, and audits them.],
  [`audit OBJ --proof PROOF [--expect-contract ID]`], [Bob's check (section 6). `--show-contract` prints the contract that was verified.],
  [`spec-test OCL --call NAME --arg JSON`], [Evaluates a definition on the inputs given.],
  [`check SRC [--fn NAME] [--target T]`], [Compiles, finds the proof, and runs the verifier.],
  [`advise SRC --fn NAME`], [Reports the counts that bear on speed (section 6).],
  [`compare A B --fn NAME`], [Sets two variants of a function side by side.],
  [`refute SRC SPEC [--cases N]`], [Runs the code on particular cases, looking for one that breaks the contract.],
  [`serve`], [Takes the same requests over a pipe, keeping the tables loaded.],
)

#heading(level: 1, numbering: none)[Appendix B · Core Surface Syntax]

The core surface syntax of a `.ode` file consists of six top-level forms:

#block(width: 6.80in, fill: ivory, stroke: 0.5pt + rulecol, radius: 2.5pt, inset: (x: 10pt, y: 8pt))[
  #set par(justify: false, leading: 0.48em)
  #raw(block: true, "file         ::= ( use_decl | const_decl | layout_decl | def_decl | inline_fn | fn_decl )*\nuse_decl     ::= 'use' IDENT '=' STRING\nconst_decl   ::= 'const' IDENT '=' expr\nlayout_decl  ::= 'layout' IDENT INT '{' field (',' field)* '}'\ndef_decl     ::= 'def' IDENT '(' params ')' '{' expr '}'\ninline_fn    ::= 'inline' 'fn' IDENT 'for' arch '(' params ')' inline_clauses '{' stmt* '}'\nfn_decl      ::= 'fn' IDENT '(' typed_params ')' clause* '{' target_block+ '}'\nclause       ::= 'requires' expr | 'ensures' target '=' expr | 'returns' expr\n               | 'trace depends on' ('nothing' | expr_list) | 'decreases' expr | 'stack' expr\ntarget_block ::= 'for' ('x86_64' | 'arm64') calling_opt '{' stmt* '}'")
]

#v(0.8em)
#align(center)[
  #text(font: "Palatino", size: 8.2pt, fill: slate, style: "italic")[
    Ode — informally, Object-code Direct Evidence. Revision #rev · November 2026.
  ]
]
