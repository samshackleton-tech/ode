// The Ode Language Report, Revision 11 (November 2026).
//
// Every listing in this report is read from a file that the repository's tests compile and verify, and
// repository counts are read from facts.json (make_facts.py).
// Build (from the repository root):
//   pypy3 paper/render-paper.py

#let rev      = 11
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

// --- Text read from tested repository files ---

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
#let step_x86 = quad_from_step.slice(0, quad_from_step.position("    for arm64 calling {")).trim(at: end) + "\n    // ... for arm64 calling { ... }\n}"
#let quad_x86 = quad.slice(quad.position("fn quad("), quad.position("    for arm64 stack 16 {")).trim(at: end) + "\n    // ... for arm64 stack 16 { ... }\n}"

#let pad_contract = excerpt("/proof-core/examples/arm64/pad_arm64.spec", "contract b3l_pad_arm64(", "\n}")
#let equal_ct_contract = excerpt("/proof-core/test_trace_proposal.py", "contract t_equal_ct(", "\n}")

// --- Page: an asymmetric grid on US Letter ---
//   main column 4.50in, gutter 0.35in, margin notes 1.95in, full span 6.80in

#set page(
  width: 8.5in,
  height: 11in,
  margin: (top: 0.78in, bottom: 0.76in, left: 0.85in, right: 3.15in),
  header: context {
    let pg = counter(page).get().first()
    if pg > 1 {
      let top_on_page = query(heading.where(level: 1)).filter(h =>
        h.location().page() == pg and h.location().position().y < 1.6in
      )
      let prev = query(selector(heading.where(level: 1)).before(here())).filter(h =>
        h.location().page() < pg
      )
      let title = if top_on_page.len() > 0 {
        top_on_page.first().body
      } else if prev.len() > 0 {
        prev.last().body
      } else {
        [Ode]
      }
      block(width: 6.80in, below: 0pt)[
        #set text(font: "Palatino", size: 7.9pt, fill: slate, tracking: 0.06em)
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
          [#text(size: 7.6pt, fill: muted)[Object-code Direct Evidence · Revision #rev]],
          [#counter(page).display()],
        )
      ]
    }
  },
)

#set text(font: "Palatino", size: 9.8pt, fill: ink, lang: "en")
#set par(justify: true, leading: 0.64em, spacing: 0.84em, first-line-indent: 0pt)
#set heading(numbering: "1.1")

#show heading.where(level: 1): it => {
  block(breakable: false, sticky: true, above: 1.55em, below: 0.72em, width: 6.80in)[
    #set par(justify: false)
    #if it.numbering != none [
      #text(fill: accent, size: 11.8pt, weight: "bold")[§ #counter(heading).display()]
      #h(0.45em)
    ]
    #text(fill: ink, size: 12.6pt, weight: "bold")[#it.body]
    #block(above: 5pt, below: 0pt, line(length: 100%, stroke: 0.55pt + rulecol))
  ]
}

#show heading.where(level: 2): it => {
  block(breakable: false, sticky: true, above: 1.25em, below: 0.58em)[
    #set par(justify: false)
    #if it.numbering != none [
      #text(fill: accent, size: 9.8pt, weight: "semibold")[#counter(heading).display()]
      #h(0.42em)
    ]
    #text(fill: ink, size: 10.3pt, weight: "bold")[#it.body]
  ]
}

// Code in prose and listings: keep short literals unbroken across line ends.
#show raw.where(block: false): it => box(text(font: "Menlo", size: 0.89em, fill: charcoal)[#it.text])
#show raw.where(block: true): set text(font: "Menlo", size: 7.4pt, fill: ink)

// --- Building blocks ---

#let figs = counter("figures")
#let tabs = counter("tables")

#let fullwidth(body) = block(width: 6.80in, breakable: false, above: 0.90em, below: 0.95em)[#body]

#let with_note(note, above: 0.80em, body) = block(width: 6.80in, breakable: false, above: above, below: 0.80em)[
  #grid(
    columns: (4.50in, 0.35in, 1.95in),
    align: (top, top, top),
    [#body],
    [],
    [
      #set par(justify: false, leading: 0.53em, spacing: 0.42em)
      #set text(font: "Palatino", size: 7.9pt, fill: slate)
      #note
    ],
  )
]

#let with_rubric(title, note, above: 0.80em, body) = with_note(
  [
    #text(fill: accent, weight: "bold", size: 7.4pt, tracking: 0.07em)[#upper(title)]
    #v(2pt)
    #note
  ],
  above: above,
  body,
)

// A listing: a quiet ground and a hairline at its left.
#let listing(label: none, strong: false, width: 100%, size: 7.4pt, body) = block(
  width: width,
  breakable: false,
  fill: if strong { sand } else { ivory },
  stroke: (left: 1.4pt + (if strong { charcoal } else { slate })),
  inset: (left: 10pt, right: 8pt, top: 6pt, bottom: 6pt),
  above: 0.55em,
  below: 0.72em,
)[
  #if label != none [
    #text(font: "Palatino", size: 7.3pt, fill: if strong { ink } else { slate }, weight: "bold", tracking: 0.07em)[#upper(label)]
    #v(2pt)
  ]
  #set par(justify: false, leading: 0.46em)
  #show raw.where(block: true): set text(size: size)
  #body
]

#let caption(kind, num, title, body) = block(width: 5.95in)[
  #set par(justify: false, leading: 0.52em)
  #text(size: 8.3pt, fill: accent, weight: "bold")[#kind #num.]
  #h(0.35em)
  #text(size: 8.3pt, fill: ink, weight: "bold")[#title.]
  #if body != [] [
    #h(0.25em)
    #text(size: 8.2pt, fill: charcoal)[#body]
  ]
]

#let fig(num, img_path, title, body) = fullwidth[
  #figs.step()
  #image(img_path, width: 6.80in)
  #v(5pt)
  #caption("Figure", num, title, body)
]

// A table with rules above and below only, generous vertical breathing room, and its caption above it.
#let booktable(num, title, columns: auto, align: left, header, ..rows) = block(width: 6.80in, breakable: true, above: 1.15em, below: 1.05em)[
  #tabs.step()
  #block(sticky: true, below: 6pt)[#caption("Table", num, title, [])]
  #set text(size: 8.4pt)
  #set par(justify: false, leading: 0.50em)
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
  #text(size: 12.2pt, style: "italic", fill: slate)[Native Machine Code Checked Against a Canonical Contract]
  #v(8pt)
  #line(length: 100%, stroke: 0.9pt + ink)
  #v(5pt)
  #grid(
    columns: (1fr, auto),
    [#text(size: 8.5pt, style: "italic", fill: slate)[Object-code Direct Evidence — exact instructions, separate proof files, independent audit.]],
    [#text(size: 8.3pt, fill: slate)[November 2026]],
  )
]

#v(0.65em)

Suppose you need a fast cryptographic hash, parser, or memory routine compiled to native x86-64 or AArch64 machine code. You did not write it, and you do not wish to read three thousand lines of assembly or rely on a compiler you cannot inspect. Test vectors confirm the binary on chosen inputs; they tell you nothing about the next input, reads past a buffer end, or branches depending on key material.

Ode separates what a routine _promises_ from how it is _built_. The promise is a short mathematical _contract_, embedded in the `.ode.ocl` section of the compiled ELF64 object file (`.o`) and identified by its 52-character BLAKE3 hash. The maker (_Alice_) writes the machine instructions for each target and delivers two files: the `.o` object file and a separate `.proof` file. The auditor (_Bob_) obtains the expected contract independently (from a published specification or release record, or by inspecting the extracted contract text), then runs `ode audit`—which invokes a Lean 4 verifier (`odeverify`)—on the machine bytes, contract, and proof. If a sound verifier answers `shown`, those bytes satisfy the contract for every input meeting its preconditions. Errors in Alice's compiler, assembler, or proof finder cannot forge a valid proof; Bob relies instead on the verifier, the object-to-statement reader, and the instruction tables (section 8).

#fig(
  1,
  "figures/fig1-boundary.svg",
  "What crosses from the maker to the auditor",
  [Alice compiles `.ode` source into an ELF64 object file (carrying its canonical contract in `.ode.ocl`) and a separate `.proof` file. Bob checks those two files against his independently expected contract identifier using the audit tool, the verifier, and the instruction tables.],
)

Sections 1–3 set out the design principles, contract language, memory framing, and trace policies. Sections 4–5 cover writing code, `use` modules, and cheap internal calls. Sections 6–8 present Bob's audit workflow, verified programs and benchmarks, and Bob's reliance set.

// ============================================================================
// 1. Design principles
// ============================================================================

#pagebreak()

= Design Principles

Four engineering decisions govern Ode's design.

#with_rubric(
  "Reliance sets",
  [A _reliance set_ is the set of components one party depends on for one conclusion (Miller, 2006). Bob's set for the verdict `shown` is drawn in Figure 1 and audited in section 8.],
)[
  *1. Keep what Bob relies on small.*
  Alice wants fast proof search and convenient notation; Bob wants as little as possible between the contract he reads and the machine bytes that execute. Ode separates _finding_ a proof (the prover, on Alice's side) from _checking_ a proof (the verifier, on Bob's side). Proof search, linear-inequality elimination, speed advice, and source shorthand stay on Alice's side; Bob runs the verifier on the compiled object bytes and proof steps.
]

*2. Keep the processor visible.*
Optimizing compilers insert stack frames, spill registers, and reorder operations in ways that defeat both hand-tuned performance and side-channel inspection. In Ode, every processor instruction is written explicitly, and higher-level shorthand expands deterministically to fixed instructions. When an operand combination cannot be encoded on the target processor, the compiler reports the source line rather than inserting hidden moves or stack spills.

*3. A contract is a closed specification.*
A contract declares everything a function may assume and everything it may do: which memory regions it may read and write, how much stack it and its callees may use, which processor extensions it needs, why its loops terminate, and what its instruction and memory-address trace may depend on. A sound verifier accepts no proof for code that touches undeclared memory, leaves callee-saved registers altered, or exceeds its stack bound.

*4. Two processors under one verifier.*
Building on a single architecture bakes that architecture's habits into the contract model. Ode targets x86-64 and AArch64 under one verifier and one contract language. Because a canonical contract names no register and no instruction, the x86-64 and AArch64 implementations of one function verify against the exact same canonical contract text and identifier.

// ============================================================================
// 2. Specifications and contracts
// ============================================================================

= Specifications and Contracts

To audit a binary without reading its instructions, Bob needs a mathematical specification that cannot be confused with machine behavior. Machine arithmetic wraps at 32 or 64 bits, and a read past the end of a buffer accesses memory outside the permitted region (faulting or reading unrelated data). Ode specifications use exact whole numbers and finite lists defined by equations.

Consider a concrete example: `all_zero` checks whether every byte of an `n`-byte buffer is zero (`[0, 0]` returns `1`; `[0, 7]` returns `0`; `[]` returns `1`), and may stop early on the first nonzero byte.

#listing(label: "paper/examples/all_zero.ode — specification and contract")[#raw(az_contract, block: true)]

The two `def` blocks are mathematics. For `0 <= at <= len(a)`, `zero_from(a, at)` returns `1` when every byte of `a` from index `at` onward is zero and `0` otherwise; `zeros(a)` starts at `0`. What decreases on each recursive call is the remaining suffix length `len(a) - at`, guaranteeing termination. The `fn` block is the contract of `all_zero`: given `a` (an address of `n` readable bytes) and `n` (an unsigned 64-bit integer), the function returns `zeros(a)`. Because an early-exit scan reveals the position of the first nonzero byte, the contract declares `trace depends on a, n`. `stack 0` promises zero local stack workspace beyond the calling convention's return mechanism. Bob can evaluate definitions on concrete inputs (`ode spec-test`), while the verifier's `shown` verdict covers every input that satisfies the contract's preconditions.

== Kinds of Values

Specifications speak of seven kinds of values (Table 1). Definitions are pure equations (`const`, `def`, and `sequence`, which defines a list from a starting element and recurrence). Every recursive definition must decrease a well-founded measure; there is no mutation and no imperative loop inside a specification.

#booktable(
  1, "The seven kinds of values in a specification",
  columns: (0.95in, 1.95in, 3.90in),
  ([Kind], [Values], [Operations]),
  [`number`], [Exact non-negative integers ($0, 1, 2, ...$)], [`+` and `*` are exact; `/` and `%` give integer quotient and remainder. `a - b` is defined only when `a >= b` (never wraps).],
  [`byte`], [Integers `0` to `255`], [One byte of memory; indexing a byte list `a[i]` yields a `byte`.],
  [`word`], [32-bit unsigned values], [`+` wraps modulo $2^32$; bitwise `&`, `|`, `^`; `x >>> k` is 32-bit right rotation by `k` bits.],
  [`counter`], [64-bit unsigned values], [Wraps modulo $2^64$ under `+`; `lo(c)` and `hi(c)` extract low and high 32-bit words.],
  [`list`], [Finite ordered sequences, 0-indexed], [`len(xs)`, `xs[i]`, half-open slice `xs[a .. b]` (indices `a` through `b - 1`), `xs ++ ys`, `[e for i in a..b]`.],
  [`bytes`], [A `list` of `byte` values], [`words(bs)` decodes every four bytes as a little-endian `word`; `bytes_of(ws)` encodes back.],
  [`record`], [Named fields], [`{h: a, length: b}` and `r.h`. A `layout` maps each field to a byte offset in memory.],
)

Three operator signs keep distinct roles across Ode files: `==` tests mathematical equality, `:=` (in code blocks) stores a value into a register or stack slot, and `=` binds a name or postcondition (`const ROOT = 8`, `reg idx = rcx`, `ensures out = E`).

== Canonical Contracts Without Author Names

Identifiers chosen by an author—such as a function named `check_signature` or a reassuring comment—can mislead an auditor past a missing condition. The text Bob audits therefore strips comments and author-chosen names. Figure 2 shows how `ode canon` transforms `all_zero` into its canonical contract.

#fig(
  2,
  "figures/fig2-canon.svg",
  "From authored source to canonical contract and BLAKE3 identifier",
  [Left: the authored contract from `all_zero.ode`. Center: canonical `.ocl` output of `ode canon` (comments stripped; definitions, parameters, and arguments numbered by first mention, e.g., `zero_from` → `f1`). Right: the 52-character base-32 BLAKE3 digest and an optional display glossary.],
)

`ode canon` performs three deterministic steps: it removes comments and unreachable definitions; it replaces every remaining identifier by a numbered placeholder in order of first appearance from the contract (`a0`, `a1` for arguments; `f0`, `f1` for definitions; `p0`, `p1` for parameters); and it omits target-specific `calling` clauses (section 5), which name hardware registers. Consistently renaming an argument or helper never changes the resulting canonical `.ocl` text or its digest (though algebraically distinct formulas produce distinct canonical texts).

The contract's sole identifier is the 256-bit BLAKE3 hash (O'Connor et al., 2020) of the canonical text, encoded in 52 lowercase RFC 4648 base-32 characters (`a`–`z`, `2`–`7`). In a packed object file, the exported linker symbol is `ode_` followed by those 52 characters, and a standalone `.ocl` file is named `<52-char-ID>.ocl`. Tools hash `.ocl` files before reading them and refuse any mismatch. An optional glossary maps numbered names back to human labels (`a0 = a`, `f1 = zero_from`); glossaries are non-authoritative display metadata that never enter the hash, so Bob verifies the canonical contract text (and its expected identifier obtained independently from a specification or release record) rather than relying on Alice's labels.

// ============================================================================
// 3. What a contract promises
// ============================================================================

= What a Contract Promises

A verified contract establishes an if–then guarantee:

- *If the caller* satisfies every `requires` precondition, passes valid non-overlapping memory regions, and runs on a processor supporting every declared `needs` extension,
- *then the function* terminates, satisfies every `ensures` and `returns` postcondition, writes only to declared output regions and up to its declared `stack` bytes, restores callee-saved registers and the stack pointer, and exhibits an instruction-and-address trace depending only on what `trace depends on` names.

On inputs that violate `requires`, the contract promises nothing.

== Memory: Pieces, Disjointness, and Lending

A machine address carries no length and no owner. Without explicit bounds, a caller could retain no fact about memory across a call. Contracts therefore describe _pieces_ of memory—each pointer argument paired with a length (`64 bytes`, or `n bytes` where `n` is another argument). Below is an internal helper contract from our verified AArch64 BLAKE3 implementation that copies `n` bytes from `src` into a 64-byte `block` and zero-pads the remainder (`padded(src)`):

#listing(label: "Internal helper contract with two pieces of memory (BLAKE3 padding)")[#raw(pad_contract, block: true)]

#with_note([
  Adjacent pieces whose byte intervals touch at an endpoint (such as `[0, 32)` and `[32, 96)`) have no byte in common and satisfy `no_overlap`.
])[
  A function may read any piece passed to it, and may write only pieces named in `ensures` (which states the final value) or `writes` (which grants write permission without fixing a single final formula). `requires no_overlap(block, src)` obliges the caller to pass disjoint memory intervals.
]

A caller _lends_ whole pieces or sub-slices to its callees—for example, lending bytes `[32, 96)` of a 120-byte `node120` record as `block` (Figure 3). A caller can lend no bytes it does not hold, and cannot lend a read-only piece as writable. After the call returns, the caller knows `ensures` for the lent slice and retains every prior fact about the untouched bytes.

#fig(
  3,
  "figures/fig3-memory.svg",
  "A caller lends a sub-slice of a record",
  [The caller's pieces are pairwise disjoint. It lends `input` read-only as `src` and the `[32, 96)` field `nd.block` read-write as `block`. Every other field of `nd` is preserved across this call.],
)

Each function owns up to `stack N` bytes of local stack space for the duration of the call (or a formula such as `18688 + 384 * bits(len / 1024)` for BLAKE3's recursive tree depth, where `bits(k)` is the bit-length of `k`, with `bits(0) = 0`), may lend stack slices to callees, and must restore the stack pointer on return. Read-only program data (`.rodata`) is readable and never writable.

#pagebreak()

== Trace Policies and Constant-Time Execution

A routine can return the right answer while leaking a key through timing or cache behavior. Ode models the architectural _trace_ of an execution: the sequence of instruction addresses executed and memory addresses accessed as defined by the instruction tables.

#with_rubric(
  "Model boundary",
  [Equal architectural traces rule out branches and cache-line addresses depending on inputs kept out of the trace, but do not model microarchitectural speculation, power draw, or data-dependent instruction latency.],
)[
  A contract's `trace depends on` clause states a two-run property: _given the same starting buffer addresses and lengths, if two valid calls agree on every value named in `trace depends on`, then both runs execute the exact same sequence of instructions and touch the exact same memory addresses, regardless of how unlisted inputs differ._
]

Consider comparing two `n`-byte buffers for equality. An early-exit loop stops at the first differing byte and verifies only with `trace depends on a, b, n`. A branchless loop accumulates byte differences across all `n` positions and verifies against this contract (where `same_ct(a, b)` is the pure mathematical equality predicate returning `1` when all bytes match and `0` otherwise):

#listing(label: "Constant-time equality contract (trace depends on length alone)")[#raw(equal_ct_contract, block: true)]

Omitting `trace depends on` (or writing `trace depends on nothing`) is strictest by default: no input scalar or buffer byte may influence any branch or memory address. A contract may also name a computed expression: a tag-checking caller that branches once to accept or reject writes `trace depends on n, same_ct(want, tag)`, allowing its trace to depend on the single boolean match outcome and nothing else about the tag bytes. When a function returns an abstract result (`returns r` constrained by `ensures`), a `result depends on` clause may declare which inputs can affect `r`.

Inside a function, the verifier enforces one rule: every branch condition and every computed memory address must depend only on entry buffer addresses and values listed in that function's `trace depends on` clause.

// ============================================================================
// 4. Writing code
// ============================================================================

= Writing Code

Hand-written assembly leaves register-alias collisions, miscounted stack offsets, and x86-64/AArch64 contract drift to human review. Ode keeps exact instruction selection with the programmer while checking that bookkeeping mechanically.

An `.ode` file contains pure specifications (`const`, `def`, `layout`, `sequence`) and functions (`fn`), each holding its contract followed by target blocks `for x86_64 { ... }` and `for arm64 { ... }`. A file is a closed namespace: nothing outside it is in scope unless explicitly imported with `use` (section 4.2).

== Register Aliases, Frames, and Structured Shorthand

Every line inside a target block is either a processor instruction from `core/x86.tab` or `arm64/arm64.tab` or one of the fixed-expansion forms below:

- `reg idx = rcx` — declares a readable register alias (preventing accidental reuse of raw register names).
- `dst := src` — expands to one `mov` (or `lea` for a stack-frame field address). Source and destination widths must match; Ode never silently widens or truncates.
- `frame { saved: 7 * u64, ... }` — names stack-frame fields and byte offsets (`frame.size`). Out-of-bounds slot indices are reported at the source line.
- `inline fn g for arm64 (a: vec, b: vec, t: vec) distinct(a, b, t) changes a, t { ... }` — expands straight-line instruction blocks inline with compile-time checks on register disjointness (`distinct`) and modified registers (`changes`).
- `for i in 0..8 { ... }` — compile-time unrolling substituting `$i` with `0..7` (not a runtime machine loop).
- `loop { ... break if ult ... }` and `if eq { ... } else { ... }` — structured branches over flags set by an explicit comparison instruction.
- `@label:` and `place { ... }` (`name x = reg`, `fact E`, `decreases M`, `wrote ...`, `keep ...`, one per line) — branch labels and loop invariants read by the prover and verifier (never emitted as machine bytes).

Figure 4 shows both target blocks of `all_zero`. Whenever control reaches `@loop`, every byte at indices `[0, idx)` has already tested zero, so checking the suffix from `idx` equals `zeros(a)` and `n - idx` strictly decreases each iteration. On both targets, `cur` and `cur64` (`edx`/`rdx`, `w4`/`x4`) alias the 32-bit and 64-bit views of one register so the byte load zero-extends cleanly into the 64-bit comparison.

#fullwidth[
  #figs.step()
  #grid(
    columns: (1fr, 10pt, 1fr),
    [#listing(label: "For x86-64 (" + str(M.all_zero.x86_64.instructions) + " insns, " + str(M.all_zero.x86_64.bytes) + " B)", size: 6.95pt)[#raw(az_x86, block: true)]],
    [],
    [#listing(label: "For AArch64 (" + str(M.all_zero.arm64.instructions) + " insns, " + str(M.all_zero.arm64.bytes) + " B)", size: 6.95pt)[#raw(az_arm, block: true)]],
  )
  #v(2pt)
  #caption("Figure", 4, "One contract, two processors", [Both target blocks of `all_zero` from `paper/examples/all_zero.ode` (instruction and byte counts are emitted machine code, excluding `place` annotations). Both verify `shown` against the same canonical contract from Figure 2.])
]

== Multi-File Programs (`use`)

Larger programs split pure specifications from target implementations, or share helper libraries across files, via explicit linked local namespaces:

```
use eq = "hash_eq_ct_spec.ode"
```

Imported definitions and functions are referenced only through their local alias (`eq.ct_bytes_eq`). Imports are non-transitive (importing `B` does not expose `B`'s imports), and shared diamond dependencies are deduplicated. Reorganizing identical definitions across `use`-linked files produces the exact same canonical `.ocl` contract and 52-character BLAKE3 identifier as a single file.

// ============================================================================
// 5. Calls
// ============================================================================

= Calls Between Ode Functions

External C or Rust callers enter exported Ode functions via the platform C calling convention: System V AMD64 on x86-64 (arguments in `rdi, rsi, rdx, rcx, r8, r9`; return in `rax`; callee-saved `rbx, rbp, r12..r15`) and AAPCS64 on AArch64 (arguments in `x0..x7`; return in `x0`; callee-saved `x19..x29` and the low 64 bits of `v8..v15`).

Between private Ode helpers inside a single object file, C calling conventions often force needless argument shuffles and callee-saved register spills. At 64-byte BLAKE3 inputs, call overhead and an extra block copy can take nearly as long as the compression itself (section 7). Ode provides three verified ways to eliminate that overhead.

== Private Calling Conventions

A private helper (local to its packed object file, never exported to C) may declare a `for <arch> calling { ... }` block with one clause per line (`in param = reg, ...`, `out = reg`, and `preserves ...`). Below, `step` preserves `rdi`, `rsi`, and `r8`, allowing `quad` to call `step` twice without spilling a single register to the stack:

#fullwidth[
  #grid(
    columns: (3.62in, 0.16in, 3.02in),
    [#listing(label: "Helper with private calling (quad.ode)", size: 6.45pt)[#raw(step_x86, block: true)]],
    [],
    [#listing(label: "Caller keeping rdi, rsi, r8 live", size: 6.45pt)[#raw(quad_x86, block: true)]],
  )
]

#with_rubric(
  "Calling restrictions",
  [To prevent conflicting bindings or losing the return address, `calling` forbids placing arguments or results in the stack pointer (or AArch64 `x30`), mapping two arguments to one register, or listing the return register in `preserves`.],
)[
  Any live caller value placed in a register listed in `preserves` survives the call without stack spills. Exported entry points cannot declare custom `calling` blocks; `ode pack` enforces the platform C convention at the external boundary.
]

== Zero-Stack Non-Leaf Callers on AArch64

On AArch64, `bl` overwrites the link register `x30`, so a function calling a helper must save its incoming `x30` somewhere safe. When the helper declares a private convention preserving a caller-saved register such as `x15`, the caller can save `x30` in `x15` across `bl helper`, restore `x30` from `x15`, and return with `stack 0`—avoiding a 16-byte stack frame altogether.

== Tail Calls (`jmp` / `b`)

When a function's final action is to delegate to another function, it may jump directly to the callee (`jmp` on x86-64, `b` on AArch64) so the callee returns straight to the outer caller without an extra call frame or second return. At a tail jump, the verifier checks three groups of conditions:

+ *Machine state:* the stack pointer equals its entry value (and on AArch64 `x30` holds its entry value), and every register the caller must preserve holds its entry value and is preserved by the callee.
+ *Resources and acyclicity:* the callee's stack bound fits inside the caller's `stack` clause, and the callee appears earlier in the proof's acyclic verification order (preventing infinite tail-call cycles).
+ *Contract compatibility:* the callee's `requires` hold at the jump, its postconditions imply the caller's promised `returns`/`ensures`, and its `trace depends on` clause is permitted by the caller's.

#fig(
  5,
  "figures/fig4-calling.svg",
  "Three ways to pass control",
  [Left: standard C ABI at external boundaries (schematic callee-saved spills). Middle: private Ode calling convention preserving `x15` for `x30` on AArch64 (`stack 0`). Right: verified tail call (`jmp`/`b`) reusing the caller's return frame.],
)

// ============================================================================
// 6. Bob's side
// ============================================================================

= Auditing Delivered Artifacts

Before linking an object file into an executable, Bob needs assurance against two failure modes: code hidden in the object file without a proof (such as extra helpers or startup constructors) and substitution of a different contract from the one he reviewed. (After `ode audit`, the linker and build pipeline must preserve the audited object bytes without introducing hooks that were not checked.)

== Packing and Auditing an Object File

`ode pack` compiles a source file into two artifacts: a relocatable 64-bit ELF object file (`.o`) containing the exported function, all local Ode callees, and the canonical contract in `.ode.ocl`; and a separate `.proof` file containing local helper contracts, private calling declarations, and step-by-step proof items. Only the selected exported function is externally visible, under the symbol `ode_<52-char-ID>`.

Bob runs `ode audit` on those two files together with his independently obtained expected contract identifier:

#listing(label: "Bob's audit invocation", width: 6.80in)[
  #raw(block: true, "python3 lang/ode_tool.py audit bundle.o --proof bundle.proof \\\n  --expect-contract jbqyjqpese4s4cq35qxlhaevjvzuaqznquqw6mtlaqleluc25ika")
]

`ode audit` checks five properties: (1) `.ode.ocl` hashes to the 52-character identifier and matches `--expect-contract`; (2) the sole global text symbol is `ode_<52-char-ID>`; (3) 100% of executable bytes in `.text` belong to verified functions; (4) no `.init_array`/`.fini_array` hooks or unresolved external symbol relocations exist; and (5) `odeverify` returns `shown` for every function in bottom-up dependency order.

#fig(
  6,
  "figures/fig5-bundle.svg",
  "Anatomy of a packed object file and proof file",
  [`ode audit` binds the single exported symbol to the BLAKE3 digest of `.ode.ocl`, accounts for 100% of `.text`, rejects init/fini hooks and external calls, and checks `.proof` step by step against the object bytes.],
)

== Outcomes and What Each Means

Reports and tools in Ode distinguish four outcomes cleanly (Table 2). In particular, `no proof found` is inconclusive rather than a defect found, whereas `refused with a proof` presents a concrete counterexample input refuting the contract.

#booktable(
  2, "Outcomes reported by Ode's tools",
  columns: (1.50in, 1.10in, 2.25in, 1.95in),
  ([Outcome], [Reported by], [What happened], [What it does not show]),
  [#text(font: "Menlo", size: 8.0pt, weight: "bold")[shown]], [`odeverify`, `ode audit`, `ode check`], [Every path of the compiled bytes was checked against the contract and proof file and accepted.], [Properties absent from the contract, or hardware bugs outside the instruction table.],
  [#text(font: "Menlo", size: 8.0pt, weight: "bold", fill: accent)[refused with a proof]], [`ode check`, `ode refute`], [A concrete counterexample input demonstrates that the machine code violates the contract. (`odeverify` itself prints `refused` + reason for any rejected proof.)], [Whether another implementation meets the contract.],
  [#text(font: "Menlo", size: 8.0pt, weight: "bold")[no proof found]], [`ode check`, `ode pack`], [No counterexample was found, and the prover could not close a proof obligation.], [That the code is wrong (or right).],
  [#text(font: "Menlo", size: 8.0pt, weight: "bold")[run]], [`ode spec-test`, benchmarks], [Code or specification executed on concrete test inputs.], [Anything about inputs not tested.],
)

// ============================================================================
// 7. Verified programs and speed
// ============================================================================

#pagebreak()

= Verified Programs and Performance

To test Ode on substantial, performance-critical code, we wrote and verified single-threaded BLAKE3 (default 32-byte hash mode) from scratch in `.ode` source on both x86-64 and AArch64. The canonical BLAKE3 contract is 95 lines long and agrees with all 105 official BLAKE3 test vectors via `ode spec-test`. All benchmarks below integrate the verified Ode object file into an experimental branch of BLAKE3-Servil (a hand-tuned Rust/assembly BLAKE3 implementation) and compare against BLAKE3-Servil and the official `blake3` Rust package (version 1.8.7). Throughout, `GiB/s` denotes $2^30$ bytes per second.

== BLAKE3 on x86-64

The x86-64 bundle contains 19 functions (1 exported entry point + 18 local helpers with local contracts), totaling 3,837 instructions across one-block SSE4.1/AVX-512 kernels, 16-way and 32-way AVX-512 SIMD multi-chunk kernels, and tree/short-input glue. One `ode audit` call checks all 19 functions and prints `shown`.

Figure 7 shows medians of 45 interleaved trials on one quiet, reserved core of an AMD Ryzen 7 9700X (Zen 5, Linux). At 64 bytes, the Ode bundle reaches 1.28 GiB/s (99% of BLAKE3-Servil, 160% of `blake3` 1.8.7), up from 0.67 GiB/s for an earlier Ode build that used C calls internally and copied the input block—a combined gain from private calling conventions, tail calls, and removing the extra copy. On larger inputs, Ode reaches 2.93 GiB/s at 4 KiB (88% of BLAKE3-Servil), 7.80 GiB/s at 16 KiB (74%), 9.22 GiB/s at 32 KiB (61%, where the 16-way kernel runs twice before switching to the 32-way kernel at 64 KiB), 14.78 GiB/s at 64 KiB (93%), 16.30 GiB/s at 256 KiB (99%, 132% of `blake3` 1.8.7), and 15.76 GiB/s at 1 MiB (98%).

#fig(
  7,
  "figures/fig6-blake3-perf.svg",
  "Single-threaded BLAKE3 throughput on AMD Ryzen 7 9700X (Zen 5)",
  [Medians of 45 interleaved trials on a dedicated core. Left: short inputs comparing an earlier C-calling + block-copying Ode baseline against the current Ode bundle, BLAKE3-Servil, and `blake3` 1.8.7. Right: categorical throughput sweep from 4 KiB to 1 MiB.],
)

== BLAKE3 on AArch64 and Other Verified Programs

The AArch64 BLAKE3 bundle contains 8 functions (1,891 instructions across 4 `use`-linked `.ode` files), using a 4-way NEON SIMD kernel. On Apple M6 (medians of 45 interleaved trials on a build machine _not reserved for timing_, without a timing lock), throughput is:

#booktable(
  3, "AArch64 BLAKE3 throughput on Apple M6 (machine not reserved for timing; medians of 45 trials)",
  columns: (0.85in, 1.15in, 1.35in, 1.45in, 2.00in),
  align: (left, right, right, right, left),
  ([Size], [Ode (GiB/s)], [vs `blake3` 1.8.7], [vs BLAKE3-Servil], [Notes]),
  [64 B], [1.18], [83%], [—], [Single-block NEON; zero-stack helpers],
  [256 B / 1 KiB], [0.9–1.0], [55% / 49%], [—], [Short-input glue overhead],
  [4 KiB], [2.28], [90%], [approx. 44%], [4-way NEON kernel active],
  [16 KiB–1 MiB], [2.2], [83%–85%], [approx. 31%], [BLAKE3-Servil uses wider unrolling],
)

Table 4 summarizes all verified programs currently in the repository.

#booktable(
  4, "Programs verified shown on x86-64 and AArch64",
  columns: (1.65in, 0.90in, 1.65in, 2.60in),
  ([Program], [Targets], [Code verified], [Scope and properties]),
  [BLAKE3 (one thread)], [x86-64], [19 fns, 3,837 insns], [One-block, 16-way, and 32-way AVX-512 kernels.],
  [BLAKE3 (one thread)], [AArch64], [8 fns, 1,891 insns], [4 `use`-linked `.ode` files; 4-way NEON kernel.],
  [BLAKE3 64 B XOF block], [both], [115 (x86), 125 (arm) insns], [Extendable-output compression; SSE2 & NEON, `stack 0`, `trace depends on nothing`, same ID.],
  [ChaCha20 block], [both], [1,090 (x86), 1,759 (arm)], [16-block AVX-512 / 4-block NEON kernels.],
  [RFC 9669 eBPF subset], [both], [209 (x86), 192 (arm) insns], [11 opcodes, 4 registers, signed relative jumps, bounded step fuel; 6 fns; audits in 0.16 s / 0.20 s.],
  [Two-target routines (5)], [both], [10 `.o` bundles], [RFC 1950 Adler-32, strict RFC 3629 UTF-8, RFC 1071 checksum, ASCII decimal, constant-time `ct_bytes_eq` (`stack 0`, identical ID across targets).],
  [Smaller routines (19)], [both], [38 `.o` bundles], [Base64, ASN.1 DER, LZ4, SHA-256, ChaCha20, hex, varint, and verifier building blocks.],
)

Audit verdicts depend solely on the compiled bytes, contract, and proof—never on source authorship (36 of the 38 `.ode` sources in the last row were generated from specifications by language models).

== Static Advice About Speed (`ode advise`)

Contracts govern correctness and trace policy, not microarchitectural latency. For Alice's tuning loop, `ode advise` reports static code-size, instruction-cache-line, and store-forwarding counts, and checks optional `budget` annotations (such as `max_bytes 64`, `max_icache_lines 1`). Budgets are advisory diagnostics for Alice; they never alter emitted bytes or Bob's verification verdict.

// ============================================================================
// 8. What Bob relies on
// ============================================================================

#pagebreak()

= What Bob Relies On

Bob's confidence in a `shown` verdict rests on three distinct layers: (1) soundness of the verifier relative to the instruction model, (2) fidelity of the instruction tables to real processors, and (3) integrity of the front-end reader that extracts ELF bytes and hashes `.ode.ocl`. Table 5 summarizes the evidence supporting each layer.

#block(width: 6.80in, breakable: true, above: 0.70em, below: 0.70em)[
  #tabs.step()
  #block(sticky: true, below: 4pt)[#caption("Table", 5, "Assurance layers for Bob's reliance set", [])]
  #set text(size: 8.15pt)
  #set par(justify: false, leading: 0.46em)
  #show table.cell: set block(breakable: false)
  #table(
    columns: (1.42in, 2.83in, 2.55in),
    align: left,
    stroke: (x, y) => (
      top: if y == 0 { 0.9pt + ink } else if y == 1 { 0.55pt + slate } else { none },
      bottom: 0.4pt + rulecol.transparentize(40%),
      left: none,
      right: none,
    ),
    inset: (x: 5.5pt, y: 3.4pt),
    table.header(
      text(weight: "bold", size: 8.0pt, fill: ink)[Layer],
      text(weight: "bold", size: 8.0pt, fill: ink)[What it establishes and relies on],
      text(weight: "bold", size: 8.0pt, fill: ink)[Current status],
    ),
    [*Lean 4 soundness proof*], [The primary verifier (`odeverify`) is written in Lean 4 (de Moura & Ullrich, 2021). Eleven machine-checked theorems prove that whenever `odeverify` returns `shown`, the program meets its contract—including two-run trace equality—on the operational model defined by the instruction tables. Relies on Lean's kernel and three standard axioms (`propext`, `Classical.choice`, `Quot.sound`), with zero `sorry`.], [Complete for x86-64 and AArch64, private calling conventions, and tail calls (`test_sound.py`).],
    [*Instruction-table fidelity*], [Two separate checks test whether `core/x86.tab` and `arm64/arm64.tab` match real CPUs: (a) a Lean proof that every AArch64 row agrees with Google DeepMind's `arm64-semantics` formal model; (b) random hardware cross-tests comparing table execution against real processors (sampled tests, not exhaustive proofs).], [x86-64: #F.tables.x86_rows rows (#F.tables.x86_rows_run_on_a_processor sampled on CPU). AArch64: #F.tables.arm64_rows rows (#F.tables.arm64_rows/#F.tables.arm64_rows proved against `arm64-semantics`; #F.tables.arm64_rows_run_on_a_processor sampled on Apple M6). Omitted from CPU sampling: calls, returns, jumps, data-address load.],
    [*Independent second verifier*], [Proof arithmetic steps carry explicit premise rows rather than relying on one verifier's internal fact numbering. An independent pure-Python verifier (`verify2.py`, about 1,240 lines, zero shared verification code with Lean) checks the same intermediate statement and `.proof` files.], [Dual-verifies single- and multi-function scalar, byte, loop, custom-calling, and branch-dispatch proofs on both targets—including `quad.ode` and the full 6-function RFC 9669 eBPF VM (`test_verify2.py`); vector and record-layout instructions are not yet covered in `verify2.py`.],
    [*Front-end reader & ELF audit*], [Before calling `odeverify`, the Python audit wrapper (`ode_tool.py`, `statement.py`, ELF decoders) checks ELF sections/symbols, hashes `.ode.ocl`, and decodes instruction bytes into the verifier's input text. This wrapper is currently in Bob's reliance set.], [Tested across negative controls (tampered bytes, rogue hooks, wrong hashes); not yet proved in Lean.],
    [*Ode-written verifier parts*], [Long-term goal: compile the verifier itself from verified Ode code once an external check anchors the bootstrap.], [Early building blocks only (e.g. `all_zero`, byte scanners); not yet a full verifier.],
  )
]

== Scope and Limits

Ode verifies pure computational functions taking numbers and memory regions and returning to their caller. Its current scope excludes operating-system calls, I/O, concurrency, and dynamic memory allocation; microarchitectural side channels beyond the architectural trace (speculation, power, data-dependent latency); vector and record-layout coverage in `verify2.py`; and a machine-checked parser proof for `Main.lean`, `Reader.lean`, and the Python ELF-to-statement decoder.

== Complexity and Size Inventory

#block(width: 6.80in, breakable: false, above: 0.45em, below: 0.45em)[
  #tabs.step()
  #block(sticky: true, below: 4pt)[#caption("Table", 6, "Sizes of the report, Lean verifier, soundness proofs, and instruction tables", [])]
  #set text(size: 8.2pt)
  #set par(justify: false, leading: 0.45em)
  #table(
    columns: (2.20in, 1.35in, 3.25in),
    align: (left, right, left),
    stroke: (x, y) => (
      top: if y == 0 { 0.9pt + ink } else if y == 1 { 0.55pt + slate } else { none },
      bottom: 0.4pt + rulecol.transparentize(40%),
      left: none,
      right: none,
    ),
    inset: (x: 5.5pt, y: 3.4pt),
    table.header(
      text(weight: "bold", size: 8.0pt, fill: ink)[Component],
      text(weight: "bold", size: 8.0pt, fill: ink)[Size],
      text(weight: "bold", size: 8.0pt, fill: ink)[Notes],
    ),
    [Language report], [#context counter(page).final().first() pages], [#context figs.final().first() figures and #context tabs.final().first() tables.],
    [Lean verifier & machine model], [#commas(F.lean.model_lines) lines], [#F.lean.model_files Lean files defining machine semantics, contracts, and `odeverify` (`Core.lean`: #commas(F.lean.core_lines) lines).],
    [Lean soundness proofs], [#commas(F.lean.sound_lines) lines], [#F.lean.sound_files Lean files checked by Lean's kernel; Bob need not read them.],
    [Instruction tables], [#F.tables.x86_rows / #F.tables.arm64_rows rows], [`core/x86.tab` (x86-64) and `arm64/arm64.tab` (AArch64).],
  )
]

#pagebreak()

// ============================================================================
// Appendix A: commands
// ============================================================================

#heading(level: 1, numbering: none)[Appendix A · Commands]

Every command below is invoked from the repository root as `python3 lang/ode_tool.py <cmd> ...` (written `ode <cmd>` in the text). Auditor commands appear first; Bob needs only `audit` (and optionally `spec-test`).

#block(width: 6.80in, breakable: true, above: 0.70em, below: 0.70em)[
  #tabs.step()
  #block(sticky: true, below: 4pt)[#caption("Table", 7, "CLI commands of lang/ode_tool.py", [])]
  #set text(size: 8.2pt)
  #set par(justify: false, leading: 0.45em)
  #show table.cell: set block(breakable: false)
  #table(
    columns: (3.65in, 3.15in),
    align: left,
    stroke: (x, y) => (
      top: if y == 0 { 0.9pt + ink } else if y == 1 { 0.55pt + slate } else { none },
      bottom: 0.4pt + rulecol.transparentize(40%),
      left: none,
      right: none,
    ),
    inset: (x: 5.5pt, y: 3.4pt),
    table.header(text(weight: "bold", size: 8.0pt, fill: ink)[Command], text(weight: "bold", size: 8.0pt, fill: ink)[Purpose]),
    [`audit OBJ --proof PROOF [--expect-contract ID] [--show-contract]`], [Bob's check (section 6): verifies 100% of `.text`, checks `.ode.ocl` against `ID`, and prints the verified contract with `--show-contract`.],
    [`spec-test OCL --call NAME --arg JSON [--glossary G]`], [Evaluates a contract definition on JSON inputs (`NAME` is a canonical name like `f0`, or an authored name when `--glossary` is given).],
    [`canon SRC [--fn NAME] [--out-dir DIR]`], [Prints the 52-character BLAKE3 identifier; with `--out-dir`, writes `<ID>.ocl`.],
    [`pack SRC --fn NAME --target T --out OBJ --proof PROOF`], [Compiles (`T` = `x86_64` or `arm64`), proves, packs `.o` + `.proof`, and audits them.],
    [`check SRC [--fn NAME] [--target T]`], [Development loop: compiles, proves, verifies, and reports counterexamples on failure.],
    [`advise SRC --fn NAME`], [Reports static code-size, cache-line, and `budget` diagnostics (section 7.3).],
    [`compare A B --fn NAME`], [Compares static advice and verification verdicts of two `.ode` variants.],
    [`refute SRC SPEC [--cases N]`], [Runs concrete fuzz cases looking for a counterexample that violates the contract.],
    [`serve`], [Line-delimited JSON stdin/stdout server reusing loaded instruction tables.],
  )
]

#heading(level: 1, numbering: none)[Appendix B · Core Surface Grammar]

This summary covers the core surface syntax of `.ode` source files (`arch` is `x86_64` or `arm64`; `stmt` and `expr` follow sections 2 and 4; optional clauses `writes`, `needs`, `result depends on`, `frame`, and `place` are shown in the productions below):

#listing(label: "Core surface grammar (summary)", width: 6.80in, size: 7.25pt)[
  #raw(block: true, "file         ::= ( use_decl | const_decl | layout_decl | sequence_decl | def_decl | inline_fn | fn_decl )*\nuse_decl     ::= 'use' IDENT '=' STRING\nconst_decl   ::= 'const' IDENT '=' expr\nlayout_decl  ::= 'layout' IDENT INT '{' field (',' field)* '}'\nsequence_decl::= 'sequence' IDENT '(' params ')' '{' expr ';' expr '}'\ndef_decl     ::= 'def' IDENT '(' params ')' '{' expr '}'\ninline_fn    ::= 'inline' 'fn' IDENT 'for' arch '(' params ')' inline_clauses '{' stmt* '}'\nfn_decl      ::= 'fn' IDENT '(' typed_params ')' clause* '{' target_block+ '}'\nclause       ::= 'requires' expr | 'ensures' target '=' expr | 'writes' IDENT | 'returns' expr\n               | 'needs' IDENT | 'trace depends on' ('nothing' | expr_list)\n               | 'result depends on' ('nothing' | expr_list) | 'decreases' expr | 'stack' expr\ntarget_block ::= 'for' arch ('calling' '{' calling_clause* '}')? ('stack' expr)? '{' frame_opt stmt* '}'\nstmt         ::= reg_decl | place_block | label | assign | loop_stmt | if_stmt | for_unroll | asm_insn")
]

#heading(level: 1, numbering: none)[References]

#block(width: 6.80in)[
  #set text(size: 8.6pt, fill: charcoal)
  #set par(justify: false, leading: 0.54em, spacing: 0.42em)
  - M. S. Miller (2006). _Robust Composition: Towards a Unified Approach to Access Control and Concurrency Control._ PhD thesis, Johns Hopkins University (Section 5.1, reliance sets).
  - J. O'Connor, J.-P. Aumasson, S. Neves, and Z. Wilcox-O'Hearn (2020). _BLAKE3: one function, fast everywhere._ Specification and reference `blake3` crate.
  - L. de Moura and S. Ullrich (2021). _The Lean 4 Theorem Prover and Programming Language._ CADE-28.
  - Google DeepMind (2025). _arm64-semantics_ (Lean 4 formal AArch64 ISA specification in `google-deepmind/code-verification`).
  - D. Thaler, ed. (2024). _BPF Instruction Set Architecture (ISA)._ IETF RFC 9669.
]
