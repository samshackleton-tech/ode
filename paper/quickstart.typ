// The Ode Quickstart.
// Companion to the Ode Language Report (paper/ODE.pdf).
// Every code listing is read directly from a tested `.ode` file in this repository.
// Build (from repository root):
//   typst compile --root . paper/quickstart.typ paper/quickstart.pdf

#let ink      = rgb("#1C1E21")
#let charcoal = rgb("#2E343D")
#let slate    = rgb("#5B6470")
#let muted    = rgb("#7D8590")
#let rulecol  = rgb("#CFC9BC")
#let accent   = rgb("#9E2A2B")
#let ivory    = rgb("#F7F5F0")
#let sand     = rgb("#EEEBE2")

#let dedent4(s) = s.split("\n").map(l => if l.starts-with("    ") { l.slice(4) } else { l }).join("\n")

#let az = read("examples/all_zero.ode")
#let az_contract = az.slice(0, az.position("\n{\n")).trim(at: end)
#let az_x86 = dedent4(az.slice(az.position("    for x86_64 {"), az.position("    for arm64 {")).trim(at: end))
#let az_arm = dedent4(az.slice(az.position("    for arm64 {")).trim(at: end).slice(0, -2).trim(at: end))

#let heq_spec = read("/proof-core/examples/hasher/hash_eq_ct_spec.ode").trim(at: end)
#let heq_code = read("/proof-core/examples/hasher/hash_eq_ct.ode")
#let heq_hdr  = heq_code.slice(0, heq_code.position("\n{\n")).trim(at: end)

#let quad     = read("examples/quad.ode")
#let quad_hdr = quad.slice(quad.position("fn step("), quad.position("    for arm64 calling {")).trim(at: end)

// --- Page: same asymmetric Tufte grid as ODE.pdf ---
#set page(
  width: 8.5in,
  height: 11in,
  margin: (top: 0.85in, bottom: 0.85in, left: 0.85in, right: 3.15in),
  header: context {
    let pg = counter(page).get().first()
    if pg > 1 {
      let on_page = query(heading.where(level: 1)).filter(h => h.location().page() == pg)
      let prev = query(selector(heading.where(level: 1)).before(here()))
      let title = if on_page.len() > 0 { on_page.first().body } else if prev.len() > 0 { prev.last().body } else { [Quickstart] }
      block(width: 6.80in, below: 0pt)[
        #set text(font: "Palatino", size: 7.9pt, fill: slate, tracking: 0.08em)
        #grid(columns: (1fr, auto), [#upper[Ode · Quickstart]], [#emph(title)])
        #v(3pt)
        #line(length: 100%, stroke: 0.45pt + rulecol)
      ]
    }
  },
  footer: context {
    block(width: 6.80in)[
      #line(length: 100%, stroke: 0.4pt + rulecol)
      #v(4pt)
      #set text(font: "Palatino", size: 8.1pt, fill: slate)
      #grid(
        columns: (1fr, auto),
        [#text(size: 7.6pt, fill: muted)[Ode · Practitioner's Quickstart]],
        [#counter(page).display()],
      )
    ]
  },
)

#set text(font: "Palatino", size: 9.8pt, fill: ink, lang: "en")
#set par(justify: true, leading: 0.64em, spacing: 0.85em, first-line-indent: 0pt)
#set heading(numbering: "1.1")

#show heading.where(level: 1): it => {
  block(breakable: false, sticky: true, above: 1.50em, below: 0.70em, width: 6.80in)[
    #set par(justify: false)
    #if it.numbering != none [
      #text(fill: accent, size: 11.8pt, weight: "bold")[§ #counter(heading).display()]
      #h(0.45em)
    ]
    #text(fill: ink, size: 12.6pt, weight: "bold")[#it.body]
    #block(above: 5pt, below: 0pt, line(length: 100%, stroke: 0.55pt + rulecol))
  ]
}

#show raw.where(block: false): it => text(font: "Menlo", size: 0.88em)[#it.text]
#show raw.where(block: true): set text(font: "Menlo", size: 7.3pt)

#let fullwidth(body) = block(width: 6.80in, breakable: false, above: 0.75em, below: 0.75em)[#body]

#let with_note(note, above: 0.75em, body) = block(width: 6.80in, breakable: false, above: above, below: 0.75em)[
  #grid(
    columns: (4.50in, 0.35in, 1.95in),
    align: (top, top, top),
    [#body],
    [],
    [
      #set par(justify: false, leading: 0.52em, spacing: 0.40em)
      #set text(size: 8.0pt, fill: slate)
      #note
    ],
  )
]

#let codebox(title, body, span: 4.50in) = block(
  width: span, breakable: false, above: 0.55em, below: 0.65em,
  fill: ivory, stroke: 0.5pt + rulecol, radius: 2.5pt, inset: (x: 9pt, y: 7pt),
)[
  #set par(justify: false, leading: 0.46em, spacing: 0pt)
  #if title != none [
    #text(font: "Palatino", size: 7.8pt, fill: slate, weight: "semibold")[#title]
    #block(above: 3pt, below: 5pt, line(length: 100%, stroke: 0.35pt + rulecol))
  ]
  #raw(block: true, body)
]

#let notebox(title, body) = block(
  width: 4.50in, breakable: false, above: 0.70em, below: 0.75em,
  fill: sand, stroke: 0.5pt + rulecol, radius: 2.5pt, inset: (x: 10pt, y: 8pt),
)[
  #set par(justify: false, leading: 0.56em, spacing: 0.40em)
  #text(font: "Palatino", size: 8.4pt, fill: charcoal, weight: "bold")[#title]
  #v(3pt)
  #set text(size: 9.0pt, fill: ink)
  #body
]

// --- Title block ---
#block(width: 6.80in, above: 0pt, below: 1.1em)[
  #text(font: "Palatino", size: 8.2pt, fill: accent, weight: "bold", tracking: 0.14em)[ODE · PRACTITIONER'S QUICKSTART]
  #v(4pt)
  #text(font: "Palatino", size: 21.5pt, fill: ink, weight: "bold")[Writing Verified Machine Code in Ode]
  #v(4pt)
  #text(font: "Palatino", size: 10.6pt, fill: slate, style: "italic")[
    A hands-on guide to writing contracts, machine-code bodies, and loop invariants that verify on x86-64 and AArch64.
  ]
  #v(9pt)
  #line(length: 100%, stroke: 0.9pt + charcoal)
]

#with_note([
  *Where to read more:* The full design, formal machine semantics, and reliance-set analysis live in the Language Report (`paper/ODE.pdf`).
])[
  An Ode source file (`.ode`) pairs a short declarative specification with the exact machine instructions you want the processor to execute. You keep full control over registers, stack layout, branches, and calling conventions. A prover searches for a proof behind the scenes; a standalone verifier checks the compiled object bytes directly against the contract.
]

= A First Program: `all_zero`

The best way to read Ode is through a complete program. The file `paper/examples/all_zero.ode` checks whether every byte of an `n`-byte buffer is zero, returning `1` if so and `0` otherwise. It states the specification and contract once, then gives the x86-64 and AArch64 implementations in the same file.

#codebox("paper/examples/all_zero.ode — specification and contract", az_contract, span: 6.80in)

#with_note([
  *Declared effects:* A function may write only to memory named in an `ensures` clause and up to `stack N` bytes below the caller's stack pointer.
])[
  Read the contract line by line. `all_zero` takes a buffer `a` of `n` bytes (`n` is a 64-bit unsigned integer, `< 2^64`) and returns `all_zero_spec(a)`. The clause `trace depends on a, n` states that branches and memory addresses may depend on the length `n` and the bytes of `a` (explained in §4). The clause `stack 0` promises that this leaf function touches zero bytes of stack.
]

#fullwidth[
  #grid(
    columns: (3.32in, 0.16in, 3.32in),
    codebox("x86-64 body", az_x86, span: 3.32in),
    [],
    codebox("AArch64 body", az_arm, span: 3.32in),
  )
]

Inside each target block, `reg name = r` declares a readable alias for a hardware register, `r := k` loads a small constant, and `@label:` marks a branch target. Before the loop label `@loop`, a `place { ... }` block states the loop invariant: `name i = idx` binds the loop counter to a fresh symbolic variable `i`, `fact` gives the inequalities and specification equality that hold on entry and on every return to `@loop`, and `decreases n - i` proves termination (non-negative on entry, strictly smaller on each iteration).

= Checking, Packing, and Auditing

During development, run `ode check` on a `.ode` file to compile it, search for a proof, and verify the compiled bytes. When ready to ship, run `ode pack` to produce a standard ELF64 object file (`.o`) with the canonical contract embedded in `.ode.ocl`, plus a separate `.proof` file. An auditor runs `ode audit` on the `.o` and `.proof` files against the expected 52-character lowercase base-32 BLAKE3 contract identifier.

#codebox("Development, release, and audit commands", "python3 lang/ode_tool.py check paper/examples/all_zero.ode --target arm64\n\npython3 lang/ode_tool.py pack paper/examples/all_zero.ode --target arm64 \\\n  --out /tmp/all_zero.o --proof /tmp/all_zero.proof\n\npython3 lang/ode_tool.py audit /tmp/all_zero.o /tmp/all_zero.proof \\\n  --expect-contract jbqyjqpese4s4cq35qxlhaevjvzuaqznquqw6mtlaqleluc25ika", span: 6.80in)

The table below lists the four outcomes printed by Ode's tools and what each means.

#fullwidth[
  #set text(size: 8.6pt)
  #set par(justify: false, leading: 0.50em)
  #table(
    columns: (1.50in, 2.75in, 2.55in),
    inset: (x: 7pt, y: 5pt),
    stroke: (x: none, y: 0.4pt + rulecol),
    fill: (x, y) => if y == 0 { sand } else if calc.rem(y, 2) == 0 { ivory } else { white },
    [*Outcome*], [*Meaning*], [*Next action*],
    [`shown`], [The verifier checked every path of the compiled bytes against the contract.], [Ready to ship via `ode pack` alongside its `.proof` file.],
    [`refused with a proof`], [A concrete input shows the machine code disagrees with the contract.], [Fix the instructions or contract using the printed input.],
    [`no proof found`], [No counterexample was found, and the prover could not close a path.], [Strengthen `place` facts, bounds, or `trace depends on`.],
    [`run`], [An unverified test or benchmark run.], [Verify with `ode check` or `ode pack` before shipping.],
  )
]

#with_note([
  *Independent cross-check:* `proof-core/verify2.py` is a standalone Python verifier sharing no verification code with Lean; it checks the same `.statement` and order-independent `.proof` files as `odeverify`.
])[
  `ode audit` checks that 100% of executable bytes in `.text` belong to verified functions, that no external hooks are left unresolved, and that the embedded `.ode.ocl` contract hashes to the expected 52-character BLAKE3 identifier.
]

= Loop Invariants (`place`) and Multi-File Namespaces (`use`)

You supply every loop invariant in a `place { ... }` block immediately before the loop label. The table below lists each directive allowed inside `place { ... }` and what the verifier checks.

#fullwidth[
  #set text(size: 8.6pt)
  #set par(justify: false, leading: 0.50em)
  #table(
    columns: (1.80in, 5.00in),
    inset: (x: 7pt, y: 5pt),
    stroke: (x: none, y: 0.4pt + rulecol),
    fill: (x, y) => if y == 0 { sand } else if calc.rem(y, 2) == 0 { ivory } else { white },
    [*Directive*], [*What the verifier checks*],
    [`name x = reg`], [Binds a loop-varying register `reg` to a fresh symbolic variable `x` at the loop head.],
    [`fact E`], [An inequality (`0 <= i`, `i <= n`) or specification equality (`f(a) == g(a, i)`), proved on entry and on every loop back-edge.],
    [`decreases E`], [A whole-number measure proved `>= 0` on entry and strictly smaller on every loop back-edge (termination).],
    [`wrote buf[k ..] = E`], [For a buffer-writing loop, states that bytes `k .. len(buf)` already match `E` (use `wrote buf[.. k] = E` for count-up loops).],
    [`keep r1 r2`], [States that `r1`, `r2` retain their pre-loop values across every iteration.],
  )
]

To split a program across files (for example, keeping a pure specification separate from its implementations), import another `.ode` file under a local alias with `use alias = "path.ode"` and qualify its exports as `alias.name`. Imports are local to the file that writes them, and shared dependencies are deduplicated so splitting a program produces the exact same canonical contract and BLAKE3 identifier as a single file.

#codebox("proof-core/examples/hasher/hash_eq_ct_spec.ode", heq_spec, span: 6.80in)
#codebox("proof-core/examples/hasher/hash_eq_ct.ode — linked namespace and contract", heq_hdr, span: 6.80in)

In `eq_from`, `(a[i] + 256 - b[i]) % 256` is `0` when `a[i] == b[i]` and in `1..255` otherwise; adding `255` and dividing by `256` maps `0` to `0` and any non-zero difference to `1`, without branching on any byte.

= Side-Channel Contracts (`trace depends on`)

The *trace* of an execution is the sequence of instructions executed and memory addresses accessed — the observable channel behind timing and cache side-channel attacks. By default, Ode keeps every input out of the trace: branching on an input or using it in a memory address is refused unless the contract names it in `trace depends on`.

#block(width: 4.50in)[
  - `trace depends on nothing` — branches and addresses depend on no input at all (strictly constant-time).
  - `trace depends on n` — branches and addresses depend only on the length `n`, never on any byte in memory (as in `ct_bytes_eq` above).
  - `trace depends on a, n` — branches and addresses may depend on both the length and the bytes of `a` (as in `all_zero`).
]

#notebox("Specification Style for Fast Proofs", [
  Write scalar `def` functions in direct tail-recursive form, passing running accumulators as parameters and returning a sentinel value on invalid input. Avoid `let` bindings inside scalar `def` bodies; the prover closes each loop iteration in one unfolding.
])

= Custom Calling Conventions, Tail Calls, and Inline Helpers

Exported entry points follow the platform C ABI (`rdi, rsi, rdx, rcx, r8, r9` on x86-64; `x0..x7` on AArch64). Private helper functions may declare a `calling { in ...; out ...; preserves ... }` block choosing exact argument, return, and preserved registers. A leaf helper with `stack 0` can be tail-called with `jmp helper` (x86-64) or `b helper` (AArch64). Repeated short instruction sequences can be factored into an `inline fn` with `distinct(...)` and `changes ...` clauses so the compiler checks register aliasing before expanding.

#codebox("paper/examples/quad.ode — custom calling convention on x86-64", quad_hdr, span: 6.80in)

= Core Instruction Reference (x86-64 and AArch64)

Ode's compiler and verifiers read the same instruction tables (`core/x86.tab` and `arm64/arm64.tab`). The table below lists the core scalar and byte instructions side by side.

#fullwidth[
  #set text(size: 8.4pt)
  #set par(justify: false, leading: 0.48em)
  #table(
    columns: (1.45in, 2.65in, 2.70in),
    inset: (x: 6pt, y: 4.8pt),
    stroke: (x: none, y: 0.4pt + rulecol),
    fill: (x, y) => if y == 0 { sand } else if calc.rem(y, 2) == 0 { ivory } else { white },
    [*Operation*], [*x86-64 (`core/x86.tab`)*], [*AArch64 (`arm64/arm64.tab`)*],
    [Register move\ Constant load], [`mov r, s`\ `r := k`], [`mov r, s`\ `r := k` (`0..65535`)],
    [Add / subtract], [`add r, s`\ `sub r, s`], [`add d, a, b`\ `sub d, a, b`],
    [Shift / mask], [`shl r, k` / `shr r, k`\ `and r, k`], [`lsl d, a, k` / `lsr d, a, k`\ `and d, a, b`],
    [Byte load / store], [`movzx r32, byte ptr [a]`\ `mov byte ptr [a], r8`], [`ldrb w, [a, off]`\ `strb w, [a, off]`],
    [64-bit stack slot], [`mov r, qword ptr [rsp + off]`\ `push r` / `pop r`], [`ldr r, [sp, off]`\ `str r, [sp, off]`],
    [Compare], [`cmp a, b`], [`cmp a, b`],
    [Unsigned branches], [`je` / `jne` / `jb` / `jae`], [`b.eq` / `b.ne` / `b.lo` / `b.hs`],
    [Jump / call\ Tail call / return], [`jmp @L` / `call fn`\ `jmp fn` / `ret`], [`b @L` / `bl fn`\ `b fn` / `ret`],
    [Register aliases], [`reg base = rdi, idx = rcx`], [`reg base = x0, idx = x2, bw = w4`],
  )
]

#with_note([
  *Name note:* Informally, *Object-code Direct Evidence* — or *Only Declared Effects*, depending on whether you are auditing or coding.
])[
  Register aliases cannot shadow hardware register names (`v0..v31` are NEON vector registers on AArch64; `al, bl, cl, dl, ah, bh, ch, dh` are 8-bit registers on x86-64). On AArch64, load constants above 65,535 from two 16-bit halves (`mov r, hi; lsl r, r, 16; mov t, lo; add r, r, t`). Leaf functions with `stack 0` keep all state in caller-saved registers (`rax, rcx, rdx, rsi, rdi, r8..r11` on x86-64; `x0..x15` on AArch64).
]

= Checklist Before Packing

#block(width: 4.50in)[
  1. *Specification and contract:* Every `def` terminates; `requires` states every precondition (`no_overlap`, bounds); `trace depends on` names only inputs that branches and memory addresses may use.
  2. *Verify and pack:* `ode check` prints `shown` on each target; `ode pack` emits `.o` and `.proof` with matching 52-character BLAKE3 contract identifiers; `ode audit` confirms 100% coverage of `.text`.
]
