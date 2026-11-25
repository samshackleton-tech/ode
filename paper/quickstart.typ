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
#let heq_arm  = dedent4(heq_code.slice(heq_code.position("    for arm64 {")).trim(at: end).slice(0, -2).trim(at: end))

#let quad     = read("examples/quad.ode")
#let quad_step_x86 = quad.slice(quad.position("fn step("), quad.position("    for arm64 calling {")).trim(at: end) + "\n    // ... for arm64 calling { ... }\n}"
#let quad_call_x86 = quad.slice(quad.position("fn quad("), quad.position("    for arm64 stack 16 {")).trim(at: end) + "\n    // ... for arm64 stack 16 { ... }\n}"

// --- Page: calm asymmetric Tufte grid matching ODE.pdf ---
#set page(
  width: 8.5in,
  height: 11in,
  margin: (top: 0.72in, bottom: 0.70in, left: 0.85in, right: 3.15in),
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
        [A First Program]
      }
      block(width: 6.80in, below: 0pt)[
        #set text(font: "Palatino", size: 7.9pt, fill: slate, tracking: 0.06em)
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
        [#text(size: 7.6pt, fill: muted)[Object-code Direct Evidence · Companion to `paper/ODE.pdf`]],
        [#counter(page).display()],
      )
    ]
  },
)

#set text(font: "Palatino", size: 9.7pt, fill: ink, lang: "en")
#set par(justify: true, leading: 0.62em, spacing: 0.78em, first-line-indent: 0pt)
#set heading(numbering: "1.1")

#show heading.where(level: 1): it => {
  block(breakable: false, sticky: true, above: 1.05em, below: 0.50em, width: 6.80in)[
    #set par(justify: false)
    #if it.numbering != none [
      #text(fill: accent, size: 11.4pt, weight: "bold")[§ #counter(heading).display()]
      #h(0.45em)
    ]
    #text(fill: ink, size: 12.2pt, weight: "bold")[#it.body]
    #block(above: 4pt, below: 0pt, line(length: 100%, stroke: 0.55pt + rulecol))
  ]
}

#show raw.where(block: false): it => box(text(font: "Menlo", size: 0.89em, fill: charcoal)[#it.text])
#show raw.where(block: true): set text(font: "Menlo", size: 7.5pt, fill: ink)

#let fullwidth(body) = block(width: 6.80in, breakable: false, above: 0.50em, below: 0.50em)[#body]

#let with_note(note, above: 0.65em, body) = block(width: 6.80in, breakable: false, above: above, below: 0.65em)[
  #grid(
    columns: (4.50in, 0.35in, 1.95in),
    align: (top, top, top),
    [#body],
    [],
    [
      #set par(justify: false, leading: 0.52em, spacing: 0.38em)
      #set text(size: 8.0pt, fill: slate)
      #note
    ],
  )
]

#let codebox(title, body, span: 4.50in, size: 7.4pt) = block(
  width: span, breakable: false, above: 0.45em, below: 0.50em,
  fill: ivory, stroke: 0.5pt + rulecol, radius: 2.5pt, inset: (x: 8pt, y: 6pt),
)[
  #set par(justify: false, leading: 0.44em, spacing: 0pt)
  #if title != none [
    #text(font: "Palatino", size: 7.9pt, fill: slate, weight: "semibold")[#title]
    #block(above: 2.5pt, below: 4pt, line(length: 100%, stroke: 0.35pt + rulecol))
  ]
  #text(font: "Menlo", size: size, fill: ink)[#raw(block: true, body)]
]

// --- Title block ---
#block(width: 6.80in, above: 0pt, below: 0.95em)[
  #text(font: "Palatino", size: 8.2pt, fill: accent, weight: "bold", tracking: 0.14em)[ODE · PRACTITIONER'S QUICKSTART]
  #v(3pt)
  #text(font: "Palatino", size: 21pt, fill: ink, weight: "bold")[Writing Verified Machine Code in Ode]
  #v(3pt)
  #text(font: "Palatino", size: 10.4pt, fill: slate, style: "italic")[
    A hands-on guide to writing contracts and machine-code bodies that verify on x86-64 and AArch64.
  ]
  #v(8pt)
  #line(length: 100%, stroke: 0.9pt + charcoal)
]

#with_note([
  *Prover vs. verifier:* The prover searches for a `.proof` file and is relied on for nothing. The verifier checks the compiled machine bytes and `.proof` against the contract; if the prover errs, the verifier refuses the proof.
])[
  When you write performance-critical code in C or assembly, you rely on a compiler or manual review not to introduce an out-of-bounds read, a missed edge case, or a data-dependent branch. An Ode source file (`.ode`) pairs a short mathematical specification with the exact machine instructions you want to run. You keep full control over registers, branches, and stack layout; a separate verifier checks the compiled object bytes directly against the contract.
]

= A First Program

Consider a small function `all_zero` that tests whether every byte of an `n`-byte buffer is zero: on `[0, 0]` it returns `1`; on `[0, 7]` it returns `0`; on the empty buffer `[]` it returns `1`. A single file, `paper/examples/all_zero.ode`, states the specification (`def`), the contract (`fn`), and both target bodies (`for x86_64` and `for arm64`).

#codebox("paper/examples/all_zero.ode — specification and contract", az_contract, span: 6.80in)

#with_note([
  *Read-only by default:* This contract names no output buffer, so the body may read `a[0 .. n)` and may write no caller memory at all. Any write outside declared outputs and the local `stack N` workspace is refused.
])[
  Every `def` is a pure mathematical definition evaluated over exact integers; `fn` binds that specification to executable machine code. Here `a: n bytes` is a pointer to `n` readable bytes (`n` is a `number`, an unsigned 64-bit integer) and `returns zeros(a)` obliges the machine code to return the exact value of `zeros(a)`. The clause `trace depends on a, n` permits branches and memory addresses to depend on both the length `n` and the byte values of `a` (an early exit on the first nonzero byte is allowed; §4 explains constant-time contracts). `stack 0` promises that the function allocates zero local stack workspace beyond the caller's return mechanism.
]

#with_note([
  *Entry registers:* Exported functions follow System V AMD64 on x86-64 (`rdi, rsi, rdx, rcx, r8, r9`; return in `rax`) and AAPCS64 on AArch64 (`x0..x7`; return in `x0`).
])[
  Below are the two target bodies from the same file. Both scan from index `0` upward and exit on the first nonzero byte. The key loop fact is simple: whenever execution reaches `@loop`, every byte before `idx` has tested zero, so checking the remaining suffix from `idx` gives the same answer as checking all of `a`, and `n - idx` strictly decreases each turn. The `place { ... }` block writes that invariant directly above `@loop`; it is a proof annotation, never emitted as machine instructions.
]

#fullwidth[
  #grid(
    columns: (3.32in, 0.16in, 3.32in),
    codebox("for x86_64 (14 instructions, 50 B)", az_x86, span: 3.32in, size: 6.85pt),
    [],
    codebox("for arm64 (13 instructions, 52 B)", az_arm, span: 3.32in, size: 6.85pt),
  )
]

Inside each target block, `reg name = r` declares a readable alias for a hardware register; `cur` and `cur64` (`edx`/`rdx` on x86-64, `w4`/`x4` on AArch64) are the 32-bit and 64-bit views of one register so the byte load zero-extends into the 64-bit compare. `r := k` loads a small constant, and `@label:` marks a branch target.

= Checking, Packing, and Auditing

Run all commands below from the repository root (`python3 lang/ode_tool.py ...`, abbreviated `ode ...` in prose). During development, `ode check` compiles the source, runs the prover, and verifies the object bytes. For release, `ode pack` emits two files: a 64-bit ELF object file (`.o`) containing the canonical contract in a `.ode.ocl` section, plus a separate `.proof` file. An auditor runs `ode audit` on those two files against an expected 52-character BLAKE3 contract identifier obtained independently from the published specification or release record—never copied from the object file under audit.

#codebox("Development, release, and audit commands (run from repository root)", "python3 lang/ode_tool.py check paper/examples/all_zero.ode --target arm64\n\npython3 lang/ode_tool.py pack paper/examples/all_zero.ode --target arm64 \\\n  --out /tmp/all_zero.o --proof /tmp/all_zero.proof\n\npython3 lang/ode_tool.py audit /tmp/all_zero.o --proof /tmp/all_zero.proof \\\n  --expect-contract jbqyjqpese4s4cq35qxlhaevjvzuaqznquqw6mtlaqleluc25ika", span: 6.80in)

#with_note([
  *Independent cross-check:* An auditor who wants a second check outside the primary Lean verifier can run `python3 proof-core/verify2.py`, a standalone pure-Python verifier that checks the same proof files independently.
])[
  `ode audit` checks that 100% of executable bytes in `.text` belong to verified functions, that no external symbol relocations remain unresolved, that the `.ode.ocl` section hashes to the expected identifier, and that the verifier accepts the `.proof` file for those bytes.
]

#fullwidth[
  #block(below: 0.45em)[The four literal outcomes printed by Ode's tools are:]
  #set text(size: 8.6pt)
  #set par(justify: false, leading: 0.48em)
  #table(
    columns: (1.58in, 2.67in, 2.55in),
    inset: (x: 7pt, y: 5pt),
    stroke: (x: none, y: 0.4pt + rulecol),
    fill: (x, y) => if y == 0 { sand } else if calc.rem(y, 2) == 0 { ivory } else { white },
    [*Tool outcome*], [*Meaning*], [*Next action*],
    [#text(font: "Menlo", size: 8.1pt, weight: "bold", fill: ink)[shown]], [Verified: the verifier checked every path of the compiled bytes against the contract.], [Ship the `.o` object file together with its `.proof` file.],
    [#text(font: "Menlo", size: 8.1pt, weight: "bold", fill: accent)[refused with a proof]], [Counterexample: a concrete input demonstrates that the machine code violates the contract.], [Fix the code or contract using the printed failing input.],
    [#text(font: "Menlo", size: 8.1pt, weight: "bold", fill: charcoal)[no proof found]], [Inconclusive: no counterexample was found, and the prover could not close a proof obligation.], [Check bounds and `place` facts; fix unintended branches rather than relaxing `trace depends on`.],
    [#text(font: "Menlo", size: 8.1pt, weight: "bold", fill: slate)[run]], [Execution without a proof (concrete test or benchmark, not a verification verdict).], [Verify with `ode check` or `ode pack` before shipping.],
  )
]

= Loop Invariants

The verifier never guesses loop invariants: you state what holds at each loop head in a `place { ... }` block immediately before the loop label. Writing loop specifications in direct tail-recursive form (passing running accumulators as arguments) lets the prover close each iteration in a single step.

#fullwidth[
  #set text(size: 8.6pt)
  #set par(justify: false, leading: 0.48em)
  #table(
    columns: (1.92in, 4.88in),
    inset: (x: 7pt, y: 5pt),
    stroke: (x: none, y: 0.4pt + rulecol),
    fill: (x, y) => if y == 0 { sand } else if calc.rem(y, 2) == 0 { ivory } else { white },
    [*Directive in `place { ... }`*], [*Meaning or obligation*],
    [#text(font: "Menlo", size: 8.1pt, weight: "bold")[name x = reg]], [Binds loop-varying register `reg` to a fresh symbolic variable `x` at the loop head.],
    [#text(font: "Menlo", size: 8.1pt, weight: "bold")[fact E]], [States an inequality (`0 <= i`, `i <= n`) or specification equality proved on entry and on every back-edge.],
    [#text(font: "Menlo", size: 8.1pt, weight: "bold")[decreases E]], [States a whole-number measure proved `>= 0` on entry and strictly smaller on every back-edge (proves termination).],
    [#text(font: "Menlo", size: 8.1pt, weight: "bold")[wrote buf[.. k] = E]], [For count-up loops writing `buf`: promises bytes `[0, k)` already match `E`. For count-down loops, write `wrote buf[k ..] = E` for `[k, len(buf))`.],
    [#text(font: "Menlo", size: 8.1pt, weight: "bold")[keep r1 r2]], [Promises that registers `r1`, `r2` retain their pre-loop values across every iteration.],
  )
]

= Multi-File Namespaces and Trace Policies

Unlike `all_zero` (which may stop on the first nonzero byte), a cryptographic tag comparison must not disclose which byte differed first. In Ode, the *trace* of an execution is the sequence of instruction addresses executed and memory addresses accessed. Given fixed starting buffer addresses and lengths, two executions whose inputs agree on everything named in `trace depends on` are proved to follow the exact same instruction and address trace. (Physical effects outside the architectural trace—speculation, power draw, and data-dependent instruction latency—are not modeled.)

By default—when `trace depends on` is omitted, or written `trace depends on nothing`—no input value or buffer byte may influence any branch or memory address. Naming `trace depends on n` permits dependence on the length `n` only, while `trace depends on a, n` also permits dependence on the bytes of `a`.

To keep a pure specification separate from its implementations, import another `.ode` file under a local alias with `use alias = "file.ode"` and qualify its definitions as `alias.name`. Below is a complete constant-time byte-slice comparison split across two files, together with its verified AArch64 machine-code loop.

#codebox("proof-core/examples/hasher/hash_eq_ct_spec.ode — shared specification", heq_spec, span: 6.80in)

#fullwidth[
  #grid(
    columns: (3.00in, 0.16in, 3.64in),
    [
      #codebox("hash_eq_ct.ode — import and contract", heq_hdr, span: 3.00in, size: 6.6pt)
      #v(0.35em)
      #set par(justify: true, leading: 0.56em)
      #set text(size: 9.1pt)
      In the mathematical definition `eq_from`, `diff` stays `0` while all bytes match and becomes `1` once any pair differs: `(a[i] + 256 - b[i]) % 256` is `0` on equal bytes and `1..255` otherwise, and integer division `(diff + d + 255) / 256` maps `0` to `0` and any positive sum to `1`.

      The AArch64 machine code on the right implements that exact arithmetic with `add`, `sub`, `and`, and `lsr 8`—never branching on `a[i]` or `b[i]`—so the verifier approves `trace depends on n`.
    ],
    [],
    codebox("hash_eq_ct.ode — branchless arm64 body", heq_arm, span: 3.64in, size: 6.2pt),
  )
]

= Custom Calling Conventions and Tail Calls

Exported entry points follow the platform C calling convention (System V AMD64 on x86-64; AAPCS64 on AArch64). Between Ode functions inside one program, saving and restoring C-convention registers on every helper call wastes instructions. A private helper may therefore declare a `for <target> calling { ... }` block (one clause per line: `in param = reg, ...`, `out = reg`, and `preserves ...`). Below, `step` preserves `rdi`, `rsi`, and `r8`, so `quad` calls `step` twice with zero stack spills (`requires a < 1000000` prevents 64-bit wraparound).

#fullwidth[
  #grid(
    columns: (3.62in, 0.16in, 3.02in),
    codebox("paper/examples/quad.ode — helper with calling", quad_step_x86, span: 3.62in, size: 6.2pt),
    [],
    codebox("paper/examples/quad.ode — caller benefiting", quad_call_x86, span: 3.02in, size: 6.2pt),
  )
]

A leaf helper with `stack 0` can also be tail-called with `jmp helper` (x86-64) or `b helper` (AArch64) once the caller has restored its own stack frame and callee-saved registers. For repeated short straight-line sequences, `inline fn` with explicit register-disjointness (`distinct(...)`) and `changes` clauses expands without a call instruction (see `paper/ODE.pdf`, sections 4 and 5).

= Core Instruction Reference

#block(width: 6.80in, below: 0.35em)[
  Use this table to translate core scalar and byte operations between targets (both compiler and verifiers read `core/x86.tab` and `arm64/arm64.tab`). Operands: `d, a, b` are 64-bit general registers (`rax..r15` / `x0..x30`); `w` is a 32-bit AArch64 register (`w0..w30`); `r32` is a 32-bit x86-64 register (`eax..r15d`); `breg` is an 8-bit x86-64 byte register (`al, cl, dl, ...`); `k` is an immediate; `off` is a byte offset.
]

#fullwidth[
  #set text(size: 8.3pt)
  #set par(justify: false, leading: 0.42em)
  #table(
    columns: (1.52in, 2.64in, 2.64in),
    inset: (x: 6pt, y: 2.9pt),
    stroke: (x: none, y: 0.4pt + rulecol),
    fill: (x, y) => if y == 0 { sand } else if calc.rem(y, 2) == 0 { ivory } else { white },
    [*Operation*], [*x86-64*], [*AArch64*],
    [Register move], [`mov d, a`], [`mov d, a`],
    [Constant load (shorthand)], [`d := k`], [`d := k` (`0..65535`)],
    [Add / subtract], [`add d, a` / `sub d, a`], [`add d, a, b` / `sub d, a, b`],
    [Shift / mask], [`shl d, k` / `shr d, k` / `and d, k`], [`lsl d, a, k` / `lsr d, a, k` / `and d, a, b`],
    [Byte load / store], [`movzx r32, byte ptr [a]`\ `mov byte ptr [a], breg`], [`ldrb w, [a, off]`\ `strb w, [a, off]`],
    [64-bit stack slot], [`mov d, qword ptr [rsp + off]`\ `mov qword ptr [rsp + off], a`], [`ldr d, [sp, off]`\ `str a, [sp, off]`],
    [Stack push / pop], [`push a` / `pop d`], [`sub sp, sp, 16` / `add sp, sp, 16`],
    [Compare], [`cmp a, b`], [`cmp a, b`],
    [Equality branches], [`je @L` / `jne @L`], [`b.eq @L` / `b.ne @L`],
    [Unsigned order branches], [`jb` / `jbe` / `ja` / `jae`], [`b.lo` / `b.ls` / `b.hi` / `b.hs`],
    [Jump / call], [`jmp @L` / `call fn`], [`b @L` / `bl fn`],
    [Tail call / return], [`jmp fn` / `ret`], [`b fn` / `ret`],
  )
]

#block(width: 6.80in, above: 0.45em)[
  *Target notes:* Register aliases (`reg idx = rcx`) cannot shadow hardware register names (such as `v0..v31` on AArch64 or `al..dl` on x86-64). On AArch64, constants from `65,536` up to `2^32 - 1` are built from two 16-bit halves (`d := hi; lsl d, d, 16; t := lo; add d, d, t`). Leaf functions (those making no calls) with `stack 0` keep all state in caller-saved registers (`rax, rcx, rdx, rsi, rdi, r8..r11` on x86-64; `x0..x15` on AArch64).
]

= Release and Audit Checklist

#block(width: 6.80in)[
  1. *Contract:* Every `def` terminates; `requires` states every buffer bound and non-overlap precondition (`no_overlap`); `trace depends on` names only inputs that branches and memory addresses are permitted to use.
  2. *Verify and pack:* `ode check` prints `shown` for every target; `ode pack` produces the `.o` object file and separate `.proof` file.
  3. *Independent audit:* `ode audit FILE.o --proof FILE.proof --expect-contract EXPECTED_ID` prints `shown` with 100% coverage of `.text`, where `EXPECTED_ID` comes from the independently audited specification—not from the object file itself.
]
