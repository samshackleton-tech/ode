// The Ode Quickstart.
// Companion to the Ode Language Report (paper/ODE.pdf) and paper/HIGH-LEVEL-ODE-SPEC.md.
// Every code listing is read directly from a tested, dual-verified `.ode` file in this repository.
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

#let az_hl    = read("examples/all_zero_hl.ode").trim(at: end)
#let ct_spec_raw = read("EXPERIMENTS/tasks/ct_count_spec.ode").trim(at: end)
#let ct_spec  = ct_spec_raw.slice(ct_spec_raw.position("def count_from")).trim(at: end)
#let ct_ref   = read("EXPERIMENTS/tasks/ct_count_reference.ode").trim(at: end)
#let b3_one   = read("EXPERIMENTS/tasks/blake3_compress1_reference.ode")
#let b3_ghalf = b3_one.slice(b3_one.position("inline fn g_half"), b3_one.position("\ninline fn perm_x86")).trim(at: end)
#let cc_ref   = read("EXPERIMENTS/tasks/chacha20_4way_reference.ode")
#let cc_qr16  = cc_ref.slice(cc_ref.position("inline fn qr16"), cc_ref.position("\n// Self-inverse 4x4")).trim(at: end)

// --- Page: calm asymmetric Tufte grid matching ODE.pdf ---
#set page(
  width: 8.5in,
  height: 11in,
  margin: (top: 0.70in, bottom: 0.68in, left: 0.85in, right: 3.15in),
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

#set text(font: "Palatino", size: 9.6pt, fill: ink, lang: "en")
#set par(justify: true, leading: 0.59em, spacing: 0.72em, first-line-indent: 0pt)
#set heading(numbering: "1.1")

#show heading.where(level: 1): it => {
  block(breakable: false, sticky: true, above: 0.85em, below: 0.44em, width: 6.80in)[
    #set par(justify: false)
    #if it.numbering != none [
      #text(fill: accent, size: 11.2pt, weight: "bold")[§ #counter(heading).display()]
      #h(0.45em)
    ]
    #text(fill: ink, size: 12.0pt, weight: "bold")[#it.body]
    #block(above: 4pt, below: 0pt, line(length: 100%, stroke: 0.55pt + rulecol))
  ]
}

#show raw.where(block: false): it => box(text(font: "Menlo", size: 0.88em, fill: charcoal)[#it.text])
#show raw.where(block: true): set text(font: "Menlo", fill: ink)

#let fullwidth(body) = block(width: 6.80in, breakable: false, above: 0.44em, below: 0.44em)[#body]

#let with_note(note, above: 0.56em, body) = block(width: 6.80in, breakable: false, above: above, below: 0.56em)[
  #grid(
    columns: (4.50in, 0.35in, 1.95in),
    align: (top, top, top),
    [#body],
    [],
    [
      #set par(justify: false, leading: 0.50em, spacing: 0.36em)
      #set text(size: 7.9pt, fill: slate)
      #note
    ],
  )
]

#let codebox(title, body, span: 4.50in, size: 7.25pt) = block(
  width: span, breakable: false, above: 0.38em, below: 0.44em,
  fill: ivory, stroke: 0.5pt + rulecol, radius: 2.5pt, inset: (x: 8pt, y: 5.5pt),
)[
  #set par(justify: false, leading: 0.42em, spacing: 0pt)
  #if title != none [
    #text(font: "Palatino", size: 7.8pt, fill: slate, weight: "semibold")[#title]
    #block(above: 2.5pt, below: 3.5pt, line(length: 100%, stroke: 0.35pt + rulecol))
  ]
  #text(font: "Menlo", size: size, fill: ink)[#raw(block: true, body)]
]

// --- Page 1: Title + Motivation + §1 A First Program ---
#block(width: 6.80in, above: 0pt, below: 0.85em)[
  #text(font: "Palatino", size: 8.2pt, fill: accent, weight: "bold", tracking: 0.14em)[ODE · PRACTITIONER'S QUICKSTART]
  #v(3pt)
  #text(font: "Palatino", size: 20.5pt, fill: ink, weight: "bold")[Writing Verified Machine Code in Ode]
  #v(3pt)
  #text(font: "Palatino", size: 10.2pt, fill: slate, style: "italic")[
    A hands-on guide to structured Ode contracts, deterministic lowering, dual verification, and static performance analysis on x86-64 and AArch64.
  ]
  #v(7pt)
  #line(length: 100%, stroke: 0.9pt + charcoal)
]

#with_note([
  *Prover vs. verifier:* The prover searches for a `.proof` file and is relied on for nothing. Separate verifiers check the compiled ELF object bytes and `.proof` directly against the contract; if the compiler or prover errs, every verifier refuses the proof.
])[
  When you write performance-critical code in C or assembly, you rely on an optimizing compiler or manual review not to introduce an out-of-bounds read, integer wraparound, missed edge case, or data-dependent branch. An Ode source file (`.ode`) pairs a short mathematical specification (`def`) with structured systems code (`fn`) that lowers 1-to-1 in written statement order to exact machine instructions—with zero hidden spills or silent instruction reordering.
]

= A First Program

Consider a function `all_zero` that tests whether every byte of an `n`-byte buffer is zero: on `[0, 0]` it returns `1`; on `[0, 7]` it returns `0`; on the empty buffer `[]` it returns `1`. One portable file, `paper/examples/all_zero_hl.ode`, states the mathematical specification (`def`), the contract (`fn`), and a single structured body that compiles and verifies for both `x86_64` (13 instructions, 48 B) and `arm64` (13 instructions, 52 B).

#codebox("paper/examples/all_zero_hl.ode — portable specification, contract, and body", az_hl, span: 6.80in)

#with_note([
  *Read-only by default:* This contract names no `ensures` output buffer, so the machine code may read `a[0 .. n)` and may write no caller memory at all. Any write outside declared outputs and the local `stack N` workspace is refused.
])[
  Every `def` is a pure mathematical definition evaluated over exact integers; `fn` binds that specification to native machine code. Here `a: n bytes` grants read-only access to `n` bytes (`n` is a `number`, an unsigned 64-bit integer; `u64` is a synonym, and `u8` adds `0 <= x <= 255`). The clause `returns zeros(a)` obliges the compiled instructions to return `zeros(a)` on every input, `trace depends on a, n` permits early exit on the first nonzero byte (§4 explains constant-time contracts), and `stack 0` promises zero stack workspace beyond the caller's return slot.
]

Inside the body, `for i in 0..n` automatically tracks `0 <= i <= n` and `decreases n - i`, so you state only the single semantic invariant `maintains zeros(a) == zero_from(a, i)`. The loop compiles cleanly with zero stack spills on both processors and yields the exact same 52-character canonical contract identifier on x86-64 and AArch64.

// --- Page 2: §2 Checking, Packing, and Dual Auditing + Outcomes ---
#pagebreak()

= Checking, Packing, and Dual Auditing

Run all commands from the repository root (`python3 lang/ode_tool.py ...`, abbreviated `ode ...`). During development, `ode check` compiles, proves, and verifies one target, while `ode advise --asm` prints the exact variable-to-register map, lowered instructions, and static cycle estimate in under 50 ms. For release, `ode pack` emits an ELF64 object file (`.o`, carrying the canonical contract in `.ode.ocl`) together with a separate `.proof` file.

#codebox("Development, release, and dual-verifier audit commands (run from repository root)", "python3 lang/ode_tool.py check paper/examples/all_zero_hl.ode --target arm64\npython3 lang/ode_tool.py advise --asm paper/examples/all_zero_hl.ode --target arm64 --all-archs\n\npython3 lang/ode_tool.py pack paper/examples/all_zero_hl.ode --c-abi --target arm64 \\\n  --verifier both --out /tmp/all_zero.o --proof /tmp/all_zero.proof\n\npython3 lang/ode_tool.py audit /tmp/all_zero.o --proof /tmp/all_zero.proof --verifier both \\\n  --expect-contract jbqyjqpese4s4cq35qxlhaevjvzuaqznquqw6mtlaqleluc25ika", span: 6.80in)

#with_note([
  *Independent contract ID:* Obtain `--expect-contract` from the reviewed specification or release record—never from the object file under audit. Every exported symbol is named `ode_<52-char-id>`, so a contract mismatch fails at link time as well as audit time.
])[
  Passing `--verifier both` requires agreement from both independent verifiers: Lean 4 `odeverify` (proved sound in Lean 4) and standalone pure-Python `proof-core/verify2.py` (which shares zero verification code with Lean or the prover). Auditors without Lean installed can pass `--verifier verify2` to verify the exact same `.o` and order-independent (`r ...`) `.proof` files with pure Python alone.
]

#codebox("Live output of ode audit --verifier both on paper/examples/all_zero_hl.ode (arm64)", "BINARY:   /tmp/all_zero.o\n  BLAKE3(binary):    b5arocbrn77fgcizqhg24zj3w74b4f42kjt44nmhvwfe6c4ryi7a\n  BLAKE3(contract):  jbqyjqpese4s4cq35qxlhaevjvzuaqznquqw6mtlaqleluc25ika  (embedded .ode.ocl)\n  SYMBOL:            ode_jbqyjqpese4s4cq35qxlhaevjvzuaqznquqw6mtlaqleluc25ika\n  COVERAGE:          100% of executable code (1 function, 13 instructions, 52 B, 1 exported symbol, 0 hooks)\n  VERIFIERS:         odeverify (shown), verify2 (shown)\n  VERDICT:           shown", span: 6.80in, size: 6.30pt)

#fullwidth[
  #block(below: 0.36em)[The table below defines the four literal verdicts printed by Ode's tools and the action each verdict calls for.]
  #set text(size: 8.5pt)
  #set par(justify: false, leading: 0.46em)
  #table(
    columns: (1.58in, 2.67in, 2.55in),
    inset: (x: 7pt, y: 4.6pt),
    stroke: (x: none, y: 0.4pt + rulecol),
    fill: (x, y) => if y == 0 { sand } else if calc.rem(y, 2) == 0 { ivory } else { white },
    [*Tool outcome*], [*Meaning*], [*Next action*],
    [#text(font: "Menlo", size: 8.0pt, weight: "bold", fill: ink)[shown]], [Verified: the verifier checked every path of the compiled machine bytes against the contract.], [Ship the `.o` object file together with its `.proof` file.],
    [#text(font: "Menlo", size: 8.0pt, weight: "bold", fill: accent)[refused with a proof]], [Counterexample: a concrete input demonstrates that the machine code violates the contract.], [Fix the code or contract using the printed failing input.],
    [#text(font: "Menlo", size: 8.0pt, weight: "bold", fill: charcoal)[no proof found]], [Inconclusive: no counterexample was found, and the prover could not close an obligation.], [Strengthen `maintains`/`writes`/`join` facts; fix unintended branches rather than relaxing `trace depends on`.],
    [#text(font: "Menlo", size: 8.0pt, weight: "bold", fill: slate)[run]], [Execution without a proof (concrete test or benchmark, never a verification verdict).], [Verify with `ode check` or `ode pack` before shipping.],
  )
]

// --- Page 3: §3 Structured Language and Memory Model ---
#pagebreak()

= Structured Language and Memory Model

High-Level Ode lowers statements deterministically in written order with lexical block scoping and explicit register/stack control. Memory contracts separate region roles and cache-line/page geometry (`aligned`, `line_disjoint`, read-only vs. in-out vs. write-only) from scalar and vector transfer widths (`1`, `2`, `4`, `8`, `16`, or `64` bytes).

#fullwidth[
  #block(below: 0.36em)[The table below summarizes each core High-Level Ode construct, its concrete syntax, and its deterministic lowering and proof rule.]
  #set text(size: 8.2pt)
  #set par(justify: false, leading: 0.43em)
  #table(
    columns: (1.35in, 2.25in, 3.20in),
    inset: (x: 5.5pt, y: 4.0pt),
    stroke: (x: none, y: 0.4pt + rulecol),
    fill: (x, y) => if y == 0 { sand } else if calc.rem(y, 2) == 0 { ivory } else { white },
    [*Construct*], [*Syntax*], [*Deterministic lowering & proof semantics*],
    [Scalar variables], [`let x := e`, `var i: u64 := 0`, `var b: u8 := 0`, `{ ... }`], [Allocates one register (`u8` adds `0 <= b <= 255`); lexical `{ ... }` blocks and dead parameters release registers immediately.],
    [Explicit stack slots], [`stack var x: u64 := 0`, `buf tmp[64] align 64`], [Explicit aligned frame slots—never hidden compiler spills. Leaf frames with `align >= 16` or `u32x16` keep `rsp` 16-byte aligned.],
    [Exact arithmetic], [`a + b`, `a - b`, `a * b`, `x += k`, `x -= k`], [Default arithmetic; the verifier proves absence of 64-bit unsigned overflow or underflow.],
    [Wrapping mod $2^64$], [`a +% b`, `a -% b`, `a *% b`, `x +%= k`], [Explicit hardware wraparound (`wrap` proof tag); enables single-compare range tests such as `(c -% 65) <= 25`.],
    [Bitwise & shifts], [`a & b`, `a | b`, `a ^ b`, `a << k`, `a >> k`], [Exact bitmasks (`& (2^w - 1)`), contiguous bitfields, and constant power-of-two shifts.],
    [Branchless select], [`select(cond, a, b)`], [Lowers directly to `cmov*` (`x86_64`) / `csel` (`arm64`); safe on values kept out of the trace.],
    [Scalar memory], [`a[i]`, `a.u16(i)`, `a.u32(i)`, `a.u64(i)`, `out[i] := v`, `out.u64(i) := v`], [1/2/4/8-byte little-endian loads uniformly across read-only, in-out (before and after partial writes), and stack slots; pure write-only `out` stays unreadable before write.],
    [Cache-line & page contracts], [`requires aligned(buf, 64)`, `requires aligned(pg, 4096)`, `requires line_disjoint(a, b, 64)`], [`aligned(buf, A)` (`A` in `8..16384`) proves `buf & (A-1) == 0`; `line_disjoint` prevents false sharing across 64 B or 128 B cache lines and propagates across aligned arena sub-slices.],
    [Counted loop], [`for i in lo..hi [step k] [maintains ...] [writes ...] { ... }`], [Auto-tracks `lo <= i <= hi`, step alignment, `decreases hi - i`, and invariant outer `if`-guards and `let` equalities.],
    [Compile-time unroll], [`for i in 0..N [step k] unroll { ... }`], [Expands straight-line at compile time with constant folding on `i` and zero loop overhead.],
    [General loop & join], [`while cond [maintains ...] decreases E`, `join maintains f1, f2`], [`while` proves termination via `decreases E`; `join` merges sequential `if/else` diamonds linearly (`2k` instead of `2^k` paths).],
    [Calls & tail calls], [`let r := f(a, b)`, `return f(a, b)`], [Ode-to-Ode calls auto-derive exact `preserves` sets with zero C-ABI boilerplate; `return f(...)` lowers to a verified tail jump (`jmp`/`b`).],
  )
]

#with_note([
  *Output-buffer loops:* Write `writes out[.. j] = spec_expr[i]` for count-up loops (bytes `[0, j)` already match) or `writes out[j ..] = spec_expr[i]` for count-down loops.
])[
  When a loop maintains a specification invariant, write the specification `def` in direct tail-recursive form passing running accumulators as arguments (as in `count_from` on the next page). That lets the prover close each iteration in a single unfolding step.
]

// --- Page 4: §4 Multi-File Namespaces & Trace + §5 Helpers & Recursion ---
#pagebreak()

= Multi-File Namespaces (`use`) and Trace Policies

Unlike `all_zero` (which exits early on the first nonzero byte), cryptographic routines must keep key and message bytes out of control flow and memory addresses. In Ode, the *trace* of an execution is the sequence of instruction addresses executed and memory addresses accessed. Given fixed buffer addresses and lengths, `Ode.verify_all_trace` proves that any two runs agreeing on `trace depends on` follow the exact same trace. (Speculation, power draw, and variable arithmetic latency lie outside the architectural model.)

#with_note([
  *Default is constant-time:* Omitting `trace depends on` (or writing `trace depends on nothing`) keeps every argument and buffer byte out of the trace. Naming `trace depends on n` permits dependence on `n` only.
], above: 0.42em)[
  Every `.ode` file is a closed local namespace. Import a shared specification under a local alias by its 52-character BLAKE3-256 digest (`use cd = "<digest>"`, computed via `ode hash file.ode`) and qualify its names as `cd.name`. Below is a constant-time differing-byte counter split across two tested, dual-verified files:
]

#codebox("paper/EXPERIMENTS/tasks/ct_count_spec.ode — pure specification", ct_spec, span: 6.80in, size: 6.95pt)

#codebox("paper/EXPERIMENTS/tasks/ct_count_reference.ode — portable branchless implementation", ct_ref, span: 6.80in, size: 6.95pt)

Because `(a[i] + 256 - b[i]) & 255` and `(diff + 255) >> 8` never branch on `a[i]` or `b[i]` (and `select(cond, a, b)` lowers directly to `cmov*`/`csel` when a conditional choice is needed), both verifiers approve `trace depends on n` on both `x86_64` and `arm64`.

= Helper Functions, Calling Conventions, and Recursion

#fullwidth[
  #grid(
    columns: (3.34in, 0.16in, 3.30in),
    align: (top, top, top),
    [
      #set par(justify: true, leading: 0.56em, spacing: 0.58em)
      Exported entry points packed with `--c-abi` follow System V AMD64 (`rdi..r9`, return `rax`) on x86-64 and AAPCS64 (`x0..x7`, return `x0`) on AArch64. Between Ode functions inside one program (or across `use`-imported files, callees before callers), the compiler automatically derives each helper's exact `preserves` set so caller registers survive calls without stack spills; on private non-recursive helpers you may omit `stack N`.

      A directly recursive function declares a `decreases arg` clause (for a parameter in `trace depends on`) and a linear stack budget `stack C + D * arg` or a logarithmic budget `stack C + D * bits(arg / K)` (used by BLAKE3's recursive Merkle subtree hasher).
    ],
    [],
    codebox("Direct self-recursion with linear stack bound", "fn rec_all_zero(a: n bytes, n: u64, d: u64)\n    requires d <= n, n <= 65536\n    returns zero_prefix(a, d)\n    decreases d\n    trace depends on a, n, d\n    stack 32 + 32 * d\n{\n    if d == 0 { return 1 }\n    if a[d - 1] != 0 { return 0 }\n    return rec_all_zero(a, n, d - 1)\n}", span: 3.30in, size: 6.5pt),
  )
]

// --- Page 5: §6 Typed SIMD, inline fn, and std/ ---
#pagebreak()

= Typed SIMD (`u32x4`, `u32x16`), `inline fn`, and `std/`

Portable functions use a single `{ ... }` body. When a cryptographic or media kernel benefits from explicit vector widths or CPU feature gates (`needs avx`, `needs avx512`), write target blocks `for x86_64 [needs ...] { ... }` and `for arm64 { ... }` using typed `u32x4` (128-bit SSE/AVX/NEON) and `u32x16` (512-bit AVX-512) variables.

To factor repeated straight-line sequences (round functions, transposes, target-specialized rotates) with zero call overhead and without losing surrounding path facts, write a hygienic `inline fn` with by-value, `var` (pass-by-alias), or compile-time `const` parameters. Ordinary, auditable helper modules live in `std/` with zero special compiler privilege; import them by content hash (`use vec = "..."`) with `--store std`.

#fullwidth[
  #grid(
    columns: (3.34in, 0.12in, 3.34in),
    codebox("BLAKE3 half-G using std/vec.ode (u32x4)", b3_ghalf, span: 3.34in, size: 6.65pt),
    [],
    codebox("ChaCha20 4-way AVX-512 quarter-round (u32x16)", cc_qr16, span: 3.34in, size: 6.65pt),
  )
]

#fullwidth[
  #block(below: 0.35em)[The table below maps each typed SIMD expression to its 1-to-1 machine instruction lowering on x86-64 and AArch64.]
  #set text(size: 8.1pt)
  #set par(justify: false, leading: 0.42em)
  #table(
    columns: (1.36in, 2.52in, 2.92in),
    inset: (x: 5.5pt, y: 3.6pt),
    stroke: (x: none, y: 0.4pt + rulecol),
    fill: (x, y) => if y == 0 { sand } else if calc.rem(y, 2) == 0 { ivory } else { white },
    [*SIMD operation*], [*High-Level Ode syntax*], [*1-to-1 lowering (`x86_64` / `arm64`)*],
    [Vector load / store], [`inp.u32x4(off)`, `out.u32x4(off) := v`, `inp.u32x16(off)`, `out.u32x16(off) := v`], [`vmovdqu` / `vmovdqu32` (`x86_64`); `ldr qN` / `str qN` (`arm64`).],
    [Scalar & broadcast], [`u64_to_vec(x)`, `const_u32x4(lbl)`, `broadcast_u32x16(w)`], [`vmovq` / `fmov dN, r`; `vmovaps [rip + #lbl]`; `vpbroadcastd`.],
    [Lane ALU (32-bit)], [`a +% b`, `a ^ b`, `a & b`, `a | b`], [`vpaddd`, `vpxord`, `vpand`, `vpor` / `add.4s`, `eor.16b`, `and.16b`, `orr.16b`.],
    [Shift & 1-insn rotate], [`a >> k`, `a << k`, `vprord(a, k)`, `rev32_16(a)`], [`vpsrld`/`vpslld`, `vprord` (`avx512`); `ushr.4s`/`shl.4s`, `rev32.8h` (`arm64`).],
    [Byte rotate / align], [`ext4(a, b)`, `ext8(a, b)`, `ext12(a, b)`], [`vpalignr` (`x86_64`) / `ext.16b` (`arm64`).],
    [Lane shuffle & unpack], [`unpacklo32/hi32`, `unpacklo64/hi64`, `uzp1_32/uzp2_32`, `shuf32`, `shufps`, `blend32`, `shufi32x4`], [`vpunpck*`, `vshufps`, `vpshufd`, `vpblendd`, `vshufi32x4` / `zip1/2`, `uzp1/2` (`arm64`).],
  )
]

#fullwidth[
  #block(below: 0.35em)[The table below lists the ordinary `std/` helper modules checked into this repository and their exact 52-character BLAKE3-256 import digests.]
  #set text(size: 8.0pt)
  #set par(justify: false, leading: 0.43em)
  #table(
    columns: (1.02in, 2.52in, 3.26in),
    inset: (x: 5pt, y: 3.8pt),
    stroke: (x: none, y: 0.4pt + rulecol),
    fill: (x, y) => if y == 0 { sand } else if calc.rem(y, 2) == 0 { ivory } else { white },
    [*Module*], [*BLAKE3-256 digest (`ode hash`)*], [*Exported helpers*],
    [`std/vec.ode`], [#text(font: "Menlo", size: 6.55pt)[`7zpczpzr6tshzr6ew4fnhluakp3vs4q3xu4pndhflmztv6rdpqra`]], [`rotr32`, `rotl32`, `rotr32_x16`, `rotl32_x16`, `pack_u64x2`, `const_u32x4`, `rot_lanes`, `transpose_4x4`.],
    [`std/bytes.ode`], [#text(font: "Menlo", size: 6.55pt)[`ozgki74ogmdvuzubstiqnse5xlh2guawnta5dmhrmaqokwp3dfqa`]], [`load_u16_le`, `load_u16_be`, `store_u16_le`, `store_u16_be`.],
    [`std/int.ode`], [#text(font: "Menlo", size: 6.55pt)[`raeybpdavam7upiziaktzghulvfgv6er54pcn6xjgiq7uuoc6kvq`]], [`mul_const`, `min_u64`, `max_u64`, `clamp_u64`, plus spec defs `min2`, `max2`, `clamp`.],
  )
]

#with_note([
  *Zero hidden spills:* On `arm64`, `u32x4` uses up to 22 caller-saved NEON registers (`v0..v7, v16..v29`); on `x86_64`, `u32x16` uses `zmm1..zmm30` and emits `vzeroupper` automatically on exit.
])[
  When an `inline fn` is called multiple times inside a loop and contains several `select`s or branches, attach a `returns <spec_expr>` clause (which inserts an automatic `join` after each expansion) or make it a separate `fn` so symbolic verification stays linear.
]

// --- Page 6: §7 Static Performance & Locality + §8 Release Checklist ---
#pagebreak()

= Static Performance and Locality Analysis

Without executing the binary, `ode advise --asm --all-archs` prints the variable-to-register map, the exact lowered instructions alongside each source line, and a calibrated out-of-order pipeline simulation over every loop and straight-line function. It reports cycles per iteration, cycles per byte (`cyc/B`), the active bottleneck (`frontend`, `dependency`, or execution ports), critical-path chains, instruction-cache footprint, per-loop `locality` (active memory streams, stride class, bytes/lines per iteration), function `memory_footprint` in cache lines and VM pages, and microarchitectural hazard warnings (`stlf-width`, `line-split`, `stream-count`, and `stride-4k-alias`).

#codebox("Live output of ode advise on paper/examples/all_zero_hl.ode (no execution; runs in < 50 ms)", "python3 lang/ode_tool.py advise paper/examples/all_zero_hl.ode --target x86_64 --all-archs\n\n# code:   13 instructions, 48 bytes, 1 i-cache line(s) (64 B/line)\n# loop 0: +0x7..+0x28 — 10 ins, 33 B, 1 i-cache line | ~2.00 cyc/iter (dependency, 2 fused)\n#   locality: 1 stream(s) (1R/0W/0RW), 1 B read + 0 B write, ~1 line/iter [rdi(read,unit,+1B)]\n#   crit path (10.0 cyc, 4 ops): L26(lea_idx) -> L27(movzx8_rm) -> L28(cmp64_ri) -> L29(je)\n#   cross-CPU static estimate (no execution):\n#     zen5    : ~ 2.00 cyc/iter, 2.00 cyc/B [dependency  ] (2 fused, 0 elim)\n#     zen4    : ~ 2.00 cyc/iter, 2.00 cyc/B [frontend    ] (2 fused, 0 elim)\n#     zen3    : ~ 2.00 cyc/iter, 2.00 cyc/B [frontend    ] (2 fused, 0 elim)\n#     icelake : ~ 4.00 cyc/iter, 4.00 cyc/B [frontend    ] (2 fused, 0 elim)", span: 6.80in, size: 6.85pt)

#with_note([
  *Compile-time budgets:* Declare `budget { max_bytes N; max_icache_lines N; max_loop_cycles C }` inside a target block so regressions fail during compilation.
])[
  Use `--arch NAME` to focus on one microarchitecture (`zen5`, `zen4`, `zen3`, `icelake`, `apple_m`, `ampere1`). The highest-payoff optimizations appear directly in `ode advise --asm`:
  - *Eliminate spills:* inspect `variables:` and shorten live ranges or use `for ... unroll` so hot state stays in caller-saved registers (`stack 0 B`, zero spills).
  - *Avoid cache and forwarding hazards:* watch for `stlf-width` (narrow stack write overlapping a wider stack read), `line-split`, `stream-count`, and `stride-4k-alias`; declare `requires aligned(buf, 64)` and `requires line_disjoint(a, b, 64)` on partitioned buffers.
  - *Interleave independent chains:* process 2–4 lanes or blocks side by side (as in 4-way NEON or 512-bit AVX-512 ChaCha20 and BLAKE3) to hide ALU/vector latency and fill execution ports.
  - *Keep hot loops branchless:* replace data-dependent branches with `select(cond, a, b)` and single-compare wrapping checks `(c -% lo) <= hi - lo`.
]

= Release and Dual-Audit Checklist

#block(width: 6.80in)[
  #set par(justify: false, leading: 0.56em, spacing: 0.55em)
  1. *Review the contract:* Every `def` terminates; `requires` states every buffer bound, `no_overlap`, and `aligned`/`line_disjoint` precondition; `trace depends on` names only inputs permitted to influence branches and memory addresses.
  2. *Verify and pack with both verifiers:* Run `ode pack FILE.ode --c-abi --target TARGET --verifier both --out FILE.o --proof FILE.proof` and confirm `VERIFIERS: odeverify (shown), verify2 (shown)` and `VERDICT: shown`.
  3. *Audit independently from the binary:* Run `ode audit FILE.o --proof FILE.proof --verifier both --expect-contract EXPECTED_ID`, where `EXPECTED_ID` comes from the independently reviewed specification rather than the binary under audit.
  4. *Zero-Lean option:* Any auditor without Lean installed can verify the exact same `.o` and order-independent (`r ...`) `.proof` file using `--verifier verify2` alone.
]

#block(width: 6.80in, above: 0.85em)[
  #line(length: 100%, stroke: 0.45pt + rulecol)
  #v(5pt)
  #set par(justify: false, leading: 0.52em)
  #set text(size: 8.6pt, fill: slate)
  *Further reading:* `paper/ODE.pdf` (complete Ode Language Report and formal semantics), `paper/HIGH-LEVEL-ODE-SPEC.md` (complete High-Level Ode reference), `docs/ODE-FOR-AUDITORS.md` (security auditor's pocket guide and reliance-set inventory), and `CATALOG.md` (verified x86-64 and AArch64 library catalog).
]
