#!/usr/bin/env pypy3
"""Generate the six co-designed vector figures for the Ode Language Report.

Visual vocabulary (shared with paper/ode.typ):
  - Serif: Palatino (prose, headings, figure labels)
  - Mono:  Menlo (code, symbols, registers, hashes)
  - Palette:
      ink      #1C1E21  warm charcoal (primary text & strokes)
      slate    #5B6470  quiet slate (hairlines, annotations, secondary curves)
      rule     #C8C3B8  warm hairline rule
      accent   #9E2A2B  Venetian terracotta (Bob's boundary, contract hashes, verified Ode)
      ivory    #F7F5F0  soft paper tint (workshop / neutral code ground)
      blush    #FBF2F1  ultra-soft blush (Bob's reliance set / verified highlight)
      white    #FFFFFF  clean card ground
"""
from pathlib import Path

OUT = Path(__file__).resolve().parent / "figures"
OUT.mkdir(parents=True, exist_ok=True)

INK = "#1C1E21"
SLATE = "#5B6470"
MUTED = "#7D8590"
RULE = "#CFC9BC"
ACCENT = "#9E2A2B"
IVORY = "#F7F5F0"
BLUSH = "#FBF2F1"
SAGE_BG = "#F2F5F2"
SAGE = "#3D6150"
WHITE = "#FFFFFF"

SERIF = "Palatino"
MONO = "Menlo"


def esc(s):
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def svg_wrap(w, h, body):
    return (
        f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {w} {h}" width="{w}" height="{h}">\n'
        f'  <defs>\n'
        f'    <marker id="arr-ink" viewBox="0 0 8 8" refX="7" refY="4" markerWidth="6" markerHeight="6" orient="auto">\n'
        f'      <path d="M1,1.3 L7,4 L1,6.7" fill="none" stroke="{INK}" stroke-width="1.1" stroke-linecap="round" stroke-linejoin="round"/>\n'
        f'    </marker>\n'
        f'    <marker id="arr-slate" viewBox="0 0 8 8" refX="7" refY="4" markerWidth="6" markerHeight="6" orient="auto">\n'
        f'      <path d="M1,1.3 L7,4 L1,6.7" fill="none" stroke="{SLATE}" stroke-width="1.1" stroke-linecap="round" stroke-linejoin="round"/>\n'
        f'    </marker>\n'
        f'    <marker id="arr-accent" viewBox="0 0 8 8" refX="7" refY="4" markerWidth="6" markerHeight="6" orient="auto">\n'
        f'      <path d="M1,1.3 L7,4 L1,6.7" fill="none" stroke="{ACCENT}" stroke-width="1.15" stroke-linecap="round" stroke-linejoin="round"/>\n'
        f'    </marker>\n'
        f'  </defs>\n'
        + body
        + "\n</svg>\n"
    )


def text(x, y, s, font=SERIF, size=9.5, fill=INK, anchor="start", weight="normal", style="normal", spacing=None):
    sp = f' letter-spacing="{spacing}"' if spacing else ""
    return (
        f'  <text x="{x}" y="{y}" text-anchor="{anchor}" font-family="{font}" '
        f'font-size="{size}" font-weight="{weight}" font-style="{style}" fill="{fill}"{sp}>{esc(s)}</text>'
    )


def rect(x, y, w, h, fill=WHITE, stroke=RULE, sw=0.75, rx=1.5, dash=None):
    d = f' stroke-dasharray="{dash}"' if dash else ""
    return f'  <rect x="{x}" y="{y}" width="{w}" height="{h}" rx="{rx}" fill="{fill}" stroke="{stroke}" stroke-width="{sw}"{d}/>'


def line(x1, y1, x2, y2, stroke=INK, sw=0.75, dash=None, marker=None):
    d = f' stroke-dasharray="{dash}"' if dash else ""
    m = f' marker-end="url(#{marker})"' if marker else ""
    return f'  <line x1="{x1}" y1="{y1}" x2="{x2}" y2="{y2}" stroke="{stroke}" stroke-width="{sw}"{d}{m}/>'


def path(d_str, stroke=INK, sw=0.75, fill="none", dash=None, marker=None):
    d = f' stroke-dasharray="{dash}"' if dash else ""
    m = f' marker-end="url(#{marker})"' if marker else ""
    return f'  <path d="{d_str}" fill="{fill}" stroke="{stroke}" stroke-width="{sw}" stroke-linecap="round" stroke-linejoin="round"{d}{m}/>'


def make_fig1():
    """Figure 1: The Boundary Between Maker and Auditor (Reliance Sets)."""
    w, h = 680, 224
    parts = [
        # Left zone: Alice's workshop
        rect(6, 12, 232, 198, fill=IVORY, stroke=RULE, sw=0.75),
        text(20, 31, "ALICE'S WORKSHOP", size=8.0, fill=SLATE, weight="bold", spacing="1.2"),
        text(20, 44, "Relied on for nothing in Bob's verdict", size=8.5, fill=SLATE, style="italic"),

        rect(20, 58, 92, 40, fill=WHITE, stroke=RULE, sw=0.75),
        text(66, 75, "Unified source", size=8.8, anchor="middle"),
        text(66, 89, "program.ode", font=MONO, size=7.6, fill=SLATE, anchor="middle"),

        rect(132, 58, 92, 40, fill=WHITE, stroke=RULE, sw=0.75),
        text(178, 75, "Compiler & prover", size=8.8, anchor="middle"),
        text(178, 89, "ode pack", font=MONO, size=7.6, fill=SLATE, anchor="middle"),
        line(112, 78, 130, 78, stroke=SLATE, sw=0.8, marker="arr-slate"),

        rect(20, 124, 204, 72, fill=WHITE, stroke=RULE, sw=0.65, dash="2.5,2.5"),
        text(32, 141, "What may go wrong here:", size=8.4, fill=SLATE, style="italic"),
        text(32, 156, "• Bugs in the compiler or prover", size=8.3, fill=SLATE),
        text(32, 170, "• Clever optimizations or proof search", size=8.3, fill=SLATE),
        text(32, 184, "• A hostile or mistaken author", size=8.3, fill=SLATE),

        # Center boundary & crossing artifacts
        line(258, 8, 258, 214, stroke=ACCENT, sw=0.75, dash="3,3"),
        text(322, 23, "ARTIFACT BOUNDARY", size=7.6, fill=ACCENT, anchor="middle", weight="bold", spacing="1.1"),

        # Three crossing pills
        rect(272, 46, 100, 34, fill=WHITE, stroke=ACCENT, sw=0.8),
        text(322, 60, "Binary  (.o)", font=MONO, size=7.8, fill=INK, anchor="middle"),
        text(322, 72, "bytes + .ode.ocl", size=7.6, fill=SLATE, anchor="middle"),
        line(224, 68, 270, 63, stroke=INK, sw=0.8, marker="arr-ink"),
        line(372, 63, 402, 68, stroke=ACCENT, sw=0.85, marker="arr-accent"),

        rect(272, 98, 100, 34, fill=WHITE, stroke=SLATE, sw=0.75),
        text(322, 112, "Proof  (.proof)", font=MONO, size=7.8, fill=INK, anchor="middle"),
        text(322, 124, "separate certificate", size=7.6, fill=SLATE, anchor="middle"),
        line(224, 86, 270, 115, stroke=SLATE, sw=0.75, marker="arr-slate"),
        line(372, 115, 402, 105, stroke=SLATE, sw=0.8, marker="arr-slate"),

        rect(272, 152, 100, 34, fill=IVORY, stroke=RULE, sw=0.75, dash="2.5,2.5"),
        text(322, 166, "Glossary (.json)", font=MONO, size=7.5, fill=SLATE, anchor="middle"),
        text(322, 178, "optional; not hashed", size=7.4, fill=MUTED, anchor="middle", style="italic"),
        line(224, 93, 270, 168, stroke=RULE, sw=0.7, dash="2.5,2.5", marker="arr-slate"),
        path("M 372 178 L 384 178 L 384 205 L 603 205 L 603 198", stroke=SLATE, sw=0.7, dash="2.5,2.5", marker="arr-slate"),

        # Right zone: Bob's Reliance Set
        rect(392, 12, 282, 202, fill=BLUSH, stroke=ACCENT, sw=0.95),
        text(406, 31, "BOB'S AUDIT  —  THE RELIANCE SET", size=8.0, fill=ACCENT, weight="bold", spacing="1.1"),
        text(406, 44, "Every piece Bob relies on for his verdict", size=8.5, fill=SLATE, style="italic"),

        rect(406, 58, 116, 62, fill=WHITE, stroke=ACCENT, sw=0.85),
        text(464, 75, "Small Verifier", size=9.2, fill=ACCENT, anchor="middle", weight="bold"),
        text(464, 90, "odeverify", font=MONO, size=8.0, fill=INK, anchor="middle"),
        text(464, 104, "checks machine bytes", size=7.8, fill=SLATE, anchor="middle"),
        text(464, 114, "against x86/arm64.tab", font=MONO, size=6.9, fill=SLATE, anchor="middle"),

        line(522, 89, 544, 89, stroke=ACCENT, sw=0.9, marker="arr-accent"),

        rect(546, 58, 114, 62, fill=WHITE, stroke=ACCENT, sw=0.85),
        text(603, 75, "Verdict & Digest", size=9.0, fill=INK, anchor="middle", weight="bold"),
        text(603, 91, "shown", font=MONO, size=8.8, fill=ACCENT, anchor="middle", weight="bold"),
        text(603, 106, "ode_<52-char-b32>", font=MONO, size=7.1, fill=SLATE, anchor="middle"),

        rect(406, 134, 116, 62, fill=WHITE, stroke=RULE, sw=0.75),
        text(464, 151, "Instruction Table", size=8.8, anchor="middle"),
        text(464, 165, "x86.tab (94 rows)", font=MONO, size=7.1, fill=SLATE, anchor="middle"),
        text(464, 177, "arm64.tab (54 rows)", font=MONO, size=7.1, fill=SLATE, anchor="middle"),
        text(464, 190, "silicon cross-checked", size=7.5, fill=SLATE, anchor="middle", style="italic"),
        line(464, 134, 464, 122, stroke=SLATE, sw=0.75, marker="arr-slate"),

        rect(546, 134, 114, 62, fill=WHITE, stroke=ACCENT, sw=0.85),
        text(603, 151, "Bob Reads Only", size=8.8, fill=ACCENT, anchor="middle", weight="bold"),
        text(603, 166, "<hash>.ocl", font=MONO, size=8.0, fill=INK, anchor="middle"),
        text(603, 180, "nameless contract;", size=7.8, fill=SLATE, anchor="middle"),
        text(603, 191, "0 register names", size=7.8, fill=SLATE, anchor="middle"),
        line(603, 120, 603, 132, stroke=ACCENT, sw=0.8, marker="arr-accent"),
    ]
    (OUT / "fig1-boundary.svg").write_text(svg_wrap(w, h, "\n".join(parts)))


def make_fig2():
    """Figure 2: From Author's Names to Content Identity (ode canon)."""
    w, h = 680, 196
    parts = [
        # Left box: Author's contract
        rect(6, 14, 214, 168, fill=IVORY, stroke=RULE, sw=0.75),
        text(18, 32, "AUTHORED CONTRACT  (.ode)", size=7.8, fill=SLATE, weight="bold", spacing="1.0"),
        text(18, 52, "// 1 if all bytes are zero", font=MONO, size=7.4, fill=MUTED),
        text(18, 66, "def zero_from(a, i) {", font=MONO, size=7.6, fill=INK),
        text(18, 78, "  if i == len(a) then 1", font=MONO, size=7.4, fill=INK),
        text(18, 90, "  else if a[i] != 0 then 0", font=MONO, size=7.4, fill=INK),
        text(18, 102, "  else zero_from(a, i + 1)", font=MONO, size=7.4, fill=INK),
        text(18, 114, "}", font=MONO, size=7.6, fill=INK),
        text(18, 130, "fn all_zero(a: n bytes, n: number)", font=MONO, size=7.3, fill=INK),
        text(18, 143, "  returns zero_from(a, 0)", font=MONO, size=7.4, fill=INK),
        text(18, 156, "  trace depends on a, n", font=MONO, size=7.4, fill=INK),
        text(18, 169, "  stack 0  { for x86_64 ... }", font=MONO, size=7.3, fill=SLATE),

        # Center transform
        line(220, 96, 286, 96, stroke=ACCENT, sw=0.95, marker="arr-accent"),
        text(253, 86, "ode canon", font=MONO, size=8.0, fill=ACCENT, anchor="middle", weight="bold"),
        text(253, 110, "strip comments", size=7.6, fill=SLATE, anchor="middle", style="italic"),
        text(253, 121, "drop unused defs", size=7.6, fill=SLATE, anchor="middle", style="italic"),
        text(253, 132, "number all slots", size=7.6, fill=SLATE, anchor="middle", style="italic"),

        # Right upper: Canonical .ocl
        rect(286, 14, 222, 116, fill=BLUSH, stroke=ACCENT, sw=0.9),
        text(298, 31, "CANONICAL CONTRACT  (.ocl)", size=7.8, fill=ACCENT, weight="bold", spacing="1.0"),
        text(298, 48, "def f1(p0, p1) {", font=MONO, size=7.4, fill=INK),
        text(298, 60, "  if p1 == len(p0) then 1 ...", font=MONO, size=7.3, fill=INK),
        text(298, 72, "}", font=MONO, size=7.4, fill=INK),
        text(298, 86, "contract (a0: a1 bytes, a1: number) {", font=MONO, size=7.0, fill=INK),
        text(298, 98, "  returns f0(a0)", font=MONO, size=7.3, fill=INK),
        text(298, 110, "  trace depends on a0, a1", font=MONO, size=7.3, fill=INK),
        text(298, 122, "  stack 0 }", font=MONO, size=7.3, fill=INK),

        # Right lower: Glossary
        rect(286, 140, 222, 42, fill=WHITE, stroke=RULE, sw=0.75, dash="2.5,2.5"),
        text(298, 155, "PERSONAL GLOSSARY  (never hashed)", size=7.3, fill=SLATE, weight="bold", spacing="0.8"),
        text(298, 171, '{ a0: "a", a1: "n", f0: "all_zero" }', font=MONO, size=7.2, fill=SLATE),

        # Far right: BLAKE3 identity
        line(508, 72, 532, 72, stroke=ACCENT, sw=0.95, marker="arr-accent"),
        rect(536, 14, 138, 116, fill=WHITE, stroke=ACCENT, sw=0.9),
        text(604, 32, "BLAKE3-256", size=8.0, fill=ACCENT, anchor="middle", weight="bold", spacing="1.0"),
        text(604, 46, "52-char base-32 digest", size=7.8, fill=SLATE, anchor="middle", style="italic"),
        text(604, 65, "jbqyjqpese4s4cq35q", font=MONO, size=7.2, fill=ACCENT, anchor="middle", weight="bold"),
        text(604, 76, "xlhaevjvzuaqznquqw", font=MONO, size=7.2, fill=ACCENT, anchor="middle", weight="bold"),
        text(604, 87, "6mtlaqleluc25ika", font=MONO, size=7.2, fill=ACCENT, anchor="middle", weight="bold"),
        line(548, 97, 660, 97, stroke=RULE, sw=0.6),
        text(604, 111, "Symbol: ode_<52>", font=MONO, size=7.3, fill=INK, anchor="middle"),
        text(604, 123, "File:   <52>.ocl", font=MONO, size=7.3, fill=INK, anchor="middle"),

        # Note under far right
        text(604, 156, "Same contract on x86-64", size=8.0, fill=SLATE, anchor="middle", style="italic"),
        text(604, 168, "and AArch64 → same hash", size=8.0, fill=SLATE, anchor="middle", style="italic"),
    ]
    (OUT / "fig2-canon.svg").write_text(svg_wrap(w, h, "\n".join(parts)))


def make_fig3():
    """Figure 3: Closed-World Memory Pieces, Disjointness, and Lending."""
    w, h = 680, 214
    parts = [
        text(10, 16, "CALLER'S MEMORY PIECES  (pairwise disjoint: no_overlap)", size=8.0, fill=SLATE, weight="bold", spacing="0.9"),

        # Piece 1: input (read-only)
        rect(10, 44, 132, 46, fill=IVORY, stroke=SLATE, sw=0.8),
        text(76, 63, "input", font=MONO, size=8.6, fill=INK, anchor="middle", weight="bold"),
        text(76, 77, "len bytes · read-only", size=7.8, fill=SLATE, anchor="middle"),

        # Disjointness gap marker
        text(158, 70, "⊥", size=11, fill=MUTED, anchor="middle"),

        # Piece 2: nd (node120 record, subdivided)
        text(312, 36, "nd : node120  (120 bytes · read/write)", font=MONO, size=7.5, fill=INK, anchor="middle"),
        rect(174, 44, 276, 46, fill=WHITE, stroke=INK, sw=0.9),
        rect(174, 44, 62, 46, fill=IVORY, stroke=INK, sw=0.65),
        text(205, 63, "nd.h", font=MONO, size=8.0, anchor="middle"),
        text(205, 77, "0..32", font=MONO, size=7.0, fill=SLATE, anchor="middle"),

        rect(236, 44, 134, 46, fill=BLUSH, stroke=ACCENT, sw=1.0),
        text(303, 63, "nd.block  (64 B)", font=MONO, size=8.0, fill=ACCENT, anchor="middle", weight="bold"),
        text(303, 77, "32..96 · lent read/write", size=7.6, fill=ACCENT, anchor="middle"),

        rect(370, 44, 80, 46, fill=IVORY, stroke=INK, sw=0.65),
        text(410, 63, "t, blen, flg", font=MONO, size=7.6, anchor="middle"),
        text(410, 77, "96..120", font=MONO, size=7.0, fill=SLATE, anchor="middle"),

        # Gap marker
        text(466, 70, "⊥", size=11, fill=MUTED, anchor="middle"),

        # Piece 3: stack
        rect(482, 44, 92, 46, fill=IVORY, stroke=SLATE, sw=0.8, dash="3,2"),
        text(528, 63, "stack", font=MONO, size=8.3, anchor="middle"),
        text(528, 77, "call-local only", size=7.6, fill=SLATE, anchor="middle"),

        text(586, 70, "⊥", size=11, fill=MUTED, anchor="middle"),

        # Piece 4: rodata
        rect(598, 44, 74, 46, fill=IVORY, stroke=RULE, sw=0.75),
        text(635, 63, ".rodata", font=MONO, size=8.0, fill=SLATE, anchor="middle"),
        text(635, 77, "program const", size=7.2, fill=MUTED, anchor="middle"),

        # Lending arrows down to callee (clean non-overlapping labels)
        path("M 76 90 C 76 122, 165 116, 185 138", stroke=SLATE, sw=0.85, marker="arr-slate"),
        text(18, 128, "lent read-only as src", size=7.8, fill=SLATE, style="italic"),

        path("M 303 90 L 303 136", stroke=ACCENT, sw=0.95, marker="arr-accent"),
        text(311, 118, "sub-span lent read/write as block", size=7.8, fill=ACCENT, style="italic"),

        # Callee box
        rect(144, 140, 260, 58, fill=WHITE, stroke=ACCENT, sw=0.9),
        text(274, 158, "Callee:  b3l_pad_fast(block, src, n)", font=MONO, size=8.1, fill=INK, anchor="middle", weight="bold"),
        text(274, 173, "ensures block = padded(src)  ·  stack 0", font=MONO, size=7.5, fill=ACCENT, anchor="middle"),
        text(274, 188, "Cannot read or touch nd.h, t, blen, flags, or caller stack", size=7.9, fill=SLATE, anchor="middle", style="italic"),

        # Preservation callout on the right
        rect(430, 140, 242, 58, fill=IVORY, stroke=RULE, sw=0.75),
        text(442, 158, "What stays proven on return:", size=8.4, fill=INK, weight="bold"),
        text(442, 173, "• nd.block now satisfies padded(src)", size=8.1, fill=ACCENT),
        text(442, 187, "• Other pieces (nd.h, t, blen, flags) keep entry values", size=8.0, fill=SLATE),
    ]
    (OUT / "fig3-memory.svg").write_text(svg_wrap(w, h, "\n".join(parts)))


def make_fig4():
    """Figure 4: Three Ways to Transfer Control (C ABI vs Custom/Zero-Stack Arm vs Tail Call)."""
    w, h = 680, 224
    pw = 212
    xs = [8, 234, 460]
    parts = []

    # Panel A: Standard C ABI
    x = xs[0]
    parts += [
        rect(x, 12, pw, 200, fill=IVORY, stroke=RULE, sw=0.75),
        text(x + 12, 30, "A.  C-ABI CALL  (BOUNDARY)", size=7.6, fill=SLATE, weight="bold", spacing="0.8"),
        text(x + 12, 43, "Required at FFI exports (STB_GLOBAL)", size=7.8, fill=SLATE, style="italic"),
        rect(x + 14, 54, 184, 34, fill=WHITE, stroke=RULE, sw=0.75),
        text(x + 22, 68, "push rbx..r15 / stp x19..x30", font=MONO, size=7.0, fill=INK),
        text(x + 22, 81, "shuffle args into rdi..r9 / x0..x7", size=7.4, fill=SLATE),
        line(x + 106, 88, x + 106, 104, stroke=SLATE, sw=0.8, marker="arr-slate"),
        rect(x + 24, 106, 164, 32, fill=WHITE, stroke=SLATE, sw=0.8),
        text(x + 106, 120, "call / bl  helper", font=MONO, size=7.7, anchor="middle"),
        text(x + 106, 132, "saves & restores own frame", size=7.4, fill=SLATE, anchor="middle"),
        line(x + 106, 138, x + 106, 154, stroke=SLATE, sw=0.8, marker="arr-slate"),
        rect(x + 14, 156, 184, 28, fill=WHITE, stroke=RULE, sw=0.75),
        text(x + 106, 173, "pop rbx..r15  ·  ret", font=MONO, size=7.4, fill=INK, anchor="middle"),
        text(x + 106, 200, "Stack frame: 48–64+ bytes", size=8.0, fill=SLATE, anchor="middle", style="italic"),
    ]

    # Panel B: Custom Ode Calling + Zero-Stack AArch64
    x = xs[1]
    parts += [
        rect(x, 12, pw, 200, fill=WHITE, stroke=SLATE, sw=0.8),
        text(x + 12, 30, "B.  CUSTOM CALLING + x30 IN x15", size=7.6, fill=INK, weight="bold", spacing="0.6"),
        text(x + 12, 43, "Internal STB_LOCAL non-leaf caller", size=7.8, fill=SLATE, style="italic"),
        rect(x + 14, 54, 184, 34, fill=IVORY, stroke=RULE, sw=0.75),
        text(x + 22, 68, "mov x15, x30   // save link", font=MONO, size=7.2, fill=ACCENT),
        text(x + 22, 81, "keep live vars in preserved regs", size=7.4, fill=SLATE),
        line(x + 106, 88, x + 106, 104, stroke=INK, sw=0.8, marker="arr-ink"),
        rect(x + 20, 106, 172, 34, fill=BLUSH, stroke=ACCENT, sw=0.85),
        text(x + 106, 120, "bl  helper   (preserves x15)", font=MONO, size=7.3, fill=ACCENT, anchor="middle", weight="bold"),
        text(x + 106, 133, "in a=x10, b=x11  ·  out=x10", font=MONO, size=7.0, fill=INK, anchor="middle"),
        line(x + 106, 140, x + 106, 154, stroke=INK, sw=0.8, marker="arr-ink"),
        rect(x + 14, 156, 184, 28, fill=IVORY, stroke=RULE, sw=0.75),
        text(x + 106, 173, "mov x30, x15  ·  ret", font=MONO, size=7.4, fill=INK, anchor="middle"),
        text(x + 106, 200, "Stack frame: 0 bytes on AArch64", size=8.0, fill=ACCENT, anchor="middle", weight="bold"),
    ]

    # Panel C: Verified Tail Call
    x = xs[2]
    parts += [
        rect(x, 12, pw, 200, fill=BLUSH, stroke=ACCENT, sw=0.95),
        text(x + 12, 30, "C.  VERIFIED TAIL CALL  (jmp / b)", size=7.6, fill=ACCENT, weight="bold", spacing="0.6"),
        text(x + 12, 43, "Zero call/ret round-trip, zero new rows", size=7.8, fill=SLATE, style="italic"),
        rect(x + 14, 54, 184, 34, fill=WHITE, stroke=ACCENT, sw=0.75),
        text(x + 22, 68, "sp == 0  &  x30 intact", font=MONO, size=7.3, fill=INK),
        text(x + 22, 81, "caller keeps ⊆ callee preserves", font=MONO, size=7.0, fill=SLATE),
        line(x + 106, 88, x + 106, 108, stroke=ACCENT, sw=0.95, marker="arr-accent"),
        text(x + 114, 102, "jmp / b", font=MONO, size=7.6, fill=ACCENT, weight="bold"),
        rect(x + 20, 110, 172, 40, fill=WHITE, stroke=ACCENT, sw=0.9),
        text(x + 106, 126, "callee entry point", font=MONO, size=7.8, fill=ACCENT, anchor="middle", weight="bold"),
        text(x + 106, 141, "returns directly to outer caller", size=7.7, fill=SLATE, anchor="middle"),
        line(x + 106, 150, x + 106, 174, stroke=ACCENT, sw=0.9, marker="arr-accent"),
        text(x + 106, 186, "outer caller receives result directly", size=7.6, fill=INK, anchor="middle", style="italic"),
        text(x + 106, 202, "12 insns total on 64 B BLAKE3", size=8.0, fill=ACCENT, anchor="middle", weight="bold"),
    ]
    (OUT / "fig4-calling.svg").write_text(svg_wrap(w, h, "\n".join(parts)))


def make_fig5():
    """Figure 5: Anatomy of a Packed & Audited ELF Object Bundle."""
    w, h = 680, 194
    parts = [
        # Left: ELF .o file cutaway
        rect(8, 12, 408, 170, fill=WHITE, stroke=INK, sw=0.9),
        text(20, 30, "ELF RELOCATABLE OBJECT  (bundle.o)", size=8.0, fill=INK, weight="bold", spacing="1.0"),
        text(404, 30, "100% checked by ode audit", size=7.8, fill=ACCENT, anchor="end", style="italic"),

        # .text band
        rect(20, 42, 384, 52, fill=BLUSH, stroke=ACCENT, sw=0.9),
        text(30, 57, ".text", font=MONO, size=8.3, fill=ACCENT, weight="bold"),
        text(70, 57, "100% of executable bytes covered by verified functions", size=8.0, fill=INK),
        rect(30, 64, 122, 22, fill=WHITE, stroke=ACCENT, sw=0.8),
        text(91, 78, "STB_GLOBAL  ode_<52>", font=MONO, size=7.2, fill=ACCENT, anchor="middle", weight="bold"),
        rect(162, 64, 108, 22, fill=IVORY, stroke=SLATE, sw=0.7),
        text(216, 78, "STB_LOCAL  helper_1", font=MONO, size=7.0, fill=INK, anchor="middle"),
        rect(278, 64, 116, 22, fill=IVORY, stroke=SLATE, sw=0.7),
        text(336, 78, "STB_LOCAL  helper_k", font=MONO, size=7.0, fill=INK, anchor="middle"),
        line(152, 75, 160, 75, stroke=ACCENT, sw=0.75, marker="arr-accent"),
        line(270, 75, 276, 75, stroke=SLATE, sw=0.75, marker="arr-slate"),

        # .rodata + .ode.ocl row
        rect(20, 102, 136, 36, fill=IVORY, stroke=RULE, sw=0.75),
        text(30, 117, ".rodata", font=MONO, size=8.0, fill=INK, weight="bold"),
        text(30, 130, "read-only constants", size=7.6, fill=SLATE),

        rect(166, 102, 238, 36, fill=BLUSH, stroke=ACCENT, sw=0.85),
        text(176, 117, ".ode.ocl", font=MONO, size=8.0, fill=ACCENT, weight="bold"),
        text(238, 117, "(non-executable metadata)", size=7.6, fill=SLATE, style="italic"),
        text(176, 130, "BLAKE3(.ode.ocl) == exported ode_<52>", font=MONO, size=7.0, fill=INK),

        # Forbidden sections bar
        rect(20, 146, 384, 24, fill=IVORY, stroke=RULE, sw=0.65, dash="2.5,2.5"),
        text(30, 162, "Refused if present:  .init_array · .fini_array · extra globals · undefined symbols", size=7.8, fill=SLATE),

        # Connecting arrow from .proof -> .o ("verifies")
        line(448, 98, 419, 98, stroke=ACCENT, sw=0.95, marker="arr-accent"),
        text(433, 91, "certifies", size=7.2, fill=ACCENT, anchor="middle", style="italic"),

        # Right: Separate .proof file
        rect(448, 12, 224, 170, fill=IVORY, stroke=SLATE, sw=0.8),
        text(460, 30, "SEPARATE PROOF  (bundle.proof)", size=7.8, fill=INK, weight="bold", spacing="0.9"),
        text(460, 43, "Relied on for nothing — checked line by line", size=7.6, fill=SLATE, style="italic"),

        rect(460, 54, 200, 36, fill=WHITE, stroke=RULE, sw=0.75),
        text(470, 68, "order:  helper_1, ..., ode_<52>", font=MONO, size=7.1, fill=INK),
        text(470, 81, "topological (no hidden cycles)", size=7.4, fill=SLATE, style="italic"),

        rect(460, 98, 200, 34, fill=WHITE, stroke=RULE, sw=0.75),
        text(470, 112, "helper contracts + calling { ... }", font=MONO, size=7.0, fill=INK),
        text(470, 124, "internal only; never in .ode.ocl", size=7.4, fill=SLATE, style="italic"),

        rect(460, 140, 200, 32, fill=WHITE, stroke=RULE, sw=0.75),
        text(470, 154, "linear facts, places, clear steps", font=MONO, size=7.0, fill=INK),
        text(470, 166, "verified directly against .text bytes", size=7.4, fill=ACCENT, style="italic"),
    ]
    (OUT / "fig5-bundle.svg").write_text(svg_wrap(w, h, "\n".join(parts)))


def make_fig6():
    """Figure 6: Verified BLAKE3 Throughput on Zen 5 (Tufte Small Multiples)."""
    w, h = 680, 252
    parts = []

    # ---- LEFT PANEL: Short inputs (64 B, 256 B, 1 KiB) ----
    # Exact verified Zen 5 medians (GiB/s) from pinned-run SUMMARY.md
    lx0, lx1 = 44, 272
    ly0, ly1 = 44, 202  # y=1.5 at 44, y=0.0 at 202
    ymax_l = 1.5

    def ly(v):
        return ly1 - (v / ymax_l) * (ly1 - ly0)

    parts += [
        text(lx0, 20, "SHORT INPUTS  (64 B – 1 KiB)", size=8.0, fill=INK, weight="bold", spacing="0.9"),
        text(lx0, 32, "Custom calling + zero-copy + tail calls close the C-ABI gap", size=7.9, fill=SLATE, style="italic"),
    ]
    # Subtle horizontal reference gridlines (Tufte minimal)
    for tick in (0.0, 0.5, 1.0, 1.5):
        y = ly(tick)
        parts.append(line(lx0, y, lx1, y, stroke=RULE if tick > 0 else INK, sw=0.45 if tick > 0 else 0.7))
        parts.append(text(lx0 - 6, y + 3, f"{tick:.1f}", font=SERIF, size=7.8, fill=SLATE, anchor="end"))
    parts.append(text(12, (ly0 + ly1) / 2, "GiB/s", size=8.0, fill=SLATE, anchor="middle"))

    short_sizes = [
        ("64 B", 0.670, 1.286, 1.300, 1.161),
        ("256 B", 0.931, 0.978, 1.033, 0.904),
        ("1 KiB", 0.940, 0.951, 0.981, 0.933),
    ]
    centers = [82, 158, 234]
    bw = 13
    for cx, (lbl, base, ode_v, nxt, off) in zip(centers, short_sizes):
        # 4 minimalist bars: baseline (ivory/slate), Ode Step D (accent), next (charcoal), official (open outline)
        bars = [
            (cx - 2 * bw - 2, base, "#D6D1C6", SLATE, 0.5),
            (cx - bw - 0.5, ode_v, ACCENT, ACCENT, 0.6),
            (cx + 0.5, nxt, "#3A3F47", "#3A3F47", 0.6),
            (cx + bw + 2, off, WHITE, SLATE, 0.75),
        ]
        for bx, val, fill, st, sw in bars:
            top = ly(val)
            parts.append(rect(bx, top, bw - 1.5, ly1 - top, fill=fill, stroke=st, sw=sw, rx=0.5))
        # Direct numeric annotation on Ode bar (clear of neighboring bars)
        label_y = min(ly(ode_v), ly(nxt)) - 5
        parts.append(text(cx - bw / 2 - 2, label_y, f"{ode_v:.2f}", font=SERIF, size=7.6, fill=ACCENT, anchor="middle", weight="bold"))
        if lbl == "64 B":
            parts.append(text(cx - 1.5 * bw - 2, ly(base) - 4, f"{base:.2f}", font=SERIF, size=7.2, fill=SLATE, anchor="middle"))
        parts.append(text(cx, ly1 + 14, lbl, font=SERIF, size=8.2, fill=INK, anchor="middle"))

    # Tiny clean horizontal key under left panel (inline, no box)
    ky = 232
    items_l = [
        (44, "#D6D1C6", SLATE, "Ode baseline"),
        (114, ACCENT, ACCENT, "Ode verified"),
        (182, "#3A3F47", "#3A3F47", "next (hand)"),
        (246, WHITE, SLATE, "official"),
    ]
    for ix, fl, st, lab in items_l:
        parts.append(rect(ix, ky - 6.5, 7, 7, fill=fl, stroke=st, sw=0.75, rx=0.5))
        parts.append(text(ix + 10, ky, lab, size=7.4, fill=ACCENT if fl == ACCENT else SLATE, weight="bold" if fl == ACCENT else "normal"))

    # ---- RIGHT PANEL: Full Sweep (4 KiB – 1 MiB) ----
    rx0, rx1 = 334, 608
    ry0, ry1 = 44, 202
    ymax_r = 18.0

    def ry(v):
        return ry1 - (v / ymax_r) * (ry1 - ry0)

    parts += [
        text(rx0, 20, "LARGE INPUTS  (4 KiB – 1 MiB)", size=8.0, fill=INK, weight="bold", spacing="0.9"),
        text(rx0, 32, "Verified AVX-512 32-way tree reaches 98.4% of next, 131.7% of official", size=7.9, fill=SLATE, style="italic"),
    ]
    for tick in (0, 4, 8, 12, 16):
        y = ry(tick)
        parts.append(line(rx0, y, rx1, y, stroke=RULE if tick > 0 else INK, sw=0.45 if tick > 0 else 0.7))
        parts.append(text(rx0 - 6, y + 3, f"{tick}", font=SERIF, size=7.8, fill=SLATE, anchor="end"))

    # Exact verified Zen 5 Step D medians (4 KiB .. 1 MiB)
    sweep = [
        ("4K",   2.162,  3.336,  3.413),
        ("16K",  6.299, 10.713, 10.734),
        ("32K",  9.221, 15.333, 11.582),
        ("64K", 14.795, 15.999, 12.023),
        ("128K",14.658, 16.357, 12.275),
        ("256K",16.336, 16.601, 12.405),
        ("1M",  15.851, 16.032, 12.356),
    ]
    xs_r = [rx0 + 12 + i * ((rx1 - rx0 - 24) / (len(sweep) - 1)) for i in range(len(sweep))]

    def poly(idx, stroke, sw, dash=None):
        pts = " ".join(f"{'M' if i == 0 else 'L'} {xs_r[i]:.1f} {ry(row[idx]):.1f}" for i, row in enumerate(sweep))
        return path(pts, stroke=stroke, sw=sw, dash=dash)

    # Curves: official (dashed slate), next (thin charcoal), Ode verified (bold Venetian red)
    parts.append(poly(3, MUTED, 1.0, dash="3,2.5"))
    parts.append(poly(2, "#3A3F47", 1.15))
    parts.append(poly(1, ACCENT, 1.75))

    for i, (lbl, ode_v, nxt, off) in enumerate(sweep):
        cx = xs_r[i]
        parts.append(f'  <circle cx="{cx:.1f}" cy="{ry(ode_v):.1f}" r="2.3" fill="{ACCENT}" stroke="{WHITE}" stroke-width="0.6"/>')
        parts.append(f'  <circle cx="{cx:.1f}" cy="{ry(nxt):.1f}" r="1.7" fill="#3A3F47"/>')
        parts.append(text(f"{cx:.1f}", ry1 + 14, lbl, font=SERIF, size=7.8, fill=INK, anchor="middle"))

    # Direct end-of-line labels (Tufte signature!)
    parts.append(text(rx1 + 6, ry(16.032) - 4, "next  16.0", size=7.7, fill="#3A3F47"))
    parts.append(text(rx1 + 6, ry(15.851) + 7, "Ode  15.9", size=7.9, fill=ACCENT, weight="bold"))
    parts.append(text(rx1 + 6, ry(12.356) + 3, "official  12.4", size=7.6, fill=MUTED))

    # Honest mid-size callout
    parts.append(line(xs_r[1] + 2, ry(6.299) + 3, xs_r[1] + 22, ry(3.2), stroke=SLATE, sw=0.6))
    parts.append(text(xs_r[1] + 25, ry(3.0), "4–32 KiB gap: 4/8/16-way", size=7.4, fill=SLATE, style="italic"))
    parts.append(text(xs_r[1] + 25, ry(1.8), "tiers not yet added", size=7.4, fill=SLATE, style="italic"))

    # Peak highlight at 256 KiB
    parts.append(text(f"{xs_r[5]:.1f}", ry(16.601) - 8, "16.34", size=7.6, fill=ACCENT, anchor="middle", weight="bold"))
    parts.append(text(rx0 - 6, ry(17.7), "GiB/s", size=7.2, fill=SLATE, anchor="end", style="italic"))

    # Bottom caption note
    parts.append(text(rx0, 232, "Zen 5 Linux · verified pinned-run · 45 interleaved trials/size · median GiB/s", size=7.4, fill=SLATE, style="italic"))

    (OUT / "fig6-blake3-perf.svg").write_text(svg_wrap(w, h, "\n".join(parts)))


if __name__ == "__main__":
    make_fig1()
    make_fig2()
    make_fig3()
    make_fig4()
    make_fig5()
    make_fig6()
    print("Wrote 6 figures to", OUT)
