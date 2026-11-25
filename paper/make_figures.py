#!/usr/bin/env pypy3
"""Generate the six co-designed vector figures for the Ode Language Report.

Visual vocabulary (shared with paper/ode.typ):
  - Serif: Palatino (prose, headings, figure labels)
  - Mono:  Menlo (code, symbols, registers, hashes)
  - Palette:
      ink      #1C1E21  warm charcoal (primary text & strokes)
      slate    #5B6470  quiet slate (hairlines, annotations, secondary curves)
      rule     #CFC9BC  warm hairline rule
      accent   #9E2A2B  Venetian terracotta (quiet typographic micro-accents, arrows, data series)
      ivory    #F7F5F0  soft paper tint (neutral ground)
      sand     #EEEBE2  warm sandstone tint (highlighted architectural panels — never red/blush boxes)
      charcoal #2E343D  authoritative dark border for emphasized zones
      white    #FFFFFF  clean card ground
"""
from pathlib import Path

OUT = Path(__file__).resolve().parent / "figures"
OUT.mkdir(parents=True, exist_ok=True)

INK = "#1C1E21"
CHARCOAL = "#2E343D"
SLATE = "#5B6470"
MUTED = "#7D8590"
RULE = "#CFC9BC"
ACCENT = "#9E2A2B"
IVORY = "#F7F5F0"
SAND = "#EEEBE2"
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
        text(30, 141, "What may go wrong here:", size=8.5, fill=SLATE, style="italic"),
        text(30, 156, "• Bugs in the compiler or prover", size=8.4, fill=SLATE),
        text(30, 170, "• Optimizing rewrites or search bugs", size=8.4, fill=SLATE),
        text(30, 184, "• A hostile or mistaken author", size=8.4, fill=SLATE),

        # Center boundary & crossing artifacts
        line(256, 8, 256, 214, stroke=SLATE, sw=0.8, dash="3,3"),
        text(322, 23, "ARTIFACT BOUNDARY", size=7.8, fill=SLATE, anchor="middle", weight="bold", spacing="1.0"),

        # Three crossing pills
        rect(270, 46, 102, 36, fill=WHITE, stroke=CHARCOAL, sw=0.85),
        text(321, 61, "Binary (.o)", font=MONO, size=8.0, fill=INK, anchor="middle"),
        text(321, 74, "bytes + .ode.ocl", size=7.9, fill=SLATE, anchor="middle"),
        line(224, 68, 268, 64, stroke=INK, sw=0.85, marker="arr-ink"),
        line(372, 64, 390, 64, stroke=ACCENT, sw=0.9, marker="arr-accent"),

        rect(270, 98, 102, 36, fill=WHITE, stroke=SLATE, sw=0.8),
        text(321, 113, "Proof (.proof)", font=MONO, size=8.0, fill=INK, anchor="middle"),
        text(321, 126, "separate file", size=7.9, fill=SLATE, anchor="middle"),
        line(224, 86, 268, 116, stroke=SLATE, sw=0.8, marker="arr-slate"),
        line(372, 116, 390, 116, stroke=SLATE, sw=0.85, marker="arr-slate"),

        rect(270, 152, 102, 36, fill=IVORY, stroke=SLATE, sw=0.75, dash="3,2.5"),
        text(321, 167, "Glossary (.json)", font=MONO, size=7.7, fill=SLATE, anchor="middle"),
        text(321, 180, "optional; never hashed", size=7.8, fill=SLATE, anchor="middle", style="italic"),
        line(224, 93, 268, 170, stroke=SLATE, sw=0.75, dash="3,2.5", marker="arr-slate"),
        path("M 372 178 L 382 178 L 382 206 L 603 206 L 603 198", stroke=SLATE, sw=0.8, dash="3,2.5", marker="arr-slate"),

        # Right zone: Bob's Reliance Set (calm sandstone ground + dark charcoal frame)
        rect(392, 12, 282, 202, fill=SAND, stroke=CHARCOAL, sw=1.0),
        text(406, 31, "BOB'S AUDIT  —  THE RELIANCE SET", size=8.1, fill=INK, weight="bold", spacing="1.0"),
        text(406, 44, "Every piece Bob relies on for his verdict", size=8.5, fill=SLATE, style="italic"),

        rect(406, 58, 116, 62, fill=WHITE, stroke=CHARCOAL, sw=0.85),
        text(464, 75, "Small Verifier", size=9.2, fill=INK, anchor="middle", weight="bold"),
        text(464, 90, "odeverify", font=MONO, size=8.2, fill=INK, anchor="middle"),
        text(464, 104, "checks machine bytes", size=8.0, fill=SLATE, anchor="middle"),
        text(464, 115, "via x86/arm64.tab", font=MONO, size=7.4, fill=SLATE, anchor="middle"),

        line(522, 89, 544, 89, stroke=ACCENT, sw=0.95, marker="arr-accent"),

        rect(546, 58, 114, 62, fill=WHITE, stroke=CHARCOAL, sw=0.85),
        text(603, 75, "Verdict & Digest", size=9.0, fill=INK, anchor="middle", weight="bold"),
        text(603, 91, "shown", font=MONO, size=9.0, fill=INK, anchor="middle", weight="bold"),
        text(603, 107, "ode_<52-char-b32>", font=MONO, size=7.4, fill=SLATE, anchor="middle"),

        rect(406, 134, 116, 62, fill=WHITE, stroke=SLATE, sw=0.75),
        text(464, 151, "Instruction Tables", size=8.8, anchor="middle"),
        text(464, 165, "x86.tab (94 rows)", font=MONO, size=7.4, fill=SLATE, anchor="middle"),
        text(464, 177, "arm64.tab (54 rows)", font=MONO, size=7.4, fill=SLATE, anchor="middle"),
        text(464, 190, "silicon cross-checked", size=7.8, fill=SLATE, anchor="middle", style="italic"),
        line(464, 134, 464, 122, stroke=SLATE, sw=0.8, marker="arr-slate"),

        rect(546, 134, 114, 62, fill=WHITE, stroke=CHARCOAL, sw=0.85),
        text(603, 151, "Contract Audited", size=8.8, fill=INK, anchor="middle", weight="bold"),
        text(603, 166, "<hash>.ocl", font=MONO, size=8.2, fill=INK, anchor="middle"),
        text(603, 180, "nameless contract;", size=8.0, fill=SLATE, anchor="middle"),
        text(603, 191, "0 register names", size=8.0, fill=SLATE, anchor="middle"),
        line(603, 120, 603, 132, stroke=SLATE, sw=0.85, marker="arr-slate"),
    ]
    (OUT / "fig1-boundary.svg").write_text(svg_wrap(w, h, "\n".join(parts)))


def all_zero_example():
    """The report's running example, read from the file the tests pack, and its canonical contract as
    `ode canon` makes it (so that no figure shows a contract or a digest typed in by hand)."""
    import sys
    root = Path(__file__).resolve().parent.parent
    for d in ("lang", "kcheck"):
        if str(root / d) not in sys.path:
            sys.path.insert(0, str(root / d))
    import ode_canon
    src = (Path(__file__).resolve().parent / "examples" / "all_zero.ode").read_text()
    lines = src.split("\n")
    end = next(i for i, l in enumerate(lines) if l.strip() == "{")
    canon = ode_canon.canonicalize_ode(src, fn_name="all_zero", target="x86_64")
    other = ode_canon.canonicalize_ode(src, fn_name="all_zero", target="arm64")
    assert canon["contract_id"] == other["contract_id"] and canon["canonical"] == other["canonical"]
    return lines[:end], canon


def make_fig2():
    """Figure 2: from the author's text to the canonical contract and its digest (`ode canon`)."""
    authored, canon = all_zero_example()
    cid = canon["contract_id"]
    assert len(cid) == 52
    w, h = 680, 232
    pitch = 10.8
    parts = [
        rect(6, 12, 204, 208, fill=IVORY, stroke=RULE, sw=0.75),
        text(16, 30, "AS THE AUTHOR WROTE IT  (.ode)", size=8.0, fill=SLATE, weight="bold", spacing="0.7"),
    ]
    for i, l in enumerate(authored):
        if l.strip():
            indent = (len(l) - len(l.lstrip(" "))) * 0.602 * 7.5
            parts.append(text(16 + indent, 48 + i * pitch, l.strip(), font=MONO, size=7.5, fill=MUTED if l.lstrip().startswith("//") else INK))

    parts += [
        line(210, 110, 268, 110, stroke=ACCENT, sw=1.0, marker="arr-accent"),
        text(239, 100, "ode canon", font=MONO, size=8.4, fill=ACCENT, anchor="middle", weight="bold"),
        text(239, 126, "leaves out", size=8.0, fill=SLATE, anchor="middle", style="italic"),
        text(239, 137, "comments;", size=8.0, fill=SLATE, anchor="middle", style="italic"),
        text(239, 152, "numbers", size=8.0, fill=SLATE, anchor="middle", style="italic"),
        text(239, 163, "every name", size=8.0, fill=SLATE, anchor="middle", style="italic"),

        rect(270, 12, 214, 208, fill=SAND, stroke=CHARCOAL, sw=0.95),
        text(280, 30, "THE CANONICAL CONTRACT  (.ocl)", size=8.0, fill=INK, weight="bold", spacing="0.7"),
    ]
    for i, l in enumerate(canon["canonical"].rstrip("\n").split("\n")):
        if l.strip():
            indent = (len(l) - len(l.lstrip(" "))) * 0.602 * 7.5
            parts.append(text(280 + indent, 48 + i * pitch, l.strip(), font=MONO, size=7.5, fill=INK))

    parts += [
        line(484, 62, 502, 62, stroke=ACCENT, sw=1.0, marker="arr-accent"),
        rect(504, 12, 170, 114, fill=WHITE, stroke=CHARCOAL, sw=0.95),
        text(589, 30, "BLAKE3 OF THAT TEXT", size=8.0, fill=INK, anchor="middle", weight="bold", spacing="0.7"),
        text(589, 43, "256 bits as 52 characters", size=8.0, fill=SLATE, anchor="middle", style="italic"),
        text(589, 61, cid[:18], font=MONO, size=7.7, fill=INK, anchor="middle", weight="bold"),
        text(589, 73, cid[18:36], font=MONO, size=7.7, fill=INK, anchor="middle", weight="bold"),
        text(589, 85, cid[36:], font=MONO, size=7.7, fill=INK, anchor="middle", weight="bold"),
        line(516, 94, 662, 94, stroke=RULE, sw=0.6),
        text(589, 107, "symbol  ode_<these 52>", font=MONO, size=7.4, fill=INK, anchor="middle"),
        text(589, 119, "file    <these 52>.ocl", font=MONO, size=7.4, fill=INK, anchor="middle"),

        rect(504, 136, 170, 84, fill=WHITE, stroke=SLATE, sw=0.75, dash="3,2.5"),
        text(516, 152, "A READER'S GLOSSARY  (not hashed)", size=7.5, fill=SLATE, weight="bold", spacing="0.4"),
    ]
    entries = [(k, v) for k, v in canon["glossary"].items() if k != "contract"]
    for i, (k, v) in enumerate(entries):
        parts.append(text(516, 168 + i * 11.5, f"{k}  =  {v}", font=MONO, size=7.5, fill=SLATE))
    (OUT / "fig2-canon.svg").write_text(svg_wrap(w, h, "\n".join(parts)))


def make_fig3():
    """Figure 3: Closed-World Memory Pieces, Disjointness, and Lending."""
    w, h = 680, 224
    parts = [
        text(10, 16, "THE CALLER'S PIECES OF MEMORY  (no two of them overlap)", size=8.2, fill=SLATE, weight="bold", spacing="0.7"),

        # Piece 1: input (read-only)
        rect(10, 46, 126, 48, fill=IVORY, stroke=SLATE, sw=0.85),
        text(73, 66, "input", font=MONO, size=8.8, fill=INK, anchor="middle", weight="bold"),
        text(73, 81, "len bytes · read-only", size=8.0, fill=SLATE, anchor="middle"),

        text(154, 72, "disjoint", size=7.2, fill=MUTED, anchor="middle", style="italic"),

        # Piece 2: nd (node120 record, subdivided into 3 adjacent fields)
        text(312, 36, "nd : node120  (one record of 120 bytes)", font=MONO, size=7.8, fill=INK, anchor="middle"),
        rect(172, 46, 280, 48, fill=WHITE, stroke=CHARCOAL, sw=1.0),
        rect(174, 48, 54, 44, fill=IVORY, stroke=RULE, sw=0.65),
        text(201, 67, "nd.h", font=MONO, size=8.2, anchor="middle"),
        text(201, 81, "0..32", font=MONO, size=7.3, fill=SLATE, anchor="middle"),

        rect(231, 48, 122, 44, fill=SAND, stroke=CHARCOAL, sw=0.95),
        text(292, 67, "nd.block", font=MONO, size=8.2, fill=INK, anchor="middle", weight="bold"),
        text(292, 81, "bytes 32..96 · lent", size=7.8, fill=ACCENT, anchor="middle"),

        rect(356, 48, 94, 44, fill=IVORY, stroke=RULE, sw=0.65),
        text(403, 67, "counter, length,", font=MONO, size=7.3, anchor="middle"),
        text(403, 81, "flags · 96..120", font=MONO, size=7.3, fill=SLATE, anchor="middle"),

        text(468, 72, "disjoint", size=7.2, fill=MUTED, anchor="middle", style="italic"),

        # Piece 3: stack
        rect(484, 46, 90, 48, fill=IVORY, stroke=SLATE, sw=0.85, dash="3,2"),
        text(529, 66, "stack", font=MONO, size=8.5, anchor="middle"),
        text(529, 81, "call-local", size=7.9, fill=SLATE, anchor="middle"),

        # Piece 4: rodata
        rect(596, 46, 76, 48, fill=IVORY, stroke=RULE, sw=0.8),
        text(634, 66, ".rodata", font=MONO, size=8.2, fill=SLATE, anchor="middle"),
        text(634, 81, "const data", size=7.7, fill=SLATE, anchor="middle"),

        # Lending arrows down to callee
        path("M 73 94 C 73 126, 165 120, 185 144", stroke=SLATE, sw=0.9, marker="arr-slate"),
        text(14, 132, "lent read-only as src", size=8.1, fill=SLATE, style="italic"),

        path("M 292 94 L 292 142", stroke=ACCENT, sw=1.0, marker="arr-accent"),
        text(300, 124, "a part of nd, lent to read and write, as block", size=8.1, fill=ACCENT, style="italic"),

        # Callee box
        rect(142, 146, 266, 62, fill=WHITE, stroke=CHARCOAL, sw=0.95),
        text(275, 164, "Callee:  b3l_pad_arm64(block, src, n)", font=MONO, size=8.2, fill=INK, anchor="middle", weight="bold"),
        text(275, 180, "ensures block = padded(src)  ·  stack 0", font=MONO, size=7.8, fill=ACCENT, anchor="middle"),
        text(275, 196, "It can touch nothing else of nd, nor the caller's stack", size=8.0, fill=SLATE, anchor="middle", style="italic"),

        # Preservation callout on the right
        rect(424, 146, 248, 62, fill=IVORY, stroke=RULE, sw=0.8),
        text(436, 164, "What the caller knows after the call:", size=8.5, fill=INK, weight="bold"),
        text(436, 180, "• nd.block is padded(src)", size=8.2, fill=ACCENT),
        text(436, 196, "• nd.h, counter, length, flags are as they were", size=8.2, fill=SLATE),
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
        text(x + 12, 30, "A.  THE C CONVENTION", size=7.6, fill=SLATE, weight="bold", spacing="0.8"),
        text(x + 12, 43, "where other code calls in", size=7.8, fill=SLATE, style="italic"),
        rect(x + 14, 54, 184, 34, fill=WHITE, stroke=RULE, sw=0.75),
        text(x + 22, 68, "push rbx..r15 / stp x19..x30", font=MONO, size=7.0, fill=INK),
        text(x + 22, 81, "move arguments into rdi..r9 / x0..x7", size=7.4, fill=SLATE),
        line(x + 106, 88, x + 106, 104, stroke=SLATE, sw=0.8, marker="arr-slate"),
        rect(x + 24, 106, 164, 32, fill=WHITE, stroke=SLATE, sw=0.8),
        text(x + 106, 120, "call / bl  helper", font=MONO, size=7.7, anchor="middle"),
        text(x + 106, 132, "saves and restores its own frame", size=7.4, fill=SLATE, anchor="middle"),
        line(x + 106, 138, x + 106, 154, stroke=SLATE, sw=0.8, marker="arr-slate"),
        rect(x + 14, 156, 184, 28, fill=WHITE, stroke=RULE, sw=0.75),
        text(x + 106, 173, "pop rbx..r15  ·  ret", font=MONO, size=7.4, fill=INK, anchor="middle"),
        text(x + 106, 200, "a stack frame of 16 bytes or more", size=8.0, fill=SLATE, anchor="middle", style="italic"),
    ]

    # Panel B: Custom Ode Calling + Zero-Stack AArch64
    x = xs[1]
    parts += [
        rect(x, 12, pw, 200, fill=WHITE, stroke=SLATE, sw=0.8),
        text(x + 12, 30, "B.  A CONVENTION OF ITS OWN", size=7.6, fill=INK, weight="bold", spacing="0.6"),
        text(x + 12, 43, "the return address kept in x15", size=7.8, fill=SLATE, style="italic"),
        rect(x + 14, 54, 184, 34, fill=IVORY, stroke=RULE, sw=0.75),
        text(x + 22, 68, "mov x15, x30   // save link", font=MONO, size=7.2, fill=INK),
        text(x + 22, 81, "values in use stay in registers", size=7.4, fill=SLATE),
        line(x + 106, 88, x + 106, 104, stroke=INK, sw=0.8, marker="arr-ink"),
        rect(x + 20, 106, 172, 34, fill=SAND, stroke=CHARCOAL, sw=0.85),
        text(x + 106, 120, "bl  helper   (preserves x15)", font=MONO, size=7.3, fill=INK, anchor="middle", weight="bold"),
        text(x + 106, 133, "in a=x9, b=x10  ·  out=x11", font=MONO, size=7.0, fill=SLATE, anchor="middle"),
        line(x + 106, 140, x + 106, 154, stroke=INK, sw=0.8, marker="arr-ink"),
        rect(x + 14, 156, 184, 28, fill=IVORY, stroke=RULE, sw=0.75),
        text(x + 106, 173, "mov x30, x15  ·  ret", font=MONO, size=7.4, fill=INK, anchor="middle"),
        text(x + 106, 200, "no stack frame", size=8.0, fill=INK, anchor="middle", weight="bold"),
    ]

    # Panel C: Verified Tail Call (calm sandstone ground + dark charcoal border)
    x = xs[2]
    parts += [
        rect(x, 12, pw, 200, fill=SAND, stroke=CHARCOAL, sw=1.0),
        text(x + 12, 30, "C.  A TAIL CALL  (jmp / b)", size=7.6, fill=INK, weight="bold", spacing="0.6"),
        text(x + 12, 43, "no call and no return of its own", size=7.8, fill=SLATE, style="italic"),
        rect(x + 14, 54, 184, 34, fill=WHITE, stroke=SLATE, sw=0.75),
        text(x + 22, 68, "sp == entry sp  &  x30 intact", font=MONO, size=7.2, fill=INK),
        text(x + 22, 81, "caller keeps ⊆ callee preserves", font=MONO, size=7.0, fill=SLATE),
        line(x + 106, 88, x + 106, 108, stroke=ACCENT, sw=0.95, marker="arr-accent"),
        text(x + 114, 102, "jmp / b", font=MONO, size=7.6, fill=ACCENT, weight="bold"),
        rect(x + 20, 110, 172, 40, fill=WHITE, stroke=CHARCOAL, sw=0.9),
        text(x + 106, 126, "callee entry point", font=MONO, size=7.8, fill=INK, anchor="middle", weight="bold"),
        text(x + 106, 141, "returns directly to outer caller", size=7.7, fill=SLATE, anchor="middle"),
        line(x + 106, 150, x + 106, 174, stroke=ACCENT, sw=0.9, marker="arr-accent"),
        text(x + 106, 186, "outer caller receives result directly", size=7.7, fill=INK, anchor="middle", style="italic"),
        text(x + 106, 202, "no stack frame, one return in all", size=8.0, fill=INK, anchor="middle", weight="bold"),
    ]
    (OUT / "fig4-calling.svg").write_text(svg_wrap(w, h, "\n".join(parts)))


def make_fig5():
    """Figure 5: Anatomy of a Packed & Audited ELF Object Bundle."""
    w, h = 680, 194
    parts = [
        # Left: ELF .o file cutaway
        rect(8, 12, 408, 170, fill=WHITE, stroke=CHARCOAL, sw=0.95),
        text(20, 30, "THE OBJECT FILE  (bundle.o)", size=8.0, fill=INK, weight="bold", spacing="1.0"),
        text(404, 30, "all of it checked by ode audit", size=7.8, fill=SLATE, anchor="end", style="italic"),

        # .text band
        rect(20, 42, 384, 52, fill=SAND, stroke=CHARCOAL, sw=0.9),
        text(30, 57, ".text", font=MONO, size=8.3, fill=INK, weight="bold"),
        text(70, 57, "every byte of code is in a function the verifier checked", size=8.0, fill=SLATE),
        rect(30, 64, 122, 22, fill=WHITE, stroke=CHARCOAL, sw=0.85),
        text(91, 78, "visible:  ode_<52>", font=MONO, size=7.2, fill=INK, anchor="middle", weight="bold"),
        rect(162, 64, 108, 22, fill=IVORY, stroke=SLATE, sw=0.7),
        text(216, 78, "local:  helper 1", font=MONO, size=7.0, fill=INK, anchor="middle"),
        rect(278, 64, 116, 22, fill=IVORY, stroke=SLATE, sw=0.7),
        text(336, 78, "local:  helper k", font=MONO, size=7.0, fill=INK, anchor="middle"),
        line(152, 75, 160, 75, stroke=ACCENT, sw=0.75, marker="arr-accent"),
        line(270, 75, 276, 75, stroke=SLATE, sw=0.75, marker="arr-slate"),

        # .rodata + .ode.ocl row
        rect(20, 102, 136, 36, fill=IVORY, stroke=RULE, sw=0.75),
        text(30, 117, ".rodata", font=MONO, size=8.0, fill=INK, weight="bold"),
        text(30, 130, "read-only data", size=7.6, fill=SLATE),

        rect(166, 102, 238, 36, fill=SAND, stroke=CHARCOAL, sw=0.85),
        text(176, 117, ".ode.ocl", font=MONO, size=8.0, fill=INK, weight="bold"),
        text(238, 117, "the canonical contract (not code)", size=7.6, fill=SLATE, style="italic"),
        text(176, 130, "its BLAKE3 hash is the symbol's <52>", font=MONO, size=7.0, fill=INK),

        # Forbidden sections bar
        rect(20, 146, 384, 24, fill=IVORY, stroke=RULE, sw=0.65, dash="2.5,2.5"),
        text(30, 162, "Refused if present:  code run at start or end · other visible symbols · symbols defined elsewhere", size=7.8, fill=SLATE),

        # Connecting arrow from .proof -> .o ("verifies")
        line(448, 98, 419, 98, stroke=ACCENT, sw=0.95, marker="arr-accent"),

        # Right: Separate .proof file
        rect(448, 12, 224, 170, fill=IVORY, stroke=SLATE, sw=0.8),
        text(460, 30, "THE PROOF FILE  (bundle.proof)", size=7.8, fill=INK, weight="bold", spacing="0.9"),
        text(460, 43, "checked step by step; relied on for nothing", size=7.6, fill=SLATE, style="italic"),

        rect(460, 54, 200, 36, fill=WHITE, stroke=RULE, sw=0.75),
        text(470, 68, "order:  helper 1, ..., ode_<52>", font=MONO, size=7.1, fill=INK),
        text(470, 81, "each function after those it calls", size=7.4, fill=SLATE, style="italic"),

        rect(460, 98, 200, 34, fill=WHITE, stroke=RULE, sw=0.75),
        text(470, 112, "contracts of the local functions", font=MONO, size=7.0, fill=INK),
        text(470, 124, "and how each takes its arguments", size=7.4, fill=SLATE, style="italic"),

        rect(460, 140, 200, 32, fill=WHITE, stroke=RULE, sw=0.75),
        text(470, 154, "the steps of each proof", font=MONO, size=7.0, fill=INK),
        text(470, 166, "checked against the bytes of code", size=7.4, fill=SLATE, style="italic"),
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
        text(lx0, 32, "Calls of Ode's own and tail calls count most at 64 bytes", size=7.9, fill=SLATE, style="italic"),
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

    # Clean horizontal key under left panel (high contrast, legible at print size)
    ky = 234
    items_l = [
        (14,  "#CFC9BC", SLATE,    "Ode, C calls inside"),
        (112, ACCENT,    ACCENT,   "Ode"),
        (146, "#3A3F47", "#3A3F47","BLAKE3-Servil"),
        (222, WHITE,     CHARCOAL, "blake3 1.8.7"),
    ]
    for ix, fl, st, lab in items_l:
        parts.append(rect(ix, ky - 7, 7.5, 7.5, fill=fl, stroke=st, sw=0.85, rx=0.5))
        parts.append(text(ix + 10.5, ky, lab, size=7.8, fill=ACCENT if fl == ACCENT else INK, weight="bold" if fl == ACCENT else "normal"))

    # ---- RIGHT PANEL: Full Sweep (4 KiB – 1 MiB) ----
    rx0, rx1 = 336, 594
    ry0, ry1 = 44, 202
    ymax_r = 18.0

    def ry(v):
        return ry1 - (v / ymax_r) * (ry1 - ry0)

    parts += [
        text(rx0, 20, "LARGE INPUTS  (4 KiB – 1 MiB)", size=8.2, fill=INK, weight="bold", spacing="0.8"),
        text(rx0, 33, "From 256 KiB on, Ode runs at 98 to 99% of BLAKE3-Servil's speed", size=7.9, fill=SLATE, style="italic"),
    ]
    for tick in (0, 4, 8, 12, 16):
        y = ry(tick)
        parts.append(line(rx0, y, rx1, y, stroke=RULE if tick > 0 else INK, sw=0.45 if tick > 0 else 0.7))
        parts.append(text(rx0 - 6, y + 3, f"{tick}", font=SERIF, size=8.0, fill=SLATE, anchor="end"))

    # Exact verified Zen 5 medians (4 KiB .. 1 MiB)
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
    parts.append(poly(3, SLATE, 1.05, dash="3.5,2.5"))
    parts.append(poly(2, "#3A3F47", 1.2))
    parts.append(poly(1, ACCENT, 1.85))

    for i, (lbl, ode_v, nxt, off) in enumerate(sweep):
        cx = xs_r[i]
        parts.append(f'  <circle cx="{cx:.1f}" cy="{ry(ode_v):.1f}" r="2.4" fill="{ACCENT}" stroke="{WHITE}" stroke-width="0.6"/>')
        parts.append(f'  <circle cx="{cx:.1f}" cy="{ry(nxt):.1f}" r="1.8" fill="#3A3F47"/>')
        parts.append(text(f"{cx:.1f}", ry1 + 14, lbl, font=SERIF, size=8.0, fill=INK, anchor="middle"))

    # Clean non-colliding direct end-of-line labels
    parts.append(text(rx1 + 8, ry(16.032) - 5, "BLAKE3-Servil 16.0", size=7.8, fill="#3A3F47"))
    parts.append(text(rx1 + 8, ry(15.851) + 9, "Ode  15.9", size=8.2, fill=ACCENT, weight="bold"))
    parts.append(text(rx1 + 8, ry(12.356) + 3, "blake3 1.8.7  12.4", size=7.8, fill=SLATE))

    # Pure architectural callout for mid sizes
    parts.append(line(xs_r[1] + 2, ry(6.299) + 3, xs_r[1] + 22, ry(3.3), stroke=SLATE, sw=0.65))
    parts.append(text(xs_r[1] + 25, ry(3.1), "4 to 32 KiB: BLAKE3-Servil has", size=7.8, fill=SLATE, style="italic"))
    parts.append(text(xs_r[1] + 25, ry(1.8), "kernels the Ode code does not", size=7.8, fill=SLATE, style="italic"))

    # Peak highlight at 256 KiB
    parts.append(text(f"{xs_r[5]:.1f}", ry(16.601) - 8, "16.34", size=8.0, fill=ACCENT, anchor="middle", weight="bold"))
    parts.append(text(rx0 - 6, ry(17.9), "GiB/s", size=7.8, fill=SLATE, anchor="end", style="italic"))

    # Bottom caption note
    parts.append(text(rx0, 234, "One Zen 5 core · medians of 45 interleaved trials a size", size=7.8, fill=SLATE, style="italic"))

    (OUT / "fig6-blake3-perf.svg").write_text(svg_wrap(w, h, "\n".join(parts)))


if __name__ == "__main__":
    make_fig1()
    make_fig2()
    make_fig3()
    make_fig4()
    make_fig5()
    make_fig6()
    print("Wrote 6 figures to", OUT)
