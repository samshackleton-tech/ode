#!/usr/bin/env pypy3
"""Cold-room visual and prose editor for rendered PDF pages.

Sends ONLY the rendered PNG pages of a document (zero chat history, zero session
notes, zero source drafts) to a fresh multimodal frontier model prompted in the
editorial tradition of Brian Kernighan, William Zinsser, and Edward Tufte.

Usage:
    pypy3 paper/cold_edit.py paper/ODE.pdf [--model anthropic/claude-sonnet-5.5] [--out report.md]
"""
import argparse
import base64
import json
import os
import subprocess
import sys
import tempfile
import urllib.request
from pathlib import Path

SYSTEM_PROMPT = """\
You are an independent, world-class technical editor and book designer—combining the
editorial instincts of Brian Kernighan (ruthless technical clarity, concrete examples
first, zero unnecessary mechanism), William Zinsser (On Writing Well: stripping clutter,
defensive asides, and author-centered prose), and Edward Tufte / Robert Bringhurst
(calm visual hierarchy, generous spacing, high data-ink ratio, unified word-and-image
composition).

You have NEVER seen this project before. You have no chat history, no author notes,
and no knowledge of earlier drafts. You are seeing ONLY the rendered pages of this
monograph exactly as a bright first-time systems programmer or security auditor sees them.

Evaluate ALL rendered pages together and give a concrete, page-by-page editorial and
visual critique across five axes:
1. VISUAL & TYPOGRAPHIC CRAFT: Check every page for cramped or uneven spacing (headings,
   paragraphs, tables, code blocks, captions), awkward line breaks or page breaks,
   running header/footer glitches, visual clutter, alarming/distracting boxes or colors,
   and diagram clarity/alignment.
2. LEAKED AUTHOR HISTORY & UNMOTIVATED CONTRASTS: Flag EVERY phrase, aside, margin note,
   or contrast ("instead of X", "never Y", "no longer Z", temporal words like "today"
   or "now", or project-internal milestone jargon) that feels like an inside reference,
   a reply to an unseen past argument, or scaffolding left behind from earlier drafts.
   Quote the exact phrase and state the naive reader's question ("What is X? Why tell me?").
3. MOTIVATION FIRST: Flag any section, subsection, or mechanism that jumps into syntax,
   rules, or tables before explaining WHY the mechanism exists and what problem it solves.
4. CLARITY, PRECISION & UNEXPLAINED TERMS: Flag any undefined acronym/jargon, ambiguous
   phrasing, unintended pun, or discrepancy between text, figures, and tables.
5. OVERALL VERDICT & TOP 5 HIGHEST-LEVERAGE IMPROVEMENTS: End with a sharp prioritized
   list of the 5 edits that would elevate this monograph the most.

Be direct, honest, and specific—cite exact page numbers and exact quoted phrases. Do not
pad with empty praise; focus on real defects and concrete fixes.\
"""


def load_openrouter_key() -> str:
    key = os.environ.get("OPENROUTER_API_KEY")
    if key:
        return key.strip()
    auth_path = Path.home() / ".pi" / "agent" / "auth.json"
    if auth_path.exists():
        with auth_path.open("r", encoding="utf-8") as f:
            data = json.load(f)
        ent = data.get("openrouter")
        if isinstance(ent, dict) and ent.get("key"):
            return str(ent["key"]).strip()
        if isinstance(ent, str) and ent:
            return ent.strip()
    raise RuntimeError("No OpenRouter API key found in OPENROUTER_API_KEY or ~/.pi/agent/auth.json")


def render_pdf_to_pngs(pdf_path: Path, out_dir: Path, dpi: int = 120) -> list[Path]:
    prefix = out_dir / "page"
    subprocess.run(
        ["pdftoppm", "-png", "-r", str(dpi), str(pdf_path), str(prefix)],
        check=True,
    )
    return sorted(out_dir.glob("page-*.png"))


def call_cold_editor(png_paths: list[Path], model: str, api_key: str, max_tokens: int = 24000, effort: str = "medium") -> tuple[str, dict]:
    content = [
        {
            "type": "text",
            "text": (
                f"Attached are all {len(png_paths)} rendered pages (pages 1 through {len(png_paths)}) "
                "of the monograph in order. Perform your complete cold-room visual and editorial review."
            ),
        }
    ]
    for idx, p in enumerate(png_paths, 1):
        with p.open("rb") as f:
            b64 = base64.b64encode(f.read()).decode("ascii")
        content.append({"type": "text", "text": f"--- Page {idx} ---"})
        content.append({"type": "image_url", "image_url": {"url": f"data:image/png;base64,{b64}"}})

    payload = {
        "model": model,
        "temperature": 0.2,
        "max_tokens": max_tokens,
        "reasoning": {"effort": effort},
        "messages": [
            {"role": "system", "content": SYSTEM_PROMPT},
            {"role": "user", "content": content},
        ],
    }
    req = urllib.request.Request(
        "https://openrouter.ai/api/v1/chat/completions",
        data=json.dumps(payload).encode("utf-8"),
        headers={
            "Authorization": f"Bearer {api_key}",
            "Content-Type": "application/json",
            "HTTP-Referer": "https://github.com/samshackleton-tech/ode",
            "X-Title": "Ode Cold-Room Editor",
        },
        method="POST",
    )
    with urllib.request.urlopen(req, timeout=220) as resp:
        data = json.loads(resp.read().decode("utf-8"))
    msg = data["choices"][0]["message"]
    reply = (msg.get("content") or "").strip()
    if not reply:
        raise RuntimeError(f"Empty reply content (usage={data.get('usage')}, finish_reason={data['choices'][0].get('finish_reason')})")
    usage = data.get("usage", {})
    return reply, usage


def main() -> None:
    ap = argparse.ArgumentParser(description="Cold-room visual + editorial review of rendered PDF pages")
    ap.add_argument("pdf", type=Path, help="Path to rendered PDF file")
    ap.add_argument("--model", default="anthropic/claude-sonnet-5.5", help="OpenRouter multimodal model")
    ap.add_argument("--dpi", type=int, default=120, help="PNG render DPI (default 120)")
    ap.add_argument("--max-tokens", type=int, default=24000, help="Completion + reasoning token cap (default 24000)")
    ap.add_argument("--effort", default="medium", help="Reasoning effort (low/medium/high)")
    ap.add_argument("--out", type=Path, default=None, help="Optional output markdown report path")
    args = ap.parse_args()

    api_key = load_openrouter_key()
    with tempfile.TemporaryDirectory() as td:
        pngs = render_pdf_to_pngs(args.pdf, Path(td), dpi=args.dpi)
        assert pngs, f"No PNGs rendered from {args.pdf}"
        print(f"Sending {len(pngs)} rendered pages ({args.dpi} DPI) to cold-room editor ({args.model})...", flush=True)
        reply, usage = call_cold_editor(pngs, args.model, api_key, max_tokens=args.max_tokens, effort=args.effort)
    print(f"Usage: {json.dumps(usage)}", flush=True)
    if args.out is not None:
        with args.out.open("w", encoding="utf-8") as f:
            f.write(reply + "\n")
        print(f"Saved report to {args.out}")
    print("\n" + reply)


if __name__ == "__main__":
    main()
