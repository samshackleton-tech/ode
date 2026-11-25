#!/usr/bin/env pypy3
"""Make the language report: the facts, the figures, then paper/ODE.pdf with Typst.

    pypy3 paper/render-paper.py

The report's listings are read by Typst from the files the tests compile (paper/examples/ and two files
of proof-core/), so the repository's root is given to Typst as the root it may read from.
"""
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def main() -> None:
    source = HERE / "ode.typ"
    dest = HERE / "ODE.pdf"
    subprocess.run([sys.executable, str(HERE / "make_facts.py")], check=True)
    subprocess.run([sys.executable, str(HERE / "make_figures.py")], check=True)
    subprocess.run(["typst", "compile", "--root", str(ROOT), str(source), str(dest)], check=True)
    with dest.open("rb") as f:
        header = f.read(5)
    assert header == b"%PDF-", f"not a PDF: {header!r}"
    print(f"Rendered {dest.name} ({dest.stat().st_size} bytes)")


if __name__ == "__main__":
    main()
