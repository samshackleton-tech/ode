#!/usr/bin/env pypy3
"""Regenerate the Ode Language Report vector figures and compile paper/ODE.pdf via Typst.

Usage:
    pypy3 paper/render-paper.py
    pypy3 paper/render-paper.py paper/ode.typ paper/ODE.pdf
"""
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent


def main() -> None:
    source = Path(sys.argv[1]) if len(sys.argv) >= 2 else HERE / "ode.typ"
    dest = Path(sys.argv[2]) if len(sys.argv) >= 3 else HERE / "ODE.pdf"

    # 1. Regenerate all six co-designed SVG figures deterministically.
    subprocess.run([sys.executable, str(HERE / "make_figures.py")], check=True)

    # 2. Compile the Typst monograph cleanly with zero warnings expected.
    subprocess.run(["typst", "compile", str(source), str(dest)], check=True)
    with dest.open("rb") as f:
        header = f.read(5)
    assert header == b"%PDF-", f"unexpected PDF header: {header!r}"
    print(f"Rendered {dest} ({dest.stat().st_size} bytes)")


if __name__ == "__main__":
    main()
