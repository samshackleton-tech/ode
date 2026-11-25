#!/usr/bin/env pypy3
"""Work out, from the repository itself, the numbers that the language report prints, into paper/facts.json.

The report (paper/ode.typ) reads that file, so that no such number is typed into its text by hand:
the identifier and length of the example's canonical contract, the rows of the two instruction tables,
and the lines of the Lean files. paper/test_paper.py fails where facts.json is not what this gives.

    pypy3 paper/make_facts.py           writes paper/facts.json
"""
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
for d in ("core", "arm64", "paper"):
    if str(ROOT / d) not in sys.path:
        sys.path.insert(0, str(ROOT / d))

# The Lean files that say what the machine does, what a contract means, and what the verifier accepts.
MODEL = ["Machine", "Contract", "Trace", "Plain", "Reader", "Table", "Arithmetic", "Core"]


def count_lines(path):
    with open(path, "r", encoding="utf-8") as f:
        return sum(1 for _ in f)


def facts():
    import make_figures
    import table
    import word

    _, canon = make_figures.all_zero_example()
    x86_rows = table.read(str(ROOT / "core" / "x86.tab"))
    arm_rows = table.read(word.TABLE)
    pc = ROOT / "proof-core"
    sound = sorted(p.name for p in pc.glob("Sound*.lean"))
    return {
        "all_zero": {
            "id": canon["contract_id"],
            "canonical_lines": len(canon["canonical"].rstrip("\n").split("\n")),
        },
        "tables": {
            "x86_rows": len(x86_rows),
            "x86_rows_run_on_a_processor": sum(1 for r in x86_rows if r.asm != "-"),
            "arm64_rows": len(arm_rows),
            "arm64_rows_run_on_a_processor": sum(1 for r in arm_rows if r.asm != "-"),
        },
        "lean": {
            "core_lines": count_lines(pc / "Core.lean"),
            "model_files": len(MODEL),
            "model_lines": sum(count_lines(pc / f"{m}.lean") for m in MODEL),
            "sound_files": len(sound),
            "sound_lines": sum(count_lines(pc / s) for s in sound),
        },
    }


if __name__ == "__main__":
    out = HERE / "facts.json"
    with open(out, "w", encoding="utf-8") as f:
        json.dump(facts(), f, indent=2, sort_keys=True)
        f.write("\n")
    print("Wrote", out)
