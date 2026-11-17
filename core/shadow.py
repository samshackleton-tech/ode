#!/usr/bin/env python3
"""shadow: the table beside today's verifier, on a real verification.

    python3 shadow.py [FUNCTION]       (default: the one-block AVX-512 kernel of ../kcheck/b3hashr.o)

kcheck's verifier (kfn.py) runs the function as it always does. Before each instruction that the table
has a row for (so far: the vector rows between registers), the row's EFFECT is worked out on the same
symbolic state with sym.py's rules; after the instruction, what the table said is compared with what
kfn.py's own code left. A difference is a fault in one of the two. This is the differential test that lets
the table take over an instruction at a time. Exit 1 on any difference."""
import os, runpy, sys
HERE = os.path.dirname(os.path.abspath(__file__))
KCHECK = os.path.join(HERE, "..", "kcheck")
sys.path.insert(0, KCHECK); sys.path.insert(0, HERE)
import kfn
import sym, table

ROWS = {}
for row in table.read():
    t = row.row.split()
    if t[0].startswith(".x") and all(h in ("X", "Y", "Z", "I") for h in t[1:]): ROWS[t[0]] = (row, t[1:])
COUNT = {"instructions": 0, "by the table": 0, "differ": 0}


def effect(row, bind, m):
    """The vector registers the row assigns, on m's symbolic state."""
    S = sym.rules(m.T)
    def value(e):
        if e[0] == "number": return e[1]
        if e[0] == "lane": return m.lanes(bind[e[1]])[e[2]]
        if e[0] == "name":
            if e[1] in S: return S[e[1]]
            return bind[e[1]] if e[1] == "I" else tuple(m.lanes(bind[e[1]]))
        return S[e[1]](*[value(a) for a in e[2]])
    return {bind[lhs[1]]: tuple(value(rhs)) for lhs, rhs in row.effect}


def shadowed(one):
    def step(self):
        _, i = self.rows[self.pc]
        op, a = i[0], i[1:]
        said = None
        if op in ROWS and len(a) == len(ROWS[op][1]) and all(isinstance(t, str) for t in a):
            row, holders = ROWS[op]
            said = effect(row, {h: int(t, 0) for h, t in zip(holders, a)}, self)
        one(self)
        COUNT["instructions"] += 1
        if said is not None:
            COUNT["by the table"] += 1
            for r, lanes in said.items():
                if tuple(self.x[r][:4]) != lanes:
                    COUNT["differ"] += 1; print(f"DIFFERS at {op} {' '.join(a)}: xmm{r}")
    return step


def main():
    name = sys.argv[1] if len(sys.argv) > 1 else "blake3_servil_compress_in_place_avx512"
    kfn.Machine.one = shadowed(kfn.Machine.one)
    os.chdir(KCHECK)
    sys.argv = ["check_binary.py", "b3hashr.o", name, "--spec", "blake3.spec", "--no-ends"]
    try: runpy.run_path("check_binary.py", run_name="__main__")
    except SystemExit as e: print("the verification's exit:", e.code)
    print(f"shadow: {COUNT['instructions']} instructions run by kfn.py, {COUNT['by the table']} of them also by the table, {COUNT['differ']} differ")
    sys.exit(1 if COUNT["differ"] else 0)


if __name__ == "__main__":
    main()
