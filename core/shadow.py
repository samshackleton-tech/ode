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
import kfn, kterms
import sym, table

ROWS = {}
for row in table.read():
    t = row.row.split()
    if t[0].startswith(".x") and all(h in ("X", "Y", "Z", "I", "N", ".B", ".S") for h in t[1:]): ROWS[t[0]] = (row, t[1:])
COUNT = {"instructions": 0, "by the table": 0, "differ": 0}
SCALAR = [(kterms.parse(row.row), row) for row in table.read() if not row.row.startswith(".x")]
ARITH = {"add64": "add", "sub64": "sub", "and64": "and", "or64": "or", "shl64": "shl", "shr64": "shr"}


def unify(pat, ins, bind):
    if isinstance(pat, list): return isinstance(ins, list) and len(pat) == len(ins) and all(unify(p, x, bind) for p, x in zip(pat, ins))
    if not isinstance(ins, str): return False
    if pat in ("I", "N"): bind[pat] = ins; return True
    if pat in (".D", ".S", ".B"): bind[pat[1]] = ins.lstrip("."); return ins.startswith(".")
    return pat == ins


def scalar(row, bind, m):
    """What a row of 64-bit registers assigns, on m's symbolic state, with kfn.py's own rules for the arithmetic:
    {("g", register): value} and {("mem", base, disp): value}. Flags are not compared yet."""
    said = {}
    def value(e):
        if e[0] == "name":
            if e[1] in ("D", "S", "B"): return said.get(("g", bind[e[1]]), m.g[bind[e[1]]])
            if e[1] == "I": return ("n", kterms.num(bind["I"]) & table.M64)
            raise sym.Refuse(e[1])
        if e[0] == "call" and e[1] in ARITH: return m.arith(ARITH[e[1]], value(e[2][0]), value(e[2][1]))
        if e[0] == "call" and e[1] == "mem64": return m.load(*m.address("." + bind[e[2][0][1]], bind[e[2][1][1]]), 8)
        raise sym.Refuse(str(e))
    for lhs, rhs in row.effect:
        if rhs == ("name", "unknown"): continue
        if lhs[0] == "name" and lhs[1] in ("D", "S", "B"): said[("g", bind[lhs[1]])] = value(rhs)
        elif lhs[0] == "call" and lhs[1] == "mem64": said[("mem", bind[lhs[2][0][1]], bind[lhs[2][1][1]])] = value(rhs)
        else: raise sym.Refuse(str(lhs))
    return said


def effect(row, bind, m):
    """What the row assigns, on m's symbolic state: {vector register: lanes} and {("mem", base, disp): lanes}."""
    S = sym.rules(m.T)
    def mem(e): return m.address("." + bind[e[2][0][1]], bind[e[2][1][1]])
    def value(e):
        if e[0] == "number": return e[1]
        if e[0] == "lane": return m.halves(bind[e[1]])[e[2]]
        if e[0] == "name":
            if e[1] in S: return S[e[1]]
            if e[1] in ("S", "B"): return m.g[bind[e[1]]]
            return bind[e[1]] if e[1] == "I" else tuple(m.halves(bind[e[1]]))
        if e[1] == "mem128": return tuple(m.load(*mem(e), 16))
        return S[e[1]](*[value(a) for a in e[2]])
    return {(("mem",) + (bind[lhs[2][0][1]], bind[lhs[2][1][1]]) if lhs[0] == "call" else bind[lhs[1]]): tuple(value(rhs)) for lhs, rhs in row.effect}


def shadowed(one):
    def step(self):
        _, i = self.rows[self.pc]
        op, a = i[0], i[1:]
        said = None
        if op in ROWS and len(a) == len(ROWS[op][1]) and all(isinstance(t, str) for t in a):
            row, holders = ROWS[op]
            bind = {h.lstrip("."): (t.lstrip(".") if h.startswith(".") else t if h == "N" else int(t, 0)) for h, t in zip(holders, a)}
            try: said = effect(row, bind, self)
            except sym.Refuse: said = None
        elif isinstance(op, str) and not op.startswith(".x"):
            for pat, row in SCALAR:
                bind = {}
                if unify(pat, i, bind):
                    try: said = scalar(row, bind, self)
                    except (sym.Refuse, kterms.Fail, kfn.Fork): said = None     # no answer by the table here: kfn.py steps alone
                    break
        one(self)
        COUNT["instructions"] += 1
        if said is not None:
            COUNT["by the table"] += 1
            for r, lanes in said.items():
                if isinstance(r, tuple) and r[0] == "g": left = self.g[r[1]]
                elif isinstance(r, tuple) and not isinstance(lanes, tuple) or isinstance(r, tuple) and lanes and isinstance(lanes[0], str): left = self.load(*self.address("." + r[1], r[2]), 8)
                else: left = tuple(self.load(*self.address("." + r[1], r[2]), 16)) if isinstance(r, tuple) else tuple(self.x[r][:4])
                if left != lanes:
                    COUNT["differ"] += 1; print(f"DIFFERS at {op} {' '.join(a)}: {r}")
    return step


def main():
    name = sys.argv[1] if len(sys.argv) > 1 else "blake3_servil_compress_in_place_avx512"
    kfn.Machine.one = shadowed(kfn.Machine.one)
    os.chdir(KCHECK)
    sys.argv = ["check_binary.py", "b3hashr.o", name, "--spec", "blake3.spec", "--no-ends"] + (["--search"] if os.environ.get("SHADOW_SEARCH") else [])
    try: runpy.run_path("check_binary.py", run_name="__main__")
    except SystemExit as e: print("the verification's exit:", e.code)
    print(f"shadow: {COUNT['instructions']} instructions run by kfn.py, {COUNT['by the table']} of them also by the table, {COUNT['differ']} differ")
    sys.exit(1 if COUNT["differ"] else 0)


if __name__ == "__main__":
    main()
