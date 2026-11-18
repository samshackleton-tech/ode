#!/usr/bin/env python3
"""prove: the prover for the verifier in Lean (Core.lean). Relied on for nothing.

    python3 prove.py OBJECT SYMBOL SPEC PLACES OUT.statement OUT.proof

What is to be shown is written by statement.py (OUT.statement). The proof (OUT.proof) starts with the
places of PLACES and is then found by asking: the verifier is run, says what it needs next (`need …`), an
answer is added to the proof, and it is run again, until it says `shown`. The answers are found here:

    need entail / branch    a proof of arithmetic, by elimination (../kcheck/kprove.py's derive)
    need compare            which of lt, eq, gt has such a proof
    need spec               which use of a definition to open: each is tried
    a kept register refused the register is left out of the place's `keep`

What comes out is a proof the verifier accepts by itself: `odeverify ../core/x86.tab OUT.statement OUT.proof`."""
import os, re, subprocess, sys
from math import gcd
HERE = os.path.dirname(os.path.abspath(__file__))
KCHECK = os.path.join(HERE, "..", "kcheck")
sys.path.insert(0, KCHECK)
import kbyte, klin, kprove, varith
sys.path.insert(0, HERE)
from statement import sexp, statement

TABLE = os.path.join(HERE, "..", "core", "x86.tab")
EXE = os.path.join(HERE, ".lake", "build", "bin", "odeverify")
REGISTERS = ["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"]


def places(places_text, keep=None):
    """The places as the verifier reads them; `keep`: the registers each place might keep (None: all it does not name)."""
    out, named = [], []
    for raw in places_text.split("\n"):
        line = raw.split("//")[0].strip()
        if not line or line == "}": continue
        m = re.fullmatch(r"place \+(0x[0-9a-fA-F]+) \{", line)
        if m: out.append(f"place {int(m.group(1), 16)}"); named = []; continue
        m = re.fullmatch(r"name (\w+) = (\w+)", line)
        if m: out.append(f"name {m.group(1)} {m.group(2)}"); named.append(m.group(2)); continue
        if line.startswith("fact "): out.append("fact " + sexp(kbyte.expression(line[5:]))); continue
        if line.startswith("decreases "):
            out.append("keep " + " ".join(r for r in REGISTERS if r not in named and (keep is None or r in keep)))
            out.append("decreases " + sexp(kbyte.expression(line[10:]))); continue
        raise SystemExit(f"prove: a line of a place the verifier in Lean does not read yet: {line}")
    return out


def lin(numbers):
    k, cs = numbers[0], numbers[1:]
    return klin.Lin([(f"v{i:05d}", c) for i, c in enumerate(cs) if c], k)


def row_text(c, k):
    """A row ({name: multiple}, number) as the verifier writes it: the number, then the multiples, no zeros at the end."""
    top = max((int(n[1:]) for n, v in c.items() if v), default=-1)
    return " ".join([str(k)] + [str(c.get(f"v{i:05d}", 0)) for i in range(top + 1)])


def proof_text(proof):
    starts, steps = proof
    out = ["r " + row_text(c, k) for c, k in starts]
    rows = [(dict(c), k) for c, k in starts]
    for i, a, j, b in steps:
        g = 0
        for n in set(rows[i][0]) | set(rows[j][0]): g = gcd(g, abs(a * rows[i][0].get(n, 0) + b * rows[j][0].get(n, 0)))
        rows.append(varith.combine(rows[i], a, rows[j], b))
        out.append(f"s {i} {a} {j} {b} {max(g, 1)}")
    return out + ["q"]


def refutation(system):
    """A proof that the rows (each >= 0) cannot all hold, or None."""
    return kprove.derive(system, 600) or kprove.derive(system, 30000)


def negation(g): return klin.Lin([(n, -c) for n, c in g.c], -g.k - 1)


class Unkept(Exception): pass


class Prover:
    def __init__(self, statement_path, place_lines, out):
        self.statement, self.lines, self.out, self.runs = statement_path, place_lines, out, 0

    def ask(self, proof):
        with open(self.out, "w") as f: f.write("\n".join(self.lines + proof) + "\n")
        self.runs += 1
        return subprocess.run([EXE, TABLE, self.statement, self.out], capture_output=True, text=True).stdout

    def note(self, proof, said):
        if os.environ.get("PROVE_TRACE"): print(f"-- after {len(proof)} lines ({[l for l in proof if l.startswith('t ')][-6:]}): {said.splitlines()[0]}", file=sys.stderr)

    def solve(self, proof):
        """The proof extended until the verifier says shown; None if this way does not get there."""
        while True:
            said = self.ask(proof)
            if said.startswith("shown"): return proof
            m = re.search(r"at the place register (\d+) does not hold", said)
            if m: raise Unkept(int(m.group(1)))
            if not said.startswith("need "): self.last = said; self.note(proof, said); return None
            lines = said.split("\n")
            what = lines[0][5:]
            facts = [lin([int(x) for x in l.split()[1:]]) for l in lines if l.startswith("f ")]
            goals = [lin([int(x) for x in l.split()[1:]]) for l in lines if l.startswith("g ")]
            if what == "entail":
                p = refutation(facts + [negation(goals[0])])
                if p is None: self.last = said; self.note(proof, said + ' (no proof found)'); return None
                proof = proof + proof_text(p)
            elif what == "branch":
                p = refutation(facts)
                proof = proof + (["t live"] if p is None else ["t dead"] + proof_text(p))
            elif what == "compare":
                d = goals[0]
                if refutation(facts + [negation(d)]) and refutation(facts + [negation(-d)]): proof = proof + ["t eq"]
                elif refutation(facts + [d]): proof = proof + ["t lt"]
                elif refutation(facts + [-d]): proof = proof + ["t gt"]
                else: self.last = said; self.note(proof, said + ' (undecided)'); return None
            elif what == "spec":
                count = int([l for l in lines if l.startswith("c ")][0].split()[1])
                opened = int([l for l in lines if l.startswith("o ")][0].split()[1])
                if opened >= 3: return None
                for k in reversed(range(count)):
                    done = self.solve(proof + [f"t open {k}"])
                    if done is not None: return done
                return None
            else: raise SystemExit(f"prove: the verifier needs what this prover does not know: {said}")


def prove(obj, symbol, spec_text, places_text, statement_out, out):
    keep, runs = None, 0
    with open(statement_out, "w") as f: f.write("\n".join(statement(obj, symbol, spec_text)) + "\n")
    while True:
        p = Prover(statement_out, places(places_text, keep), out)
        p.last = ""
        try: proof = p.solve([])
        except Unkept as e:
            keep = [r for r in (keep if keep is not None else REGISTERS) if r != REGISTERS[e.args[0]]]
            runs += p.runs
            continue
        if proof is None: raise SystemExit(f"prove: no proof found. The verifier's last word:\n{p.last}")
        k = len(proof) - 1
        while k >= 0:                                  # a use of a definition opened to no purpose is taken out
            if proof[k].startswith("t open") and p.ask(proof[:k] + proof[k + 1:]).startswith("shown"): del proof[k]
            k -= 1
        with open(out, "w") as f: f.write("\n".join(p.lines + proof) + "\n")
        return runs + p.runs, len(proof)


if __name__ == "__main__":
    obj, symbol, spec, places_path, statement_out, out = sys.argv[1:]
    with open(spec) as f: spec_text = f.read()
    with open(places_path) as f: places_text = f.read()
    runs, items = prove(obj, symbol, spec_text, places_text, statement_out, out)
    print(f"{symbol}: shown; the proof has {items} lines, found in {runs} runs of the verifier; {os.path.getsize(out)} bytes in {out}")
