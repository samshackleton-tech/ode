#!/usr/bin/env python3
"""prove: the prover for the verifier in Lean (Core.lean). Relied on for nothing.

    python3 prove.py SPEC OUT.statement OUT.proof OBJECT:SYMBOL[:PLACES] [OBJECT:SYMBOL[:PLACES] …]

What is to be shown is written by statement.py (OUT.statement). The proof (OUT.proof) has a part for each
function, a function after those it calls. A part starts with the places of PLACES (a file) and is then
found by asking: the verifier is run, says what it needs next (`need …`), an answer is added to the proof,
and it is run again, until it has no more to ask of that function. The answers are found here:

    need entail / branch    a proof of arithmetic, by elimination (../kcheck/kprove.py's derive)
    need compare            which of lt, eq, gt has such a proof
    need spec               which value held to carry over, or which use of a definition to open: each is tried
    need held               which value held is of a use with the same things: each is tried
    a kept register refused the register is left out of the place's `keep`

What comes out is a proof the verifier accepts by itself: `odeverify ../core/x86.tab OUT.statement OUT.proof`."""
import os, re, subprocess, sys, time
from math import gcd
HERE = os.path.dirname(os.path.abspath(__file__))
KCHECK = os.path.join(HERE, "..", "kcheck")
sys.path.insert(0, KCHECK)
import kbyte, klin, kprove, varith
sys.path.insert(0, HERE)
from statement import sexp, statement, ordered, sequences
import ode

TABLE = os.path.join(HERE, "..", "core", "x86.tab")
EXE = os.path.join(HERE, ".lake", "build", "bin", "odeverify")
REGISTERS = ["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"]


def places(places_text, keep={}, seqs={}):
    """The places as the verifier reads them; `keep`: for a place (by where it is), the registers it might keep
    (a place not in it: all it does not name); `seqs`: the specification's sequences (statement.sequences)."""
    out, named, also, at = [], [], [], None
    for raw in places_text.split("\n"):
        line = raw.split("//")[0].strip()
        if not line or line == "}": continue
        m = re.fullmatch(r"place \+(0x[0-9a-fA-F]+) \{", line)
        if m: at = int(m.group(1), 16); out.append(f"place {at}"); named, also = [], []; continue
        m = re.fullmatch(r"keep ((?:\w+ ?)+)", line)              # registers a place names and keeps all the same
        if m: also += m.group(1).split(); continue
        m = re.fullmatch(r"name (\w+) = (\w+)", line)
        if m: out.append(f"name {m.group(1)} {m.group(2)}"); named.append(m.group(2)); continue
        if line.startswith("fact "): out.append("fact " + sexp(kbyte.expression(line[5:]), seqs)); continue
        if line.startswith("decreases "):
            out.append("keep " + " ".join(r for r in REGISTERS if (r not in named or r in also) and r in keep.get(at, REGISTERS)))
            out.append("decreases " + sexp(kbyte.expression(line[10:]), seqs)); continue
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


def bearing(system, seed):
    """The rows that bear on the row at `seed`: those that share an unknown with it, and those that share one
    with these, and so on; in the order given."""
    names, chosen = set(n for n, _ in system[seed].c), {seed}
    while True:
        more = [k for k, f in enumerate(system) if k not in chosen and any(n in names for n, _ in f.c)]
        if not more: break
        chosen.update(more)
        for k in more: names.update(n for n, _ in system[k].c)
    return [f for k, f in enumerate(system) if k in chosen]


def near(system, seed, steps):
    """The rows within so many steps of the row at `seed`: a row is one step from a row it shares an unknown with."""
    names, chosen = set(n for n, _ in system[seed].c), {seed}
    for _ in range(steps):
        more = [k for k, f in enumerate(system) if k not in chosen and any(n in names for n, _ in f.c)]
        if not more: break
        chosen.update(more)
        for k in more: names.update(n for n, _ in system[k].c)
    return [f for k, f in enumerate(system) if k in chosen]


FOUND = {}                # (the rows, the seed) -> what was found: the same question comes again and again in a search


def refutation(system, seed=-1, quick=False):
    """A proof that the rows (each >= 0) cannot all hold, or None; `seed`: the row asked about (the goal's, or the
    newest fact). Elimination over all the rows first, in a small room. Then over the rows that bear on the one
    asked about: in the usual order; with the unknowns that some row multiplies (a quotient, in x = m * q + r)
    left for last, so that what is known of them as whole numbers is used (a row m * q + k >= 0 is rounded
    where it is made); and in a large room. `quick`: only the small room (for a question that, where its answer
    is yes, is a plain one: are two uses of a definition of the same things)."""
    if not system: return None
    key = (tuple(system), seed, quick)
    if key not in FOUND:
        found = kprove.derive(system, 600)
        if not found:
            rows = bearing(system, seed % len(system))
            if len(rows) < len(system): found = kprove.derive(rows, 600)
            if not found and not quick:
                for room in (30000, 300000):           # the rows near the one asked about, the quotients left for last
                    tried = None
                    for steps in (1, 2, 3, 4):
                        close = near(system, seed % len(system), steps)
                        if close == tried or len(close) == len(rows): break
                        tried = close
                        found = kprove.derive(close, room, last=frozenset(n for f in close for n, c in f.c if abs(c) > 1))
                        if found: break
                    if found: break
            if not found and not quick:
                multiplied = frozenset(n for f in rows for n, c in f.c if abs(c) > 1)
                if multiplied: found = kprove.derive(rows, 3000, last=multiplied)
            found = found or kprove.derive(rows, 30000)
        FOUND[key] = found
    return FOUND[key]


def negation(g): return klin.Lin([(n, -c) for n, c in g.c], -g.k - 1)


class Unkept(Exception): pass


class GaveUp(Exception): pass           # more runs of the verifier, or more time, than the prover was allowed


class Prover:
    """Finds the proof of one function. `head`: the proof's lines before what is to be found (the parts of the
    functions shown before, `for NAME`, the places); `later`: the names of the statement's functions after it."""
    def __init__(self, statement_path, head, out, later=(), budget=None, until=None):
        self.statement, self.lines, self.out, self.runs, self.later, self.budget = statement_path, head, out, 0, set(later), budget
        self.until = until                  # the time (time.time()) after which the search gives up

    def finished(self, said):
        """The verifier has no more to ask of this function: all is shown, or it speaks of a later function."""
        if said.startswith("shown"): return True
        m = re.search(r"^in (\S+)$", said, re.M)
        return bool(m) and m.group(1) in self.later

    def ask(self, proof):
        if self.budget is not None and self.runs >= self.budget: raise GaveUp(self.runs)
        if self.until is not None and time.time() > self.until: raise GaveUp(self.runs)
        with open(self.out, "w") as f: f.write("\n".join(self.lines + proof) + "\n")
        self.runs += 1
        return subprocess.run([EXE, TABLE, self.statement, self.out], capture_output=True, text=True).stdout

    def note(self, proof, said):
        if os.environ.get("PROVE_TRACE"): print(f"-- after {len(proof)} lines ({[l for l in proof if l.startswith('t ')][-6:]}): {said.splitlines()[0]}", file=sys.stderr)

    def solve(self, proof):
        """The proof extended until the verifier says shown; None if this way does not get there."""
        while True:
            said = self.ask(proof)
            if self.finished(said): return proof
            m = re.search(r"at the place (\d+) register (\d+) does not hold", said)
            if m: raise Unkept(int(m.group(1)), int(m.group(2)))
            if not said.startswith("need "): self.last = said; self.note(proof, said); return None
            lines = said.split("\n")
            what = lines[0][5:]
            facts = [lin([int(x) for x in l.split()[1:]]) for l in lines if l.startswith("f ")]
            goals = [lin([int(x) for x in l.split()[1:]]) for l in lines if l.startswith("g ")]
            if what in ("entail", "same"):                  # (same: are two uses of a definition of the same things)
                p = refutation(facts + [negation(goals[0])], quick=what == "same")
                if p is None: self.last = said; self.note(proof, said + ' (no proof found)'); return None
                proof = proof + proof_text(p)
            elif what == "branch":
                p = refutation(facts, 0)                       # (the newest fact is first)
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
                held = int(([l for l in lines if l.startswith("h ")] or ["h 0"])[0].split()[1])
                before = self.last
                for k in reversed(range(held)):                # a value held, carried over to the fact asked for
                    done = self.solve(proof + [f"t carry {k}"])
                    if done is not None: return done
                self.last = before or said                     # (a value that does not carry over is not why no proof is found)
                if opened >= 3: return None
                for k in reversed(range(count)):
                    done = self.solve(proof + [f"t open {k}"])
                    if done is not None: return done
                return None
            elif what == "held":                               # which value held is of a use with the same things
                count = int([l for l in lines if l.startswith("c ")][0].split()[1])
                for k in reversed(range(count)):
                    done = self.solve(proof + [f"t held {k}"])
                    if done is not None: return done
                self.last = said; self.note(proof, said + ' (no value held fits)')
                return None
            else: raise SystemExit(f"prove: the verifier needs what this prover does not know: {said}")


def prove(spec_text, targets, statement_out, out):
    """targets: [(object, symbol, the text of its places)]. Writes the statement and the proof; gives
    {symbol: (runs of the verifier, lines found)}."""
    functions = ordered([(obj, symbol) for obj, symbol, _ in targets])
    places_of = {symbol: text for _, symbol, text in targets}
    seqs = sequences(ode.Spec(spec_text))
    with open(statement_out, "w") as f: f.write("\n".join(statement(spec_text, functions)) + "\n")
    done, numbers = [], {}
    for at, (obj, symbol) in enumerate(functions):
        later = [s for _, s in functions[at + 1:]]
        keep, runs = {}, 0
        while True:
            p = Prover(statement_out, done + [f"for {symbol}"] + places(places_of[symbol], keep, seqs), out, later)
            p.last = ""
            try: proof = p.solve([])
            except Unkept as e:
                keep[e.args[0]] = [r for r in keep.get(e.args[0], REGISTERS) if r != REGISTERS[e.args[1]]]
                runs += p.runs
                continue
            if proof is None: raise SystemExit(f"prove: no proof of {symbol} found. The verifier's last word:\n{p.last}")
            k = len(proof) - 1
            while k >= 0:                              # a use of a definition opened to no purpose is taken out
                if proof[k].startswith("t open") and p.finished(p.ask(proof[:k] + proof[k + 1:])): del proof[k]
                k -= 1
            done = p.lines + proof
            numbers[symbol] = (runs + p.runs, len(proof))
            break
    with open(out, "w") as f: f.write("\n".join(done) + "\n")
    return numbers


if __name__ == "__main__":
    if len(sys.argv) < 5: raise SystemExit(__doc__)
    spec, statement_out, out = sys.argv[1:4]
    targets = []
    for w in sys.argv[4:]:
        parts = w.split(":")
        if len(parts) not in (2, 3): raise SystemExit(f"prove: {w}: write OBJECT:SYMBOL or OBJECT:SYMBOL:PLACES")
        text = ""
        if len(parts) == 3:
            with open(parts[2]) as f: text = f.read()
        targets.append((parts[0], parts[1], text))
    with open(spec) as f: spec_text = f.read()
    numbers = prove(spec_text, targets, statement_out, out)
    for symbol, (runs, items) in numbers.items(): print(f"{symbol}: its part of the proof has {items} lines, found in {runs} runs of the verifier")
    print(f"shown: {', '.join(numbers)}; the proof: {os.path.getsize(out)} bytes in {out}")
