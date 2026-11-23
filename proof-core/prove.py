#!/usr/bin/env python3
"""prove: the prover for the verifier in Lean (Core.lean). Relied on for nothing.

    python3 prove.py SPEC OUT.statement OUT.proof OBJECT:SYMBOL[:PLACES] [OBJECT:SYMBOL[:PLACES] …]

What is to be shown is written by statement.py (OUT.statement). The proof (OUT.proof) has a part for each
function, a function after those it calls. A part starts with the places of PLACES (a file: for a source
that has its places written at its loops, `python3 ../lang/odec.py SOURCE NAME --places` prints it) and is then
found a line at a time: the verifier's rules are run on the lines so far; where those lines run out, the run
says which kind of line the proof lacks next (`need …`); such a line is found here and added; and so on,
until that function's part lacks nothing. How each kind of line is found:

    need entail / branch    a proof of arithmetic, by elimination (../kcheck/kprove.py's derive)
    need compare            which of lt, eq, gt has such a proof
    need shift              exact, where the number shifted to the left is shown to lose no bit, else wrap
    need below              which of lt, ge has such a proof
    need know               a row to give the verifier before an `ensures` of a run of words or before a call:
                            the first of the rows proposed that has such a proof (only `odeprove` proposes
                            rows: the advice is no part of the verifier)
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
from statement import sexp, statement, ordered, sequences, kinds_of, by_kind
import built, ode, session

TABLE = os.path.join(HERE, "..", "core", "x86.tab")
EXE = os.path.join(HERE, ".lake", "build", "bin", "odeverify")
FROM_THE_START = bool(os.environ.get("ODE_PROVE_FROM_START"))     # ask `odeverify` each time (the slow way, to compare with)
REGISTERS = ["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"]


def lane_line(var, regs, use, after, seqs, kinds, counted, name):
    """`lane I: zmmA .. zmmB = SEQUENCE(things) after K`, a line of a place, as the verifier reads it: in each
    lane I (0 to 15) the words of the vector registers, in their order, are the value of the counted sequence
    after K of its steps. That value is the use of the definition SEQUENCE.STATE the sequence is written as
    (statement.machine_lines), with K for its place. `kinds`: what the names of the function's contract stand
    for (statement.kinds_of); `counted`: {a counted sequence's name: the name of its state}."""
    rs = []
    for part in regs.split(","):
        m = re.fullmatch(r"\s*zmm(\d+)(?:\s*\.\.\s*zmm(\d+))?\s*", part)
        if not m: raise SystemExit(f"prove: a place's lanes are of vector registers zmmA, or zmmA .. zmmB: {part.strip()!r}")
        a, b = int(m.group(1)), int(m.group(2) or m.group(1))
        if not a <= b < 32: raise SystemExit(f"prove: no such vector registers: {part.strip()!r}")
        rs += range(a, b + 1)
    e, k = kbyte.expression(use), kbyte.expression(after)
    if e[0] != "call" or e[1] not in counted: raise SystemExit(f"prove: a place's lanes are said by a sequence with a count: {use!r}")
    if var in kinds: raise SystemExit(f"prove: a place's lanes count by a name the contract gives: {var}")
    full = ("call", f"{e[1]}.{counted[e[1]]}", [by_kind(a, kinds, name) for a in e[2]] + [by_kind(k, kinds, name)])
    return f"lane {var} " + " ".join(f"zmm{r}" for r in rs) + " = " + sexp(full, seqs)


def of_kinds(e, line, kinds, name):
    """A place's fact with each name of the contract that stands for something other than a register's number
    replaced by what it stands for (statement.by_kind), where the fact has such a name."""
    return by_kind(e, kinds, name) if any(re.search(rf"\b{re.escape(k)}\b", line) for k in kinds) else e


def cell_line(off, var, word, seqs, kinds, name):
    """`cell [rsp + N]: word I = E`, a line of a place, as the verifier reads it: of the sixty-four bytes that
    lie N bytes above the stack pointer (a cell of the frame that a vector was stored to), word I (0 to 15) is
    the word E of the specification, in which I is the word's number."""
    if var in kinds: raise SystemExit(f"prove: a place's cell counts its words by a name the contract gives: {var}")
    return f"cell {int(off)} {var} " + sexp(by_kind(kbyte.expression(word), kinds, name), seqs)


def places(places_text, keep={}, seqs={}, kinds={}, counted={}, name="", marked={}):
    """The places as the verifier reads them; `keep`: for a place (by where it is), the registers it might keep
    (a place not in it: all it does not name); `seqs`: the specification's sequences (statement.sequences);
    `kinds`, `counted`, `name`: for a line of lanes (lane_line)."""
    out, named, also, lanes, at = [], [], [], [], None
    for raw in places_text.split("\n"):
        line = raw.split("//")[0].strip()
        if not line or line == "}": continue
        m = re.fullmatch(r"place \+(0x[0-9a-fA-F]+) \{", line)
        if m: at = int(m.group(1), 16); out.append(f"place {at}"); named, also, lanes = [], [], []; continue
        m = re.fullmatch(r"keep ((?:\w+ ?)+)", line)              # registers a place names and keeps all the same
        if m: also += m.group(1).split(); continue
        m = re.fullmatch(r"name (\w+) = (\w+)", line)
        if m: out.append(f"name {m.group(1)} {m.group(2)}"); named.append(m.group(2)); continue
        if line.startswith("fact "): out.append("fact " + sexp(of_kinds(kbyte.expression(line[5:]), line, kinds, name), seqs)); continue
        m = re.fullmatch(r"wrote (\w+)\[(.+) \.\.\] = (.+)", line)       # from that place on, the run holds that list, place by place
        if m: lanes.append(f"wrote {m.group(1)} (index {sexp(kbyte.expression(m.group(3)), seqs)} {sexp(kbyte.expression(m.group(2)), seqs)})"); continue
        m = re.fullmatch(r"lane (\w+): (.+?) = (.+) after (.+)", line)
        if m: lanes.append(lane_line(*m.groups(), seqs, kinds, counted, name)); continue
        m = re.fullmatch(r"cell \[rsp \+ (\d+)\]: word (\w+) = (.+)", line)
        if m: lanes.append(cell_line(*m.groups(), seqs, kinds, name)); continue
        if line.startswith("decreases "):
            out.append("keep " + " ".join(r for r in REGISTERS if (r not in named or r in also) and r in keep.get(at, REGISTERS)))
            if marked.get(at): out.append("marked " + " ".join(marked[at]))      # registers that may depend on a secret on a later coming there
            out.append("decreases " + sexp(kbyte.expression(line[10:]), seqs))
            out += lanes; continue
        raise SystemExit(f"prove: a line of a place the verifier in Lean does not read yet: {line}")
    return out


def lin(numbers):
    k, cs = numbers[0], numbers[1:]
    return klin.Lin([(f"v{i:05d}", c) for i, c in enumerate(cs) if c], k)


def row_text(c, k):
    """A row ({name: multiple}, number) as the verifier writes it: the number, then the multiples, no zeros at the end."""
    top = max((int(n[1:]) for n, v in c.items() if v), default=-1)
    return " ".join([str(k)] + [str(c.get(f"v{i:05d}", 0)) for i in range(top + 1)])


def proof_text(proof, given):
    """A proof of arithmetic as the verifier reads it: the rows it starts from by their numbers among the rows
    the verifier holds (`given`, in its order), then the steps."""
    starts, steps = proof
    at = {}
    for number, f in enumerate(given): at.setdefault((frozenset(dict(f.c).items()), f.k), number)
    out = ["p " + " ".join(str(at[(frozenset((n, v) for n, v in c.items() if v), k)]) for c, k in starts)]
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


def derive_eq(system, limit=30000, last=frozenset()):
    """As kprove.derive (a proof that the rows cannot all hold, or None), with the equalities used first. An
    equality is a row given together with its opposite. Where it has an unknown once (multiple 1 or -1) that
    no row multiplies (`last`: the unknowns some row multiplies), that unknown is put out of every other row
    by adding the equality to it, so many times; the rows stay as many as they were. What is left goes by
    elimination, the multiplied unknowns last."""
    norm = klin.Facts.norm
    how, live = {}, []
    for f in system:
        if f not in how: how[f] = None; live.append(f)
    def done(final):
        index = {}
        def visit(f):
            if f in index: return
            h = how[f]
            if h is not None: visit(h[0]); visit(h[2])
            index[f] = None
        visit(final)
        used = list(index)
        starts = [f for f in used if how[f] is None]
        if system[-1] in starts: starts.remove(system[-1])
        starts.append(system[-1])
        for k, f in enumerate(starts): index[f] = k
        steps = []
        for f in used:
            if how[f] is not None:
                p, a, q, b = how[f]; index[f] = len(starts) + len(steps); steps.append((index[p], a, index[q], b))
        if how[final] is None: k = starts.index(final); steps.append((k, 1, k, 1))
        return [kprove.row(f) for f in starts], steps
    for f in live:
        if not f.c and f.k < 0: return done(f)
    rows = [f for f in live if f.c]
    again = True
    while again:
        again = False
        have = set(rows)
        for p in rows:
            n = -p
            if n not in have: continue
            once = [s for s, a in p.c if abs(a) == 1 and s not in last]
            if not once: continue
            s = once[0]
            up, down = (p, n) if dict(p.c)[s] > 0 else (n, p)          # up: +s ...; down: -s ...
            new = []
            for r in rows:
                if r is p or r is n or r == p or r == n: continue
                b = dict(r.c).get(s, 0)
                if b:
                    e = down if b > 0 else up
                    made = norm(r + e.scale(abs(b)))
                    if made not in how: how[made] = (r, 1, e, abs(b))
                    if not made.c:
                        if made.k < 0: return done(made)
                        continue
                    r = made
                new.append(r)
            rows, again = list(dict.fromkeys(new)), True
            break
    rows = dict.fromkeys(rows)
    while rows:
        count = {}
        for f in rows:
            for s, a in f.c:
                p = count.setdefault(s, [0, 0]); p[0 if a > 0 else 1] += 1
        s = min(count, key=lambda s: (s in last, count[s][0] * count[s][1], s))
        rows, pos, neg = kprove.split_rows(rows, s)
        if len(rows) + len(pos) * len(neg) > limit: return None
        for p, a in pos:
            for n, b in neg:
                g = gcd(a, b)
                r = norm(p.scale(b // g) + n.scale(a // g))
                if r not in how: how[r] = (p, b // g, n, a // g)
                if not r.c:
                    if r.k < 0: return done(r)
                else: rows[r] = None
    return None


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
            if not found and not quick:                # the equalities first, on the rows near the one asked about
                tried = None
                for steps in (2, 3, 4, 6):
                    close = near(system, seed % len(system), steps)
                    if close == tried: break
                    tried = close
                    found = derive_eq(close, 30000, last=frozenset(n for f in close for n, c in f.c if abs(c) > 1))
                    if found: break
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


class Marked(Exception): pass           # at a place, a register may depend on a secret that did not on first coming there


class GaveUp(Exception): pass           # more runs of the verifier, or more time, than the prover was allowed


class Prover:
    """Finds the proof of one function. `head`: the proof's lines before what is to be found (the parts of the
    functions shown before, `for NAME`, the places); `later`: the names of the statement's functions after it."""
    def __init__(self, statement_path, head, out, later=(), budget=None, until=None):
        self.statement, self.lines, self.out, self.runs, self.later, self.budget = statement_path, head, out, 0, set(later), budget
        self.until = until                  # the time (time.time()) after which the search gives up
        self.session = None                 # the talk with `odeprove`, begun at the first question

    def close(self):
        if self.session is not None: self.session.close(); self.session = None

    def __del__(self): self.close()

    def finished(self, said):
        """The verifier has no more to ask of this function: all is shown, or it speaks of a later function."""
        if said.startswith("shown"): return True
        m = re.search(r"^in (\S+)$", said, re.M)
        return bool(m) and m.group(1) in self.later

    def ask(self, proof):
        if self.budget is not None and self.runs >= self.budget: raise GaveUp(self.runs)
        if self.until is not None and time.time() > self.until: raise GaveUp(self.runs)
        self.runs += 1
        if FROM_THE_START or not os.path.exists(session.EXE):
            # the verifier itself, from the proof's first line each time
            with open(self.out, "w") as f: f.write("\n".join(self.lines + proof) + "\n")
            return subprocess.run([EXE, TABLE, self.statement, self.out], capture_output=True, text=True).stdout
        # `odeprove` says what the verifier would say, and goes only through the lines that are new (session.py)
        if self.session is None:
            names = [l.split()[1] for l in self.lines if l.split()[:1] == ["for"]]
            if not names: raise SystemExit("prove: the lines before the proof name no function (`for NAME`)")
            self.session = session.Session(self.statement, self.lines, names[-1])
        return self.session.ask(proof)

    def note(self, proof, said):
        if os.environ.get("PROVE_TRACE"): print(f"-- after {len(proof)} lines ({[l for l in proof if l.startswith('t ')][-6:]}): {said.splitlines()[0]}", file=sys.stderr)

    def solve(self, proof):
        """The proof extended until the verifier says shown; None if this way does not get there."""
        while True:
            said = self.ask(proof)
            if self.finished(said): return proof
            m = re.search(r"at the place (\d+) register (\d+) does not hold", said)
            if m: raise Unkept(int(m.group(1)), int(m.group(2)))
            m = re.search(r"at the place (\d+) register (\d+) may depend on a secret", said)
            if m: raise Marked(int(m.group(1)), int(m.group(2)))
            if not said.startswith("need "): self.last = said; self.note(proof, said); return None
            lines = said.split("\n")
            what = lines[0][5:]
            facts = [lin([int(x) for x in l.split()[1:]]) for l in lines if l.startswith("f ")]
            goals = [lin([int(x) for x in l.split()[1:]]) for l in lines if l.startswith("g ")]
            if what in ("entail", "same"):                  # (same: are two uses of a definition of the same things)
                p = refutation(facts + [negation(goals[0])], quick=what == "same")
                if p is None: self.last = said; self.note(proof, said + ' (no proof found)'); return None
                proof = proof + proof_text(p, [negation(goals[0])] + facts)
            elif what == "branch":
                p = refutation(facts, 0)                       # (the newest fact is first)
                proof = proof + (["t live"] if p is None else ["t dead"] + proof_text(p, facts))
            elif what == "below":                              # is a - b below zero: `lt`, or not: `ge`
                d = goals[0]
                if refutation(facts + [d]): proof = proof + ["t lt"]
                elif refutation(facts + [negation(d)]): proof = proof + ["t ge"]
                else: self.last = said; self.note(proof, said + ' (undecided)'); return None
            elif what == "know":                               # rows of which one may be worth giving here: the first that has a proof
                rows, given, found = [l[2:] for l in lines if l.startswith("g ")], [l for l in lines if l.startswith("f ")], None
                for g, row in zip(goals, rows):
                    if not g.c or any(f.c == g.c and f.k <= g.k for f in facts): continue        # (a fact says it at once)
                    if refutation(facts + [negation(g)]) is None: continue
                    # The verifier takes rows at the first point it comes to after the lines so far, which may be
                    # an earlier one than the point that lacks the row (a call before the return, where the call
                    # lacks nothing). `t next` ends the rows of a point: as many as put the row where it is
                    # lacked, which is where the verifier then needs the row's proof from these same facts.
                    for passed in range(9):
                        trial = proof + ["t next"] * passed + ["k " + row]
                        answer = self.ask(trial).split("\n")
                        if answer[0] == "need entail" and "g " + row in answer and [l for l in answer if l.startswith("f ")] == given:
                            found = trial
                            break
                    break
                if found is None: self.last = said; self.note(proof, said + ' (none of the rows has a proof)'); return None
                proof = found
            elif what == "shift":                              # a shift to the left: is the number shown to lose no bit, or is only its low part kept
                proof = proof + (["t exact"] if refutation(facts + [negation(goals[0])]) else ["t wrap"])
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
                done = self.solve(proof + ["t open"])           # no value held fits: the use is opened where it is met
                if done is not None: return done
                self.last = said; self.note(proof, said + ' (no value held fits, and opening the use does not do)')
                return None
            else: raise SystemExit(f"prove: the verifier needs what this prover does not know: {said}")


def prove(spec_text, targets, statement_out, out):
    """targets: [(object, symbol, the text of its places)]. Writes the statement and the proof; gives
    {symbol: (runs of the verifier, lines found)}."""
    functions = ordered([(obj, symbol) for obj, symbol, _ in targets])
    places_of = {symbol: text for _, symbol, text in targets}
    spec = ode.Spec(spec_text)
    seqs = sequences(spec)
    counted = {name: m["state"] for name, m in ode.Parser(spec_text).file()[2].items()}
    with open(statement_out, "w") as f: f.write("\n".join(statement(spec_text, functions)) + "\n")
    done, numbers = [], {}
    for at, (obj, symbol) in enumerate(functions):
        later = [s for _, s in functions[at + 1:]]
        keep, marked, runs = {}, {}, 0
        while True:
            kinds = kinds_of(spec.contracts[symbol], symbol, spec.layouts) if symbol in spec.contracts else {}
            p = Prover(statement_out, done + [f"for {symbol}"] + places(places_of[symbol], keep, seqs, kinds, counted, symbol, marked), out, later)
            p.last = ""
            try: proof = p.solve([])
            except Unkept as e:
                keep[e.args[0]] = [r for r in keep.get(e.args[0], REGISTERS) if r != REGISTERS[e.args[1]]]
                runs += p.runs
                p.close()
                continue
            except Marked as e:
                if REGISTERS[e.args[1]] in marked.get(e.args[0], []): raise SystemExit(f"prove: no proof of {symbol} found. The verifier's last word:\n{p.last}")
                marked[e.args[0]] = marked.get(e.args[0], []) + [REGISTERS[e.args[1]]]
                runs += p.runs
                p.close()
                continue
            if proof is None: raise SystemExit(f"prove: no proof of {symbol} found. The verifier's last word:\n{p.last}")
            k = len(proof) - 1
            while k >= 0:                              # a use of a definition opened to no purpose is taken out
                if proof[k].startswith("t open") and p.finished(p.ask(proof[:k] + proof[k + 1:])): del proof[k]
                k -= 1
            done = p.lines + proof
            numbers[symbol] = (runs + p.runs, len(proof))
            p.close()
            break
    with open(out, "w") as f: f.write("\n".join(done) + "\n")
    # the prover's helper is not the verifier: what was found is a proof only if `odeverify` says so
    said = subprocess.run([EXE, TABLE, statement_out, out], capture_output=True, text=True).stdout
    if not said.startswith("shown"): raise SystemExit(f"prove: the verifier does not take the proof that was found:\n{said[:400]}")
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
