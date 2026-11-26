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
from statement import sexp, statement, ordered, sequences, kinds_of, by_kind, table_for
import built, ode, session

TABLE = os.path.join(HERE, "..", "core", "x86.tab")
EXE = os.path.join(HERE, ".lake", "build", "bin", "odeverify")
FROM_THE_START = bool(os.environ.get("ODE_PROVE_FROM_START"))     # ask `odeverify` each time (the slow way, to compare with)
REGISTERS = ["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"]
REGISTERS_ARM = ["x0", "x1", "x2", "x3", "sp", "x5", "x6", "x7", "x8", "x9", "x10", "x11", "x12", "x13", "x14", "x15",
                 "x16", "x17", "x18", "x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26", "x27", "x28", "x29", "x30", "x4"]


def locate(statement_path, proof_path):
    """Run `odeprove --locate` to get (pc_or_None, fn_or_None, message) on a refusal.
    Relied on for nothing: only used for error diagnostics."""
    if not os.path.exists(session.EXE) or not os.path.exists(statement_path) or not os.path.exists(proof_path):
        return None, None, ""
    r = subprocess.run([session.EXE, "--locate", table_for(statement_path), statement_path, proof_path],
                       capture_output=True, text=True)
    out = r.stdout.strip()
    pc, fn = None, None
    body = []
    for line in out.splitlines():
        m = re.fullmatch(r"at \+(\d+)", line.strip())
        if m: pc = int(m.group(1)); continue
        m = re.fullmatch(r"in (\S+)", line.strip())
        if m: fn = m.group(1); continue
        body.append(line)
    return pc, fn, "\n".join(body)


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


def places(places_text, keep={}, seqs={}, kinds={}, counted={}, name="", marked={}, regs=None, marked_result={}):
    """The places as the verifier reads them; `keep`: for a place (by where it is), the registers it might keep
    (a place not in it: all it does not name); `seqs`: the specification's sequences (statement.sequences);
    `kinds`, `counted`, `name`: for a line of lanes (lane_line)."""
    reg_list = REGISTERS if regs is None else regs
    out, named, also, lanes, at, hdr_idx, saw_dec = [], [], [], [], None, None, False
    for raw in places_text.split("\n"):
        line = raw.split("//")[0].strip()
        if not line: continue
        if line == "}":
            if at is not None and not saw_dec:
                # A `place { ... }` without `decreases` is an acyclic mid-function join point.
                # Unlike loop places, named registers unchanged since the enclosing scope (e.g. a loop counter
                # referenced in `fact`) can stay kept; `Unkept` automatically removes any that changed across branches.
                out[hdr_idx] = f"join {at}"
                out.append("keep " + " ".join(r for r in reg_list if r in keep.get(at, reg_list)))
                if marked.get(at): out.append("marked " + " ".join(marked[at]))
                if marked_result.get(at): out.append("marked_result " + " ".join(marked_result[at]))
                out += lanes
            at, hdr_idx, saw_dec = None, None, False
            continue
        m = re.fullmatch(r"place \+(0x[0-9a-fA-F]+) \{", line)
        if m:
            at = int(m.group(1), 16)
            hdr_idx = len(out)
            out.append(f"place {at}")
            named, also, lanes, saw_dec = [], [], [], False
            continue
        m = re.fullmatch(r"keep ((?:\w+ ?)+)", line)              # registers a place names and keeps all the same
        if m: also += m.group(1).split(); continue
        m = re.fullmatch(r"name (\w+) = (\w+)", line)
        if m: out.append(f"name {m.group(1)} {m.group(2)}"); named.append(m.group(2)); continue
        if line.startswith("fact "): out.append("fact " + sexp(of_kinds(kbyte.expression(line[5:]), line, kinds, name), seqs)); continue
        m = re.fullmatch(r"wrote (\w+)\[(.+) \.\.\] = (.+)", line)       # from that place on, the run holds that list, place by place
        if m: lanes.append(f"wrote {m.group(1)} (index {sexp(kbyte.expression(m.group(3)), seqs)} {sexp(kbyte.expression(m.group(2)), seqs)})"); continue
        m = re.fullmatch(r"wrote (\w+)\[\.\. (.+)\] = (.+)", line)       # up to that place (0..HI), the run holds that list, place by place
        if m: lanes.append(f"wrote_pre {m.group(1)} (index {sexp(kbyte.expression(m.group(3)), seqs)} {sexp(kbyte.expression(m.group(2)), seqs)})"); continue
        m = re.fullmatch(r"lane (\w+): (.+?) = (.+) after (.+)", line)
        if m: lanes.append(lane_line(*m.groups(), seqs, kinds, counted, name)); continue
        m = re.fullmatch(r"cell \[rsp \+ (\d+)\]: word (\w+) = (.+)", line)
        if m: lanes.append(cell_line(*m.groups(), seqs, kinds, name)); continue
        if line.startswith("decreases "):
            saw_dec = True
            out.append("keep " + " ".join(r for r in reg_list if (r not in named or r in also) and r in keep.get(at, reg_list)))
            if marked.get(at): out.append("marked " + " ".join(marked[at]))      # registers that may depend on values kept out of the trace on a later coming there
            if marked_result.get(at): out.append("marked_result " + " ".join(marked_result[at]))
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


def proof_text(proof, given, raw_given=None):
    """A proof of arithmetic as the verifier reads it: the starting rows (emitted explicitly as `r ...`
    lines so the proof does not depend on any verifier's internal fact-list order), then the steps."""
    starts, steps = proof
    at = {}
    for number, f in enumerate(given): at.setdefault((frozenset(dict(f.c).items()), f.k), number)
    if os.environ.get("ODE_INDEX_PROOF") == "1" or raw_given is None:
        out = ["p " + " ".join(str(at[(frozenset((n, v) for n, v in c.items() if v), k)]) for c, k in starts)]
    else:
        out = ["r " + raw_given[at[(frozenset((n, v) for n, v in c.items() if v), k)]] for c, k in starts]
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
                seed_row = system[seed % len(system)]
                tried = None
                for steps in (2, 3, 4, 6):
                    close = near(system, seed % len(system), steps)
                    if close == tried: break
                    tried = close
                    last_q = frozenset(n for f in close if f != seed_row for n, c in f.c if abs(c) > 1)
                    found = derive_eq(close, 30000, last=last_q)
                    if not found and len(close) <= 45:
                        found = derive_eq(close, 1200, last=frozenset())
                    if found: break
            if not found and not quick:
                seed_row = system[seed % len(system)]
                for room in (30000, 300000):           # the rows near the one asked about, the quotients left for last
                    tried = None
                    for steps in (1, 2, 3, 4):
                        close = near(system, seed % len(system), steps)
                        if close == tried or len(close) == len(rows): break
                        tried = close
                        last_q = frozenset(n for f in close if f != seed_row for n, c in f.c if abs(c) > 1)
                        found = kprove.derive(close, room, last=last_q)
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


class Marked(Exception): pass           # at a place, a register may depend on a value kept out of the trace that did not on first coming there


class MarkedResult(Exception): pass     # the same, during the `result depends on` pass


class GaveUp(Exception): pass           # more runs of the verifier, or more time, than the prover was allowed


class NoPlace(Exception): pass          # a path looped back to the same instruction repeatedly with no place


_NO_DEST_OPS = frozenset({
    ".cmp", ".cmpi", ".cmpr", ".test", ".tst",
    ".push", ".str", ".str8", ".str32", ".str64", ".str64_sp", ".str128", ".str128_sp", ".st1",
    ".jmp", ".je", ".jne", ".jb", ".jae", ".ja", ".jbe",
    ".b", ".beq", ".bne", ".bhs", ".blo", ".bhi", ".bls",
    ".ret", ".nop", ".vzeroupper", ".prefetch",
})
_UNCOND_EXIT_OPS = frozenset({".ret", ".jmp", ".b"})


def fn_statement_info(statement_path, symbol, reg_list):
    """Extract (trace_exprs, instrs, written_at) for `symbol` from a statement file.
    `instrs`: list of (pc, next_pc, op, regs_used) in statement order.
    `written_at`: list of (pc, next_pc, op, target_or_none, dest_regs) for keep pre-seeding."""
    trace_exprs, instrs, raw_ins, cur = [], [], [], None
    reg_set = set(reg_list)
    is_arm = ("x0" in reg_set)
    default_keeps = ({"x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26", "x27", "x28", "x29", "sp"}
                     if is_arm else {"rbx", "rbp", "r12", "r13", "r14", "r15", "rsp"})
    fn_keeps = {}
    with open(statement_path) as f:
        for raw in f:
            line = raw.strip()
            if not line: continue
            parts = line.split()
            if parts[0] == "fn" and len(parts) >= 2:
                cur = parts[1]; continue
            if parts[0] == "keeps" and cur is not None:
                fn_keeps[cur] = set(parts[1:]) | ({"sp"} if is_arm else {"rsp"})
                continue
            if cur != symbol: continue
            if parts[0] == "traceexpr":
                trace_exprs.append(line[len("traceexpr "):].strip())
            elif parts[0] == "i" and len(parts) >= 4:
                pc, nxt, op = int(parts[1]), int(parts[2]), parts[3]
                regs, dests, target = [], set(), None
                for tok in parts[4:]:
                    v = tok.strip("().")
                    if v in reg_set and v not in regs:
                        regs.append(v)
                if op in (".call", ".bl") and len(parts) >= 5:
                    callee = parts[4].strip("().")
                    ck = fn_keeps.get(callee, default_keeps)
                    dests |= (reg_set - ck)
                    if op == ".bl" and "x30" in reg_set: dests.add("x30")
                    if op == ".call" and "rax" in reg_set: dests.add("rax")
                elif op in (".jmp", ".je", ".jne", ".jb", ".jae", ".ja", ".jbe",
                            ".b", ".beq", ".bne", ".bhs", ".blo", ".bhi", ".bls"):
                    if len(parts) >= 5:
                        try: target = int(parts[4], 0)
                        except ValueError: pass
                elif op not in _NO_DEST_OPS and not (op == ".mov" and len(parts) >= 6 and "(.mem" in parts[5]):
                    # First register token in operand list is the written destination GPR
                    if regs:
                        dests.add(regs[0])
                instrs.append((pc, nxt, op, regs))
                raw_ins.append((pc, nxt, op, target, dests))
    return trace_exprs, instrs, raw_ins


def loop_written_regs(raw_ins, at, reg_list):
    """Registers NOT modified on instructions that can reach `at` via a back-edge (always keeping sp/rsp)."""
    preds = {}
    for pc, nxt, op, target, _ in raw_ins:
        if op not in _UNCOND_EXIT_OPS:
            preds.setdefault(nxt, []).append(pc)
        if target is not None:
            preds.setdefault(target, []).append(pc)
    # Backward BFS from `at` restricted to pc >= at (loop body)
    seen, stack = set(), [p for p in preds.get(at, ()) if p >= at]
    while stack:
        u = stack.pop()
        if u in seen or u < at: continue
        seen.add(u)
        for p in preds.get(u, ()):
            if p >= at and p not in seen:
                stack.append(p)
    written = set()
    for pc, _, _, _, dests in raw_ins:
        if pc in seen:
            written |= dests
    written.discard("rsp"); written.discard("sp")
    return [r for r in reg_list if r not in written]


def join_written_regs(raw_ins, at, stop_pcs, reg_list):
    """For an acyclic join point at `at`, registers NOT modified on any path reaching `at` since
    entry or a preceding `place` in `stop_pcs` (always keeping sp/rsp)."""
    preds = {}
    for pc, nxt, op, target, _ in raw_ins:
        if op not in _UNCOND_EXIT_OPS:
            preds.setdefault(nxt, []).append(pc)
        if target is not None:
            preds.setdefault(target, []).append(pc)
    seen, stack = set(), [p for p in preds.get(at, ()) if p < at]
    while stack:
        u = stack.pop()
        if u in seen: continue
        seen.add(u)
        if u in stop_pcs: continue
        for p in preds.get(u, ()):
            if p < at and p not in seen:
                stack.append(p)
    written = set()
    for pc, _, _, _, dests in raw_ins:
        if pc in seen:
            written |= dests
    written.discard("rsp"); written.discard("sp")
    return [r for r in reg_list if r not in written]


class Prover:
    """Finds the proof of one function. `head`: the proof's lines before what is to be found (the parts of the
    functions shown before, `for NAME`, the places); `later`: the names of the statement's functions after it."""
    def __init__(self, statement_path, head, out, later=(), budget=None, until=None, trace_exprs=(), instrs=(), reg_list=REGISTERS, wrap_pcs=()):
        self.statement, self.lines, self.out, self.runs, self.later, self.budget = statement_path, head, out, 0, set(later), budget
        self.until = until                  # the time (time.time()) after which the search gives up
        self.session = None                 # the talk with `odeprove`, begun at the first question
        self.last = None
        self.last_proof = []
        self.best_last = None
        self.best_last_proof = []
        self.furthest_root = 0
        self.spec_fuel_hit = False
        self.spec_fuel_proof = []
        self.spec_max_open = 14
        self.hard_refusal = False
        self.trace_exprs = list(trace_exprs)
        self.instrs = list(instrs)
        self.reg_list = list(reg_list)
        self.wrap_pcs = set(wrap_pcs)
        self.tried_clears = set()
        self.saw_undecided_below = False
        self.split_tries = 0

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
            return subprocess.run([EXE, table_for(self.statement), self.statement, self.out], capture_output=True, text=True).stdout
        # `odeprove` says what the verifier would say, and goes only through the lines that are new (session.py)
        if self.session is None:
            names = [l.split()[1] for l in self.lines if l.split()[:1] == ["for"]]
            if not names: raise SystemExit("prove: the lines before the proof name no function (`for NAME`)")
            self.session = session.Session(self.statement, self.lines, names[-1], only=True)
        return self.session.ask(proof)

    def note(self, proof, said):
        if os.environ.get("PROVE_TRACE"): print(f"-- after {len(proof)} lines ({[l for l in proof if l.startswith('t ')][-6:]}): {said.splitlines()[0]}", file=sys.stderr)

    def fail(self, proof, said, force=False):
        """Record a branch failure, preserving the deepest partial proof reached across backtracking."""
        self.last = said
        self.last_proof = proof
        if force or self.best_last is None or len(proof) >= len(self.best_last_proof):
            self.best_last = said
            self.best_last_proof = proof
        self.note(proof, said)

    def clear_candidates(self, fail_pc, said):
        """Candidate (clear_pc, reg, expr) steps right at or just before `fail_pc`."""
        by_pc = {pc: (idx, nxt, op, regs) for idx, (pc, nxt, op, regs) in enumerate(self.instrs)}
        cands = []
        if fail_pc in by_pc:
            idx, _, op, regs = by_pc[fail_pc]
            # Try fail_pc itself (for memory reads, calls, returns) and up to 3 preceding instructions
            # (for jumps whose flags were set by a preceding test/cmp/subs).
            window = []
            for step in range(4):
                if idx - step < 0: break
                pc_i, _, op_i, regs_i = self.instrs[idx - step]
                rs = list(regs_i)
                if step == 0 and ("return" in said or op_i in ("ret", "ret_link")) and self.reg_list[0] not in rs:
                    rs.insert(0, self.reg_list[0])
                if step == 0 and "call" in said:
                    for r in self.reg_list[:6]:
                        if r not in rs: rs.append(r)
                for r in rs:
                    if r in ("rsp", "sp"): continue
                    window.append((pc_i, r))
            for pc_i, r in window:
                for expr in self.trace_exprs:
                    cands.append((pc_i, r, expr))
        return cands

    def solve(self, proof, allow_split=False):
        """The proof extended until the verifier says shown; None if this way does not get there."""
        while True:
            said = self.ask(proof)
            if self.finished(said): return proof
            m = re.search(r"at the (?:join )?place (\d+) register (\d+) (?:does not hold|depends on a value not in scope)", said)
            if m: raise Unkept(int(m.group(1)), int(m.group(2)))
            m = re.search(r"for `result depends on`:.*at the (?:join )?place (\d+) register (\d+) may depend on values kept out of the trace", said)
            if m: raise MarkedResult(int(m.group(1)), int(m.group(2)))
            m = re.search(r"at the (?:join )?place (\d+) register (\d+) may depend on values kept out of the trace", said)
            if m: raise Marked(int(m.group(1)), int(m.group(2)))
            if "a path returns to it" in said:
                self.last = said; self.last_proof = proof
                raise NoPlace(self.last)
            if not said.startswith("need "):
                if "kept out of the trace" in said and self.trace_exprs and "trace-clear" not in said:
                    with open(self.out, "w") as f: f.write("\n".join(self.lines + proof) + "\n")
                    fail_pc, _, _ = locate(self.statement, self.out)
                    if fail_pc is not None:
                        before, before_proof = self.last, self.last_proof
                        for clear_pc, reg, expr in self.clear_candidates(fail_pc, said):
                            key = (len(proof), clear_pc, reg, expr)
                            if key in self.tried_clears: continue
                            self.tried_clears.add(key)
                            done = self.solve(proof + [f"clear {clear_pc} {reg} {expr}"])
                            if done is not None: return done
                        self.last, self.last_proof = (before, before_proof) if before else (said, proof)
                        return None
                is_spec_local = any(said.startswith(p) for p in (
                    "refused: the value held is of another use",
                    "refused: two uses of a definition with other things",
                    "refused: a use of a definition opened where a number is needed",
                    "refused: no such value is held",
                    "refused: no such use of a definition",
                    "refused: a condition that is not true or false",
                ))
                if not is_spec_local:
                    self.hard_refusal = True
                    self.fail(proof, said, force=True)
                else:
                    self.last = said; self.last_proof = proof; self.note(proof, said)
                return None
            lines = said.split("\n")
            what = lines[0][5:]
            raw_facts = [l[2:].strip() for l in lines if l.startswith("f ")]
            raw_goals = [l[2:].strip() for l in lines if l.startswith("g ")]
            facts = [lin([int(x) for x in s.split()]) for s in raw_facts]
            goals = [lin([int(x) for x in s.split()]) for s in raw_goals]
            if what in ("entail", "same"):                  # (same: are two uses of a definition of the same things)
                p = refutation(facts + [negation(goals[0])], quick=what == "same")
                if p is None:
                    if what == "entail" and self.wrap_pcs:
                        with open(self.out, "w") as f: f.write("\n".join(self.lines + proof) + "\n")
                        fail_pc, _, _ = locate(self.statement, self.out)
                        if fail_pc is not None and fail_pc in self.wrap_pcs:
                            nxt_said = self.ask(proof + ["t wrap"])
                            if nxt_said != said and not nxt_said.startswith("refused:"):
                                proof = proof + ["t wrap"]
                                continue
                    self.fail(proof, said); return None
                g_nums = [int(x) for x in raw_goals[0].split()]
                neg_raw = " ".join([str(-1 - g_nums[0])] + [str(-x) for x in g_nums[1:]])
                proof = proof + proof_text(p, [negation(goals[0])] + facts, [neg_raw] + raw_facts)
            elif what == "branch":
                p = refutation(facts, 0)                       # (the newest fact is first)
                if p is None:
                    # Guard against a loop with no place spinning `t live` forever (REVIEW item 4):
                    lives = proof.count("t live")
                    if lives >= 80 and lives % 40 == 0:
                        with open(self.out, "w") as f: f.write("\n".join(self.lines + proof) + "\n")
                        pc, _, msg = locate(self.statement, self.out)
                        if pc is not None and "with no place" in msg:
                            self.last = f"at +{pc}\n{msg}"; self.last_proof = proof
                            raise NoPlace(self.last)
                    proof = proof + ["t live"]
                else:
                    proof = proof + ["t dead"] + proof_text(p, facts, raw_facts)
            elif what == "branch_neq":
                # False branch of `equal a b`: `goals[0]` is `a - b`.
                # If `a > b` or `a < b` is already impossible (e.g. `i <= n` or `x >= 0`), take the
                # stronger inequality branch (`a < b` or `a > b`); otherwise emit `t neq 0` to keep
                # ONE symbolic state recording `a != b` instead of splitting into 2^N paths!
                d_nums = [int(x) for x in raw_goals[0].split()]
                gt_nums = [d_nums[0] - 1] + d_nums[1:]
                lt_nums = [-d_nums[0] - 1] + [-x for x in d_nums[1:]]
                gt_lin, lt_lin = lin(gt_nums), lin(lt_nums)
                gt_raw = " ".join(str(x) for x in gt_nums)
                lt_raw = " ".join(str(x) for x in lt_nums)
                p_gt = refutation([gt_lin] + facts, 0) if gt_lin.c else None
                if p_gt is not None:
                    proof = proof + ["t dead"] + proof_text(p_gt, [gt_lin] + facts, [gt_raw] + raw_facts)
                elif lt_lin.c and refutation([lt_lin] + facts, 0) is not None:
                    proof = proof + ["t live"]
                elif not gt_lin.c or not lt_lin.c:
                    proof = proof + ["t neq 0"]
                else:
                    done = self.solve(proof + ["t neq 0"], allow_split=allow_split)
                    if done is not None:
                        return done
                    proof = proof + ["t live"]
            elif what == "below":                              # is a - b below zero: `lt`, or not: `ge`
                d = goals[0]
                if refutation(facts + [d]): proof = proof + ["t lt"]
                elif refutation(facts + [negation(d)]): proof = proof + ["t ge"]
                else:
                    self.saw_undecided_below = True
                    # Pass 2 only: branchless single-compare range checks like `(c -% lo) <= hi - lo`:
                    # split on `d >= 0` vs `d < 0` via `t split` + `k <row>` (strictly bounded).
                    split_row = raw_goals[0]
                    if allow_split and proof.count("t split") < 2 and self.split_tries < 6:
                        saved_furthest = self.furthest_root
                        for cut in range(len(proof), max(-1, len(proof) - 16), -1):
                            if cut < len(proof) and proof[cut].startswith("k "):
                                continue
                            cand = proof[:cut] + ["t split", "k " + split_row]
                            ans = self.ask(cand)
                            if ans != said and (ans == "shown" or ans.startswith("need ")):
                                self.split_tries += 1
                                done = self.solve(cand, allow_split=allow_split)
                                if done is not None:
                                    return done
                                self.furthest_root = saved_furthest
                                break
                    self.fail(proof, said)
                    return None
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
                if found is None: self.fail(proof, said); return None
                proof = found
            elif what == "samebyte":                           # pairs (v_k, o - o'_k): unify readByte with an already-read byte at equal offset
                chosen = None
                for k in range(0, len(goals) - 1, 2):
                    v_id = goals[k].k
                    diff = goals[k + 1]
                    if refutation(facts + [negation(diff)]) and refutation(facts + [negation(-diff)]):
                        chosen = v_id
                        break
                proof = proof + ([f"t samebyte {chosen}"] if chosen is not None else ["t newbyte 0"])
            elif what == "shift":                              # a shift to the left: is the number shown to lose no bit, or is only its low part kept
                proof = proof + (["t exact"] if refutation(facts + [negation(goals[0])]) else ["t wrap"])
            elif what == "compare":
                d = goals[0]
                if refutation(facts + [negation(d)]) and refutation(facts + [negation(-d)]): proof = proof + ["t eq"]
                elif refutation(facts + [d]): proof = proof + ["t lt"]
                elif refutation(facts + [-d]): proof = proof + ["t gt"]
                else: self.fail(proof, said); return None
            elif what == "spec":
                count = int([l for l in lines if l.startswith("c ")][0].split()[1])
                opened = int([l for l in lines if l.startswith("o ")][0].split()[1])
                held = int(([l for l in lines if l.startswith("h ")] or ["h 0"])[0].split()[1])
                start_len = len(proof)
                if opened == 0:
                    if start_len > self.furthest_root:
                        self.furthest_root = start_len
                    self.spec_fuel_hit = False
                before, before_proof = self.last, self.last_proof
                # First try exact congruence (`t same (i * 256 + j)`) on same-function call pairs
                # reported by `p ...` whose arguments are provably equal (e.g. `words == 2 * ihl`)!
                # At `opened == 0` check all pairs; at `opened == 1` check only pairs involving a
                # newly added call (tail index) so earlier unrelated calls are never re-probed.
                plines = [l[2:].strip() for l in lines if l.startswith("p ")]
                if opened <= 1 and plines and plines[0]:
                    nums = [int(x) for x in plines[0].split()]
                    for pi in range(0, len(nums) - 1, 2):
                        ci_k, cj_k = nums[pi], nums[pi + 1]
                        if opened == 1 and cj_k != count - 1:
                            continue
                        p_same = proof + [f"t same {ci_k * 256 + cj_k}"]
                        sa = self.ask(p_same)
                        ok_same = True
                        while sa.startswith("need same\n"):
                            sl = sa.split("\n")
                            sf_raw = [l[2:].strip() for l in sl if l.startswith("f ")]
                            sg_raw = [l[2:].strip() for l in sl if l.startswith("g ")]
                            sf = [lin([int(x) for x in s.split()]) for s in sf_raw]
                            sg = [lin([int(x) for x in s.split()]) for s in sg_raw]
                            rp = refutation(sf + [negation(sg[0])], quick=True)
                            if rp is None:
                                ok_same = False
                                break
                            gn = [int(x) for x in sg_raw[0].split()]
                            nr = " ".join([str(-1 - gn[0])] + [str(-x) for x in gn[1:]])
                            p_same = p_same + proof_text(rp, [negation(sg[0])] + sf, [nr] + sf_raw)
                            sa = self.ask(p_same)
                        if ok_same and not sa.startswith("refused:"):
                            proof = p_same
                            break
                    else:
                        p_same = None
                    if p_same is not None and proof is p_same:
                        continue
                ylines = [l for l in lines if l.startswith("y")]
                if ylines:
                    carry_ks = [int(x) for x in ylines[0][1:].split()]
                else:
                    carry_ks = list(range(held))
                for k in reversed(carry_ks):                   # a value held, carried over to the fact asked for
                    if self.hard_refusal or self.furthest_root > start_len: return None
                    trial = proof + [f"t carry {k}"]
                    ans_c = self.ask(trial)
                    if ans_c.startswith("refused: no such value is held"):
                        break
                    if ans_c.startswith("refused:"):
                        continue
                    done = self.solve(trial, allow_split=allow_split)
                    if done is not None: return done
                    if self.hard_refusal or self.furthest_root > start_len: return None
                self.last, self.last_proof = (before, before_proof) if before else (said, proof)    # (a value that does not carry over is not why no proof is found)
                if opened >= self.spec_max_open:
                    self.spec_fuel_hit = True
                    self.spec_fuel_proof = proof
                    self.last = f"need spec (reached {self.spec_max_open} specification definition opens without closing goal)"
                    self.last_proof = proof
                    return None
                if opened >= 2:
                    # Deep recursive unfolding (e.g. 4x..18x unrolled loops): advance greedily along the
                    # single newly created call (at the tail/head of `callsOf`), so depth 20 stays O(depth)
                    # instead of branching exponentially.
                    cands = []
                    order_k = (count - 1, count - 2, count - 3, 1, 0) if opened == 2 else (count - 2, count - 1, count - 3, 1, 0)
                    for k in order_k:
                        if 0 <= k < count and k not in cands:
                            cands.append(k)
                    for k in cands:
                        p_try = proof + [f"t open {k}"]
                        # Step through deterministic inner checks of `openCall` (`below`/`entail`/`same`/`compare`/`held`)
                        # until we either close the `spec` goal, hit the next `need spec`, or fail.
                        ok_step, nxt = True, self.ask(p_try)
                        for _ in range(24):
                            if not nxt.startswith("need "): break
                            nl = nxt.split("\n")
                            nw = nl[0][5:]
                            if nw == "spec": break
                            if nw == "held":
                                hc = int([l for l in nl if l.startswith("c ")][0].split()[1])
                                mls = [l for l in nl if l.startswith("m")]
                                hks = [int(x) for x in mls[0][1:].split()] if mls else list(range(hc))
                                picked = None
                                for hk in reversed(hks):
                                    ht = p_try + [f"t held {hk}"]
                                    ha = self.ask(ht)
                                    if ha.startswith("refused: the value held is of another use"):
                                        continue
                                    if ha.startswith("need same\n"):
                                        hl = ha.split("\n")
                                        hf_raw = [l[2:].strip() for l in hl if l.startswith("f ")]
                                        hg_raw = [l[2:].strip() for l in hl if l.startswith("g ")]
                                        hf = [lin([int(x) for x in s.split()]) for s in hf_raw]
                                        hg = [lin([int(x) for x in s.split()]) for s in hg_raw]
                                        rp = refutation(hf + [negation(hg[0])], quick=True)
                                        if rp is None:
                                            continue
                                        gn = [int(x) for x in hg_raw[0].split()]
                                        nr = " ".join([str(-1 - gn[0])] + [str(-x) for x in gn[1:]])
                                        picked = ht + proof_text(rp, [negation(hg[0])] + hf, [nr] + hf_raw)
                                        break
                                    picked = ht
                                    break
                                p_try = picked if picked is not None else (p_try + ["t open"])
                                nxt = self.ask(p_try)
                                continue
                            if nw not in ("below", "entail", "same", "compare"):
                                break
                            nf_raw = [l[2:].strip() for l in nl if l.startswith("f ")]
                            ng_raw = [l[2:].strip() for l in nl if l.startswith("g ")]
                            nf = [lin([int(x) for x in s.split()]) for s in nf_raw]
                            ng = [lin([int(x) for x in s.split()]) for s in ng_raw]
                            if nw in ("entail", "same"):
                                rp = refutation(nf + [negation(ng[0])], quick=nw == "same")
                                if rp is None: ok_step = False; break
                                gn = [int(x) for x in ng_raw[0].split()]
                                nr = " ".join([str(-1 - gn[0])] + [str(-x) for x in gn[1:]])
                                p_try = p_try + proof_text(rp, [negation(ng[0])] + nf, [nr] + nf_raw)
                            elif nw == "below":
                                if refutation(nf + [ng[0]]): p_try = p_try + ["t lt"]
                                elif refutation(nf + [negation(ng[0])]): p_try = p_try + ["t ge"]
                                else: ok_step = False; break
                            elif nw == "compare":
                                if refutation(nf + [negation(ng[0])]) and refutation(nf + [negation(-ng[0])]): p_try = p_try + ["t eq"]
                                elif refutation(nf + [ng[0]]): p_try = p_try + ["t lt"]
                                elif refutation(nf + [-ng[0]]): p_try = p_try + ["t gt"]
                                else: ok_step = False; break
                            nxt = self.ask(p_try)
                        if not ok_step:
                            continue
                        if nxt.startswith("need spec\n"):
                            nl2 = nxt.split("\n")
                            nc = int([l for l in nl2 if l.startswith("c ")][0].split()[1])
                            no = int([l for l in nl2 if l.startswith("o ")][0].split()[1])
                            nh = int(([l for l in nl2 if l.startswith("h ")] or ["h 0"])[0].split()[1])
                            if no > 0 and nc <= count and nh <= held:
                                continue                       # already-opened call with no new held value; skip without branching
                            done = self.solve(p_try, allow_split=allow_split) # brand-new call or next path (`no == 0`)
                            if done is not None: return done
                            if opened >= 3 or self.hard_refusal or self.furthest_root > start_len: return None
                            continue
                        # Spec goal closed (or moved past `spec` to next instruction)!
                        done = self.solve(p_try, allow_split=allow_split)
                        if done is not None: return done
                        if self.hard_refusal or self.furthest_root > start_len: return None
                    if opened >= 3 or self.spec_fuel_hit:
                        return None
                any_fuel_hit = False
                prev_max = self.spec_max_open
                budgets = (14, 30) if opened == 0 else (prev_max,)
                for bud in budgets:
                    self.spec_max_open = bud
                    any_fuel_hit = False
                    for k in reversed(range(count)):
                        if self.hard_refusal:
                            self.spec_max_open = prev_max
                            return None
                        self.spec_fuel_hit = False
                        done = self.solve(proof + [f"t open {k}"], allow_split=allow_split)
                        if done is not None:
                            self.spec_max_open = prev_max
                            return done
                        if self.hard_refusal or self.furthest_root > start_len:
                            self.spec_max_open = prev_max
                            return None
                        if self.spec_fuel_hit:
                            any_fuel_hit = True
                    if not any_fuel_hit:
                        break
                self.spec_max_open = prev_max
                if any_fuel_hit:
                    self.spec_fuel_hit = True
                    if opened == 0:
                        self.last = "need spec (reached 30 specification definition opens without closing goal)"
                        self.last_proof = self.spec_fuel_proof
                return None
            elif what == "held":                               # which value held is of a use with the same things
                count = int([l for l in lines if l.startswith("c ")][0].split()[1])
                mls = [l for l in lines if l.startswith("m")]
                held_ks = [int(x) for x in mls[0][1:].split()] if mls else list(range(count))
                start_len = len(proof)
                before, before_proof = self.last, self.last_proof
                matched_any = False
                for k in reversed(held_ks):
                    if self.hard_refusal or self.furthest_root > start_len:
                        return None
                    trial = proof + [f"t held {k}"]
                    ans = self.ask(trial)
                    if ans.startswith("refused: the value held is of another use"):
                        continue
                    if ans.startswith("need same\n"):
                        hl = ans.split("\n")
                        hf_raw = [l[2:].strip() for l in hl if l.startswith("f ")]
                        hg_raw = [l[2:].strip() for l in hl if l.startswith("g ")]
                        hf = [lin([int(x) for x in s.split()]) for s in hf_raw]
                        hg = [lin([int(x) for x in s.split()]) for s in hg_raw]
                        rp = refutation(hf + [negation(hg[0])], quick=True)
                        if rp is None:
                            continue
                        gn = [int(x) for x in hg_raw[0].split()]
                        nr = " ".join([str(-1 - gn[0])] + [str(-x) for x in gn[1:]])
                        trial = trial + proof_text(rp, [negation(hg[0])] + hf, [nr] + hf_raw)
                    matched_any = True
                    done = self.solve(trial, allow_split=allow_split)
                    if done is not None: return done
                    if self.hard_refusal or self.furthest_root > start_len:
                        return None
                if not matched_any:
                    self.last, self.last_proof = before, before_proof
                if self.hard_refusal: return None
                done = self.solve(proof + ["t open"], allow_split=allow_split) # no value held fits: the use is opened where it is met
                if done is not None: return done
                if self.hard_refusal: return None
                if not self.last or self.last.startswith("refused: the value held is of another use"):
                    self.last = said; self.last_proof = proof
                self.note(proof, said + ' (no value held fits, and opening the use does not do)')
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
    reg_list = REGISTERS_ARM if table_for(statement_out).endswith("arm64.tab") else REGISTERS
    done, numbers = [], {}
    for at, (obj, symbol) in enumerate(functions):
        later = [s for _, s in functions[at + 1:]]
        keep, marked, marked_result, runs = {}, {}, {}, 0
        trace_exprs, instrs, raw_ins = fn_statement_info(statement_out, symbol, reg_list)
        # Pre-seed `keep` for loop `place`s (those with `decreases`) by excluding registers written in the loop body,
        # and collect any `wrap +0xNN` directives marking explicit wrapping `+%`/`-%` instructions.
        preseeded = False
        place_pcs = set()
        place_specs = []
        wrap_pcs = set()
        filtered_place_lines = []
        cur_pat, cur_has_dec = None, False
        for pline in places_of[symbol].splitlines():
            sline = pline.split("//")[0].strip()
            wm = re.fullmatch(r"wrap \+(0x[0-9a-fA-F]+)", sline)
            if wm:
                wrap_pcs.add(int(wm.group(1), 16))
                continue
            filtered_place_lines.append(pline)
            pm = re.fullmatch(r"place \+(0x[0-9a-fA-F]+) \{", sline)
            if pm:
                cur_pat, cur_has_dec = int(pm.group(1), 16), False
            elif sline.startswith("decreases "):
                cur_has_dec = True
            elif sline == "}" and cur_pat is not None:
                place_pcs.add(cur_pat)
                place_specs.append((cur_pat, cur_has_dec))
                cur_pat, cur_has_dec = None, False
        clean_places_text = "\n".join(filtered_place_lines)
        for cur_pat, cur_has_dec in place_specs:
            if cur_has_dec:
                keep[cur_pat] = loop_written_regs(raw_ins, cur_pat, reg_list)
                preseeded = True
            else:
                keep[cur_pat] = join_written_regs(raw_ins, cur_pat, place_pcs - {cur_pat}, reg_list)
                preseeded = True
        max_asks = int(os.environ.get("ODE_PROVE_MAX_ASKS", "15000"))
        timeout_s = float(os.environ.get("ODE_PROVE_TIMEOUT", "60"))
        fn_deadline = time.time() + timeout_s if timeout_s > 0 else None
        while True:
            kinds = kinds_of(spec.contracts[symbol], symbol, spec.layouts) if symbol in spec.contracts else {}
            p = Prover(statement_out, done + [f"for {symbol}"] + places(clean_places_text, keep, seqs, kinds, counted, symbol, marked, regs=reg_list, marked_result=marked_result), out, later,
                       budget=max_asks if max_asks > 0 else None, until=fn_deadline,
                       trace_exprs=trace_exprs, instrs=instrs, reg_list=reg_list, wrap_pcs=wrap_pcs)
            p.last = ""
            p.last_proof = []
            try:
                proof = p.solve([], allow_split=False)
                if proof is None and p.saw_undecided_below and not p.hard_refusal:
                    p.furthest_root = 0
                    p.spec_fuel_hit = False
                    proof = p.solve([], allow_split=True)
            except GaveUp:
                fin_last = p.best_last or p.last or "prover search budget exceeded"
                fin_proof = p.best_last_proof if p.best_last is not None else p.last_proof
                p.close()
                with open(out, "w") as f: f.write("\n".join(p.lines + fin_proof) + "\n")
                raise SystemExit(
                    f"prove: no proof of {symbol} found (search budget exceeded after {p.runs} verifier queries; "
                    f"set ODE_PROVE_TIMEOUT/ODE_PROVE_MAX_ASKS to raise). The verifier's last word:\n{fin_last}"
                )
            except Unkept as e:
                keep[e.args[0]] = [r for r in keep.get(e.args[0], reg_list) if r != reg_list[e.args[1]]]
                runs += p.runs
                p.close()
                continue
            except Marked as e:
                if reg_list[e.args[1]] in marked.get(e.args[0], []): raise SystemExit(f"prove: no proof of {symbol} found. The verifier's last word:\n{p.last}")
                marked[e.args[0]] = marked.get(e.args[0], []) + [reg_list[e.args[1]]]
                runs += p.runs
                p.close()
                continue
            except MarkedResult as e:
                if reg_list[e.args[1]] in marked_result.get(e.args[0], []): raise SystemExit(f"prove: no proof of {symbol} found. The verifier's last word:\n{p.last}")
                marked_result[e.args[0]] = marked_result.get(e.args[0], []) + [reg_list[e.args[1]]]
                runs += p.runs
                p.close()
                continue
            except NoPlace:
                p.close()
                with open(out, "w") as f: f.write("\n".join(p.lines + p.last_proof) + "\n")
                raise SystemExit(f"prove: no proof of {symbol} found. The verifier's last word:\n{p.last}")
            if proof is None:
                if preseeded:
                    # Fallback in case a loop saved and restored a register across the loop body.
                    keep, preseeded = {}, False
                    runs += p.runs
                    p.close()
                    continue
                # Preserve partial proof at the deepest failure so callers can run `locate()` on the exact point.
                fin_last = p.best_last or p.last
                fin_proof = p.best_last_proof if p.best_last is not None else p.last_proof
                with open(out, "w") as f: f.write("\n".join(p.lines + fin_proof) + "\n")
                raise SystemExit(f"prove: no proof of {symbol} found. The verifier's last word:\n{fin_last}")
            if len(proof) < 200:
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
    said = subprocess.run([EXE, table_for(statement_out), statement_out, out], capture_output=True, text=True).stdout
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
