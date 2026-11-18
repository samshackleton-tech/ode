#!/usr/bin/env python3
"""statement: what is to be shown of functions, for the verifier in Lean (Core.lean). RELIED ON.

    python3 statement.py SPEC OUT.statement OBJECT:SYMBOL [OBJECT:SYMBOL …]

Each function's instructions as ../kcheck/kdecode.py reads them from its OBJECT's bytes by the table, the
contract of each SYMBOL in SPEC and the definitions of SPEC as ../kcheck/ode.py reads them, written as the
lines Main.lean reads. A contract or a definition with anything the verifier in Lean does not read yet is
refused here: no line of a contract is left out. A function is written after those it calls (the verifier
takes a call only by the contract of a function it has shown before). The theorem in SoundTop.lean is about
what these lines say; that they say what the files' bytes and the specification's text say rests on this
file and the two it reads with."""
import os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "kcheck"))
import kdecode, ode


class Scope:
    """Where an expression stands. `consts`: the specification's constants; `given`: the names given a meaning
    there (a definition's own, its `let`s, the name a list is made over), or None where that is not said (then
    no name is taken for a constant). `local`: inside a definition, its sequences {name: the things the
    definition it is lifted to is used with before the place}; `own`: the definition's name; `before`: inside
    a sequence's second equation, (the sequence's name, the name of the place before)."""
    def __init__(self, consts=(), given=None, local=None, own=None, before=None):
        self.consts, self.given, self.local, self.own, self.before = consts, given, local or {}, own, before
    def with_name(self, x):
        if self.local and any(x in things for things in self.local.values()):
            raise SystemExit(f"statement: {self.own}: the name {x} is given twice in a definition with sequences: the verifier in Lean does not read that yet")
        return Scope(self.consts, None if self.given is None else self.given | {x}, self.local, self.own, self.before)


def sexp(e, seqs={}, scope=None):
    """An expression as Reader.lean reads one. `seqs`: the specification's sequences, each with how many things
    it is of; NAME(x)[k], the sequence's value at place k, is written as the use NAME(x, k) of the
    definition the sequence is (sequence_def). A constant is written as the use of the definition it is, of
    nothing."""
    scope = scope or Scope()
    go = lambda x: sexp(x, seqs, scope)
    kind = e[0]
    if kind == "num": return f"(num {e[1]})"
    if kind == "name":
        if e[1] in scope.local: raise SystemExit(f"statement: {scope.own}: the sequence {e[1]} is used other than at a place of it")
        if scope.given is not None and e[1] not in scope.given and e[1] in scope.consts: return f"(call {e[1]})"
        return f"(name {e[1]})"
    if kind == "bin": return f"(bin {e[1]} {go(e[2])} {go(e[3])})"
    if kind == "list": return "(" + " ".join(["list"] + [go(a) for a in e[1]]) + ")"
    if kind == "ifx": return f"(ifx {go(e[1])} {go(e[2])} {go(e[3])})"
    if kind == "index":
        if e[1][0] == "name" and e[1][1] in scope.local:
            # a definition's own sequence at a place: the use of the definition it is lifted to; inside its
            # second equation, the value at the place before is had once, by a `let` (lifted)
            if scope.before == (e[1][1], e[2][1] if e[2][0] == "name" else None): return f"(name {e[1][1]})"
            return "(call " + " ".join([f"{scope.own}.{e[1][1]}"] + [f"(name {x})" for x in scope.local[e[1][1]]] + [go(e[2])]) + ")"
        if e[1][0] == "call" and e[1][1] in seqs and len(e[1][2]) == seqs[e[1][1]]:
            return "(call " + " ".join([e[1][1]] + [go(a) for a in e[1][2]] + [go(e[2])]) + ")"
        return f"(index {go(e[1])} {go(e[2])})"
    if kind == "call":
        if e[1] in seqs and len(e[2]) != seqs[e[1]] + 1:
            raise SystemExit(f"statement: the sequence {e[1]} is used other than at one place of it: the verifier in Lean does not read that yet")
        return "(call " + " ".join([e[1]] + [go(a) for a in e[2]]) + ")"
    if kind == "each":
        inner = scope.with_name(e[2])
        return f"(each {sexp(e[1], seqs, inner)} {e[2]} {go(e[3])} {go(e[4])})"
    if kind == "slice": return f"(slice {go(e[1])} {go(e[2])} {go(e[3])})"
    if kind == "with": return "(" + " ".join(["with", go(e[1])] + [go(x) for pair in e[2] for x in pair]) + ")"
    if kind == "record":
        if len({name for name, _ in e[1]}) != len(e[1]): raise SystemExit("statement: a record with a name twice")
        return "(" + " ".join(["record"] + [f"({name} {go(x)})" for name, x in e[1]]) + ")"
    if kind == "field": return f"(field {go(e[1])} {e[2]})"
    if kind == "the":
        _, which, var, among, cond = e
        inner = scope.with_name(var)
        if among[0] == "range": return f"(thenumber {which} {var} {go(among[1])} {go(among[2])} {sexp(cond, seqs, inner)})"
        return f"(thepower {which} {var} {sexp(cond, seqs, inner)})"
    raise SystemExit(f"statement: an expression of a kind the verifier in Lean does not read yet: {e!r}")


def fresh(name, taken):
    while name in taken: name += "_"
    return name


def definition_lines(name, params, body, seqs, consts):
    """A definition as `def` lines: its `let`s one inside the next, then its value. A sequence of its own,

        let s[0] = E      let s[i + 1] = F

    is lifted to a definition of its own, `NAME.s`, of the names given before the definition's first sequence
    and a place k:    def NAME.s … k = if k == 0 then E else (let i = k - 1; let s = NAME.s(…, i); F'), F' being
    F with the name s for s[i], the value at the place before. In the definition, s[e] is the use NAME.s(…, e)."""
    kinds = [s[0] for s in body]
    if "fails" in kinds: raise SystemExit(f"statement: the definition {name} has `fails`, which the verifier in Lean does not read yet")
    lets = [s[1] for s in body if s[0] == "set"]
    if len(set(params)) != len(params) or len(set(params + lets)) != len(params + lets):
        raise SystemExit(f"statement: the definition {name} gives a name twice")
    local, things = {}, None                # things: what was given before the first sequence
    given = list(params)
    for s in body:
        if s[0] in ("first", "next"):
            if things is None: things = list(given)
            if s[0] in local.setdefault(s[1], {}): raise SystemExit(f"statement: {name}: the sequence {s[1]} has an equation twice")
            local[s[1]][s[0]] = s
        elif s[0] == "set": given.append(s[1])
    def names(e):
        """Every name an expression holds (whatever gives it its meaning there)."""
        if isinstance(e, tuple) and len(e) == 2 and e[0] == "name": return {e[1]}
        return set().union(*[names(x) for x in e]) if isinstance(e, (tuple, list)) else set()
    for s, eqs in local.items():
        if set(eqs) != {"first", "next"}: raise SystemExit(f"statement: {name}: the sequence {s} without its two equations")
        if s in params + lets: raise SystemExit(f"statement: {name}: {s} is a sequence and a name")
        # An equation is read with the names given before the definition's first sequence. (ode.py reads it
        # with whatever the definition has given by the time the sequence is used: a name given later is
        # refused here, so that the two readings are one.)
        later = (names(eqs["first"][2]) | names(eqs["next"][3])) & (set(lets) - set(things))
        if later: raise SystemExit(f"statement: {name}: the sequence {s} uses {', '.join(sorted(later))}, given after the definition's first sequence: "
                                   "the verifier in Lean does not read that yet")
    lifted = {s: things for s in local}
    out = []
    # the definition itself
    scope = Scope(consts, frozenset(params), lifted, name)
    text, closing = "", 0
    for s in body:
        if s[0] == "set":
            text += f"(let {s[1]} {sexp(s[2], seqs, scope)} "; closing += 1
            scope = Scope(consts, scope.given | {s[1]}, lifted, name)
        elif s[0] == "expr": text += sexp(s[1], seqs, scope) + ")" * closing
    out.append(" ".join(["def", name] + params + ["=", text]))
    # its sequences
    for s, eqs in local.items():
        var = eqs["next"][2]
        k = fresh("place", set(things) | set(local) | {var})
        if var in things or var in local: raise SystemExit(f"statement: {name}: the sequence {s} counts by a name given before")
        first = sexp(eqs["first"][2], seqs, Scope(consts, frozenset(things), lifted, name))
        nxt = sexp(eqs["next"][3], seqs, Scope(consts, frozenset(things) | {var, s}, lifted, name, (s, var)))
        again = "(call " + " ".join([f"{name}.{s}"] + [f"(name {x})" for x in things] + [f"(name {var})"]) + ")"
        out.append(" ".join(["def", f"{name}.{s}"] + things + [k, "="]) +
                   f" (ifx (bin == (name {k}) (num 0)) {first} (let {var} (bin - (name {k}) (num 1)) (let {s} {again} {nxt})))")
    return out


def machine_lines(name, m, seqs, consts):
    """A sequence with its count,

        sequence NAME(x) { h[0] = E    h[b + 1] = F    for b in 0..n }        NAME(x) is its last, h[n]

    (../kcheck/ode.py reads it with the name h for h[b] in F), as two `def` lines: NAME.h, of x and a place k,
    as a definition's own sequence is lifted (definition_lines), and NAME(x) = NAME.h(x, n)."""
    params, h = m["params"], m["state"]
    if (m["loop"][0] != "for" or m["loop"][2] != ("num", 0) or h is None or m["init"] is None
            or len(m["turn"]) != 1 or m["turn"][0][0] != "set" or m["turn"][0][1] != h):
        raise SystemExit(f"statement: {name} is a machine, which the verifier in Lean does not read yet")
    var, count = m["loop"][1], m["loop"][3]
    if len(set(params)) != len(params) or var in params or h in params or var == h:
        raise SystemExit(f"statement: the sequence {name} gives a name twice")
    k = fresh("place", set(params) | {h, var})
    first = sexp(m["init"], seqs, Scope(consts, frozenset(params)))
    nxt = sexp(m["turn"][0][2], seqs, Scope(consts, frozenset(params) | {var, h}))
    things = [f"(name {x})" for x in params]
    again = "(call " + " ".join([f"{name}.{h}"] + things + [f"(name {var})"]) + ")"
    return [" ".join(["def", f"{name}.{h}"] + params + [k, "="]) +
            f" (ifx (bin == (name {k}) (num 0)) {first} (let {var} (bin - (name {k}) (num 1)) (let {h} {again} {nxt})))",
            " ".join(["def", name] + params + ["="]) + " (call " + " ".join([f"{name}.{h}"] + things + [sexp(count, seqs, Scope(consts, frozenset(params)))]) + ")"]


def definitions(spec_text):
    """The specification's constants, definitions and sequences as the `def` lines Reader.lean reads."""
    spec = ode.Spec(spec_text)
    seqs = sequences(spec)
    consts, fns, machines = ode.Parser(spec_text).file()          # (the constants as they are written)
    out = []
    for name, e in consts.items(): out.append(f"def {name} = " + sexp(e, seqs, Scope(consts, frozenset())))
    for name, (params, body) in fns.items(): out += definition_lines(name, params, body, seqs, consts)
    for name, seq in spec.seqs.items(): out.append(sequence_def(name, seq, seqs))
    for name, m in machines.items(): out += machine_lines(name, m, seqs, consts)
    return out


def sequence_def(name, seq, seqs):
    """A sequence as the definition it is (LANGUAGE.md: values in order, each from the one before):

        sequence NAME(x) { s[0] = E   s[i + 1] = F }      NAME(x)[k] is its value at place k

    is written    def NAME x k = if k == 0 then E else F', F' being F with k - 1 for i and NAME(x, k - 1) for s[i]."""
    params, h, var, first, nxt = seq
    k = "place"
    while k in params or k in (h, var): k += "_"
    before = ("bin", "-", ("name", k), ("num", 1))
    def put(e, inside):
        kind = e[0]
        if kind == "num": return e
        if kind == "name":
            if e[1] == h or (e[1] == var and not inside): raise SystemExit(f"statement: the sequence {name}: {e[1]} stands where the verifier in Lean does not read it yet")
            return before if e[1] == var else e
        if kind == "bin": return ("bin", e[1], put(e[2], inside), put(e[3], inside))
        if kind == "ifx": return ("ifx", put(e[1], inside), put(e[2], inside), put(e[3], inside))
        if kind == "index":
            if e[1] == ("name", h):
                if not inside: raise SystemExit(f"statement: the sequence {name}: its first value is said from itself")
                return ("call", name, [("name", p) for p in params] + [put(e[2], inside)])
            return ("index", put(e[1], inside), put(e[2], inside))
        if kind == "call": return ("call", e[1], [put(a, inside) for a in e[2]])
        raise SystemExit(f"statement: the sequence {name}: an expression of a kind the verifier in Lean does not read yet: {e!r}")
    body = ("ifx", ("bin", "==", ("name", k), ("num", 0)), put(first, False), put(nxt, True))
    return " ".join(["def", name] + params + [k, "=", sexp(body, seqs)])


def sequences(spec):
    """{a sequence's name: how many things it is of}."""
    return {name: len(seq[0]) for name, seq in spec.seqs.items()}


def contract_lines(c, name, seqs={}, consts=()):
    """A contract as the lines Reader.lean reads."""
    out = []
    names = [arg for arg, _ in c["args"]]
    if len(set(names)) != len(names): raise SystemExit(f"statement: the contract of {name} has two arguments of one name")
    # `returns r`, r no name of the specification's (LANGUAGE.md): the number returned is called r in `ensures` lines.
    r = c["returns"]
    result = r[1] if r is not None and r[0] == "name" and r[1] not in names and r[1] not in consts else None
    # A run an `ensures` speaks of is written. In the account in Lean the function may write it and never reads
    # it (which is less than the contract lets it do), and nothing is said of what the run held before.
    written = [leaf["name"] for leaf in c["leaves"]]
    if len(set(written)) != len(written): raise SystemExit(f"statement: the contract of {name} has two `ensures` of one run: the verifier in Lean does not read that yet")
    for arg, kind in c["args"]:
        m = re.fullmatch(r"(\w+) bytes", kind)
        if kind == "number" and arg not in written: out.append(f"arg {arg} number")
        elif m and not m.group(1).isdigit() and arg not in written: out.append(f"arg {arg} bytes {m.group(1)}")
        elif m and m.group(1).isdigit() and arg in written: out.append(f"arg {arg} out {int(m.group(1))}")
        else: raise SystemExit(f"statement: {name}: an argument of a kind the verifier in Lean does not read yet: {arg}: {kind}")
    for key in ("asks", "calls", "conditions", "given", "needs", "spoils"):
        if c[key]: raise SystemExit(f"statement: the contract of {name} has `{key}`, which the verifier in Lean does not read yet")
    if c["decreases"]: raise SystemExit(f"statement: the contract of {name} has a line the verifier in Lean does not read yet")
    # What is written is taken to overlap nothing else given (the account in Lean asks it of the caller), so the
    # contract must ask it of the caller too: `requires no_overlap` of every address among the arguments.
    addresses = [arg for arg, kind in c["args"] if kind != "number"]
    if written and len(addresses) > 1:
        if sorted(c["no_overlap"] or []) != sorted(addresses):
            raise SystemExit(f"statement: the contract of {name} does not say `requires no_overlap({', '.join(addresses)})`: what it writes is taken to overlap nothing else it is given")
    elif c["no_overlap"]: raise SystemExit(f"statement: the contract of {name} has `requires no_overlap`, which the verifier in Lean reads only with something written")
    # A contract promises that which instructions run and which addresses are touched do not depend on the bytes
    # in memory, but for the runs a `trace depends on` line names. The account in Lean says nothing of that: a
    # run only read must be named there. (A run written is never read in that account, so nothing depends on
    # what it held; and it is not to be named, since nothing may then depend on it.)
    quiet = [arg for arg, kind in c["args"] if kind != "number" and arg not in c["trace"] and arg not in written]
    if quiet: raise SystemExit(f"statement: the contract of {name} promises that the trace does not depend on the bytes of {', '.join(quiet)}: "
                               "the verifier in Lean does not show that yet")
    if [arg for arg in written if arg in c["trace"]]: raise SystemExit(f"statement: the contract of {name}: the trace depends on a run it writes: the verifier in Lean does not read that yet")
    if result is not None: out.append(f"result {result}")
    elif r is not None: out.append("returns " + sexp(r, seqs))
    for leaf in c["leaves"]:
        if leaf["index"] is not None or leaf["each"] is not None or leaf["cond"] is not None:
            raise SystemExit(f"statement: the contract of {name} has an `ensures` of a form the verifier in Lean does not read yet")
        count = next(int(re.fullmatch(r"(\d+) bytes", kind).group(1)) for arg, kind in c["args"] if arg == leaf["name"])
        lo, hi = leaf["part"] if leaf["part"] is not None else (("num", 0), ("num", count))
        out.append(f"ensures {leaf['name']} {sexp(lo, seqs)} {sexp(hi, seqs)} {sexp(leaf['expr'], seqs)}")
    out.append(f"stack {c['stack']}")
    return out


def called(obj, symbol):
    """The functions SYMBOL calls, by name, in the order of their first call."""
    out = []
    for _, _, text in kdecode.read(obj, symbol, 0, 0)[0]:
        m = re.fullmatch(r"\.call (\S+)", text)
        if m and m.group(1) not in out: out.append(m.group(1))
    return out


def ordered(functions):
    """The functions [(object, symbol)], each after those it calls. A function called must be among them; a
    ring of calls is refused. (Only a help to whoever asks: the verifier refuses a call of a function it has
    not shown before, whatever the order here.)"""
    obj_of = {}
    for obj, symbol in functions:
        if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9.$]*", symbol): raise SystemExit(f"statement: a function's name that is no plain name: {symbol!r}")
        if symbol in obj_of: raise SystemExit(f"statement: two functions are named {symbol}")
        obj_of[symbol] = obj
    calls = {symbol: called(obj, symbol) for obj, symbol in functions}
    out = []
    def visit(symbol, path):
        if symbol in path: raise SystemExit(f"statement: a ring of calls: {' -> '.join(path + [symbol])}")
        if symbol in out: return
        for name in calls[symbol]:
            if name not in calls: raise SystemExit(f"statement: {symbol} calls {name}, which is not among the functions to be shown")
            visit(name, path + [symbol])
        out.append(symbol)
    for _, symbol in functions: visit(symbol, [])
    return [(obj_of[symbol], symbol) for symbol in out]


def one_line(line):
    """A line of the statement is one line. (A function's name comes from the file's table of names, which is
    its maker's: a name with a line break in it would put a line of the maker's own into what is to be shown.
    The reader of code refuses such a name already, since a row's text with it is no instance of the row.)"""
    if not line or any(ch in line for ch in "\n\r\x0b\x0c\x1c\x1d\x1e\x85\u2028\u2029") or not line.isprintable():
        raise SystemExit(f"statement: a line with a line break or a character that is not printed in it: {line!r}")
    return line


def statement(spec_text, functions):
    """The lines that say what is to be shown of the functions [(object, symbol)]: each one's instructions and
    its contract, a function after those it calls; then the definitions."""
    out = []
    spec = ode.Spec(spec_text)
    seqs = sequences(spec)
    # Nothing of the specification is left out without a word: what the account in Lean has no meaning for is refused.
    for what, there in (("a layout", spec.layouts), ("a lemma", spec.lemmas), ("a kind", spec.kinds)):
        if there: raise SystemExit(f"statement: the specification has {what} ({', '.join(map(str, list(there)[:3]))}), which the verifier in Lean does not read yet")
    for obj, symbol in ordered(functions):
        out.append(f"fn {symbol}")
        rows, _ = kdecode.read(obj, symbol, 0, 0)
        for a, b, text in rows: out.append(f"i {a} {b} {text}")
        if symbol not in spec.contracts: raise SystemExit(f"statement: no contract of {symbol} in the specification")
        out += contract_lines(spec.contracts[symbol], symbol, seqs, spec.consts)
    out += definitions(spec_text)
    return [one_line(l) for l in out]


def functions_of(words):
    """OBJECT:SYMBOL words as [(object, symbol)]."""
    out = []
    for w in words:
        obj, _, symbol = w.rpartition(":")
        if not obj or not symbol: raise SystemExit(f"statement: {w}: write OBJECT:SYMBOL")
        out.append((obj, symbol))
    return out


if __name__ == "__main__":
    if len(sys.argv) < 4: raise SystemExit(__doc__)
    spec, out = sys.argv[1:3]
    with open(spec) as f: lines = statement(f.read(), functions_of(sys.argv[3:]))
    with open(out, "w") as f: f.write("\n".join(lines) + "\n")
