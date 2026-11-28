#!/usr/bin/env python3
"""statement: what is to be shown of functions, for the verifier in Lean (Core.lean). RELIED ON.

    python3 statement.py SPEC OUT.statement OBJECT:SYMBOL [OBJECT:SYMBOL …]

Each function's instructions as ../kcheck/kdecode.py reads them from its OBJECT's bytes by the table (an
object file for AArch64: as ../arm64/obj.py reads them by ../arm64/arm64.tab, and the function's lines say
`machine arm64`), the contract of each SYMBOL in SPEC and the definitions of SPEC as ../kcheck/ode.py reads
them, written as the lines Main.lean reads. A contract or a definition with anything the verifier in Lean does not read yet is
refused here: no line of a contract is left out. A function is written after those it calls (the verifier
takes a call only by the contract of a function it has shown before). The theorem in SoundTop.lean is about
what these lines say; that they say what the files' bytes and the specification's text say rests on this
file and the two it reads with."""
import os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "kcheck"))
sys.path.insert(0, os.path.join(HERE, "..", "arm64"))
import kdecode, ode
import obj as arm64_obj


def arm64(path):
    """Is the object file one for AArch64?"""
    return arm64_obj.machine(path) == "arm64"


# The table of instructions each machine's functions are read by, here and by the verifier.
TABLES = {"x86-64": os.path.join(HERE, "..", "core", "x86.tab"), "arm64": os.path.join(HERE, "..", "arm64", "arm64.tab")}


def table_of(lines):
    """The table the verifier is given with a statement: AArch64's where its functions say `machine arm64`,
    else x86-64's. (A statement's functions are all for one machine: `statement` refuses any other.)"""
    return TABLES["arm64" if "machine arm64" in lines else "x86-64"]


def table_for(path):
    """The same, of a statement in a file."""
    with open(path) as f: return table_of(f.read().split("\n"))


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
    if kind == "bin":
        if e[1] == "&&": return f"(ifx {go(e[2])} {go(e[3])} (bin == (num 0) (num 1)))"
        if e[1] == "||": return f"(ifx {go(e[2])} (bin == (num 0) (num 0)) {go(e[3])})"
        return f"(bin {e[1]} {go(e[2])} {go(e[3])})"
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
    # A sequence's value at a place that is a number, used more than once (`s[7][i] ^ s[7][i + 8]`), is had
    # once, by a `let` around the whole (the name `s.7` is none a specification can write). So where the
    # sequence is of the definition's own things alone: they are given before anything else. (The value is
    # then asked for even where no use of it would have been reached: the definition has no fewer values
    # for that in ../kcheck/ode.py than here, and where it has none here nothing is shown.)
    for s in local:
        if not set(things) <= set(params): continue
        head = "(call " + " ".join([f"{name}.{s}"] + [f"(name {x})" for x in things]) + " (num "
        for k in sorted({int(part.split(")")[0]) for part in text.split(head)[1:]}):
            use = f"{head}{k}))"
            if text.count(use) > 1: text = f"(let {s}.{k} {use} " + text.replace(use, f"(name {s}.{k})") + ")"
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


# The kinds of argument that say how a value lies in a register or in memory (LANGUAGE.md), as the account in
# Lean has them: (the line's kind, or None for a register; the bytes; what the argument's name stands for in
# the contract's expressions, of the name as the account has it: a number, or a run's bytes).
WORDS = lambda x: ("call", "words", [x])
KINDS = {"cv": (32, WORDS),                                        # eight words: 32 bytes, the lowest byte of a word first
         "block": (64, WORDS),                                     # sixteen words
         "counter": (None, lambda x: ("call", "counter", [x])),    # a register: 64 bits as a counter
         "low byte": (None, lambda x: ("bin", "%", x, ("num", 256))),   # a register: its low byte, the rest being anything
         "low word": (None, lambda x: ("bin", "%", x, ("num", 2 ** 32))),   # a register: its low 32 bits, the rest being anything
         "word": (None, lambda x: x),                              # a register: a number the caller keeps below 2^32 (BOUNDS)
         "byte": (None, lambda x: x)}                              # a register: a number the caller keeps below 256 (BOUNDS)
BOUNDS = {"word": 2 ** 32, "byte": 256}                            # the kinds that ask something of the caller: the number is below this


def no_value(arg, why="is of the kind `any`"):
    """An argument of the kind `any` is a register of which the contract says nothing: no expression speaks of it."""
    def refuse(x): raise SystemExit(f"statement: the argument {arg} {why}: an expression cannot speak of it")
    return refuse


def layout_kind(arg, kind, lay):
    """An argument that is the address of a record laid out as `layout KIND BYTES { FIELD: KIND at OFFSET … }`
    says (../kcheck/ode.py has seen that the fields lie within the record and do not overlap): how many bytes
    the record is; the record, as an expression of the bytes at the address; and the lines that say what the
    layout asks of the numbers in it. A field of chaining-value kind is eight words; one of so many bytes is
    those bytes; a `number` is the eight bytes there as one number, the lowest byte first, below what
    `below` says; a `byte` is such a number below 256."""
    fields, lines = [], []
    part = lambda at, n: ("slice", ("name", arg), ("num", at), ("num", at + n))
    for field, f in lay["fields"].items():
        m = re.fullmatch(r"(\d+) bytes", f["kind"])
        if f["count"] is not None: raise SystemExit(f"statement: the layout {kind} has a field that is several things ({field}): the verifier in Lean does not read that yet")
        if f["below"] is not None and f["kind"] not in ("number", "byte"):
            raise SystemExit(f"statement: the layout {kind} says `below` of a field that is no number ({field})")
        if f["kind"] == "cv": x = ("call", "words", [part(f["at"], 32)])
        elif m: x = part(f["at"], int(m.group(1)))
        elif f["kind"] in ("number", "byte"):
            x = ("call", "number.le", [part(f["at"], 8)])
            below = number_bound(f)
            if below < 2 ** 64: lines.append(f"mbelow {arg} {f['at']} {below}")
        else: raise SystemExit(f"statement: the layout {kind} has a field of a kind the verifier in Lean does not read yet: {field}: {f['kind']}")
        fields.append((field, x))
    return lay["size"], (lambda x: ("record", fields)), lines


def number_bound(f):
    """What a field that is a number must be below: 2^64 (it is eight bytes); 256 where it is a `byte`; and
    what the layout says with `below`. The least of them."""
    return min([2 ** 64] + ([256] if f["kind"] == "byte" else []) + ([f["below"]] if f["below"] is not None else []))


def record_words(kind, lay, e, name):
    """The words of a record laid out as `layout KIND …`, of the record e as a value (an expression): its
    fields' words, one field after another. The fields must lie one after another and fill the record. A
    field of chaining-value kind is its eight words; one of so many bytes, a multiple of four, is the words
    of those bytes; a `number` or a `byte` is the two words of its eight bytes, the low word first, where
    the number is below what the layout asks (`number_bound`). Where it is not below that, the expression
    has no value: no record of the layout holds such a number, so the `ensures` is false."""
    at, parts = 0, []
    for field, f in sorted(lay["fields"].items(), key=lambda item: item[1]["at"]):
        m = re.fullmatch(r"(\d+) bytes", f["kind"])
        if f["count"] is not None or f["at"] != at:
            raise SystemExit(f"statement: the contract of {name} writes a record of the layout {kind}, whose fields do not lie one after another, each one thing: not read yet")
        if f["below"] is not None and f["kind"] not in ("number", "byte"):
            raise SystemExit(f"statement: the layout {kind} says `below` of a field that is no number ({field})")
        none = ("index", ("list", [("num", 0)]), ("num", 1))          # (the place 1 of a list of one thing: no value)
        if f["kind"] == "cv":
            x = ("field", e, field)
            parts.append(("ifx", ("bin", "==", ("call", "len", [x]), ("num", 8)), x, none)); at += 32
        elif m and int(m.group(1)) % 4 == 0:
            nbytes = int(m.group(1))
            x = ("field", e, field)
            parts.append(("ifx", ("bin", "==", ("call", "len", [x]), ("num", nbytes)), ("call", "words", [x]), none)); at += nbytes
        elif f["kind"] in ("number", "byte"):
            bound = number_bound(f)
            x = ("field", e, field)
            words = ("list", [("call", "lo", [("call", "counter", [x])]), ("call", "hi", [("call", "counter", [x])])])
            parts.append(("ifx", ("bin", "<", x, ("num", bound)), words, none)); at += 8
        else: raise SystemExit(f"statement: the contract of {name} writes a record of the layout {kind} with a field of a kind the verifier in Lean does not read there yet: {field}: {f['kind']}")
    if at != lay["size"] or not parts: raise SystemExit(f"statement: the contract of {name} writes a record of the layout {kind}, whose fields do not fill it: not read yet")
    joined = parts[-1]
    for x in reversed(parts[:-1]): joined = ("bin", "++", x, joined)
    return joined


def named_bytes(arg, names):
    """An argument of the kind `bytes a b c d` is a number in a register; a, b, c, d name the four low bytes of
    it, the lowest first, and of the four bytes above them nothing is said. What each name stands for, said
    of the register's number x: x % 256; x % 2^32 / 2^8 % 256; x % 2^32 / 2^16 % 256; x % 2^32 / 2^24.
    (Each is that byte whatever the form; these are the forms in which a function that moves the register's
    low half and shifts it comes to the bytes, so that the verifier meets the same numbers.)"""
    if len(names) != 4 or len(set(names + [arg])) != 5: raise SystemExit(f"statement: the argument {arg} names its bytes twice, or not four of them")
    x = ("name", arg)
    low = ("bin", "%", x, ("num", 2 ** 32))
    byte = lambda e: ("bin", "%", e, ("num", 256))
    part = lambda k: ("bin", "/", low, ("num", 2 ** (8 * k)))
    return dict(zip(names, [byte(x), byte(part(1)), byte(part(2)), part(3)]))


def with_number(e, var, k, name):
    """The expression with the number k for the name var. (The forms `by_kind` reads.)"""
    if e[0] == "name": return ("num", k) if e[1] == var else e
    if e[0] == "num": return e
    if e[0] == "bin": return ("bin", e[1], with_number(e[2], var, k, name), with_number(e[3], var, k, name))
    if e[0] == "call": return ("call", e[1], [with_number(a, var, k, name) for a in e[2]])
    if e[0] == "list": return ("list", [with_number(a, var, k, name) for a in e[1]])
    if e[0] == "index": return ("index", with_number(e[1], var, k, name), with_number(e[2], var, k, name))
    raise SystemExit(f"statement: the contract of {name}: an `ensures` of each of some values with an expression of this form is not read yet: {e!r}")


def by_kind(e, kinds, name):
    """The expression with each argument's name replaced by what its kind makes it stand for. (`kinds`: for
    each such argument, the function that says what its name stands for.)"""
    if e[0] == "name": return kinds[e[1]](e) if e[1] in kinds else e
    if e[0] == "num": return e
    if e[0] == "bin": return ("bin", e[1], by_kind(e[2], kinds, name), by_kind(e[3], kinds, name))
    if e[0] == "call": return ("call", e[1], [by_kind(a, kinds, name) for a in e[2]])
    if e[0] == "list": return ("list", [by_kind(a, kinds, name) for a in e[1]])
    if e[0] == "index": return ("index", by_kind(e[1], kinds, name), by_kind(e[2], kinds, name))
    if e[0] == "slice": return ("slice", by_kind(e[1], kinds, name), by_kind(e[2], kinds, name), by_kind(e[3], kinds, name))
    if e[0] == "field":
        # (a field of an argument that is a record: that field's own expression, so that the record's other
        # fields are not worked out; each field of such a record has a value, so nothing is lost)
        inner = by_kind(e[1], kinds, name)
        if inner[0] == "record" and [x for field, x in inner[1] if field == e[2]]:
            return [x for field, x in inner[1] if field == e[2]][0]
        return ("field", inner, e[2])
    if e[0] == "record": return ("record", [(field, by_kind(x, kinds, name)) for field, x in e[1]])
    # (a form that gives a name, a `let` or a list made thing by thing, could give an argument's name again)
    raise SystemExit(f"statement: the contract of {name}: beside arguments whose names stand for words, counters or records "
                     f"an expression of this form is not read yet: {e!r}")


def kinds_of(c, name, layouts={}):
    """The names of a contract that stand for something other than a register's number or a run's bytes:
    for each, the function that says what it stands for, of the name as the account in Lean has it (`by_kind`).
    An argument of a kind that says how a value lies in a register or in memory (KINDS); a record in memory
    (a layout); the four bytes an argument of the kind `bytes a b c d` names."""
    laid = {arg: layout_kind(arg, kind, layouts[kind]) for arg, kind in c["args"] if kind in layouts}
    kinds = {arg: KINDS[kind][1] for arg, kind in c["args"] if kind in KINDS}
    kinds.update({arg: laid[arg][1] for arg in laid})
    kinds.update({arg: no_value(arg) for arg, kind in c["args"] if kind == "any"})
    names = [arg for arg, _ in c["args"]]
    if len(set(names)) != len(names): raise SystemExit(f"statement: the contract of {name} has two arguments of one name")
    packed = {arg: kind.split()[1:] for arg, kind in c["args"] if re.fullmatch(r"bytes( \w+)+", kind)}
    for arg, parts in packed.items():
        for part, e in named_bytes(arg, parts).items():
            if part in names or part in kinds: raise SystemExit(f"statement: the contract of {name} gives the name {part} twice")
            kinds[part] = (lambda e: lambda x: e)(e)
        kinds[arg] = no_value(arg, "is a number of which only four bytes are named")
    return kinds


def linear_expr(e, num_args):
    """Parse a linear integer combination of number parameters: returns (const, {name: coeff}) or None."""
    if e[0] == "num": return (e[1], {})
    if e[0] == "name" and e[1] in num_args: return (0, {e[1]: 1})
    if e[0] == "bin" and e[1] in ("+", "-"):
        a, b = linear_expr(e[2], num_args), linear_expr(e[3], num_args)
        if a is None or b is None: return None
        sign = 1 if e[1] == "+" else -1
        c = dict(a[1])
        for k, v in b[1].items(): c[k] = c.get(k, 0) + sign * v
        return (a[0] + sign * b[0], c)
    if e[0] == "bin" and e[1] == "*":
        a, b = linear_expr(e[2], num_args), linear_expr(e[3], num_args)
        if a is None or b is None: return None
        if not a[1]: return (a[0] * b[0], {k: a[0] * v for k, v in b[1].items()})
        if not b[1]: return (b[0] * a[0], {k: b[0] * v for k, v in a[1].items()})
    return None


def stack_bits_spec(e, num_args):
    """Parse `BASE + STEP * bits((ARG - SUB) / DIV)` (with optional `- SUB` and `/ DIV`), or None."""
    if not (e[0] == "bin" and e[1] == "+" and e[2][0] == "num" and e[2][1] >= 0): return None
    base = e[2][1]
    rhs = e[3]
    if not (rhs[0] == "bin" and rhs[1] == "*" and rhs[2][0] == "num" and rhs[2][1] >= 0): return None
    step = rhs[2][1]
    call = rhs[3]
    if not (call[0] == "call" and call[1] == "bits" and len(call[2]) == 1): return None
    inner = call[2][0]
    sub, div = 0, 1
    if inner[0] == "bin" and inner[1] == "/" and inner[3][0] == "num" and inner[3][1] > 0:
        div = inner[3][1]
        inner = inner[2]
    if inner[0] == "bin" and inner[1] == "-" and inner[3][0] == "num" and inner[3][1] >= 0:
        sub = inner[3][1]
        inner = inner[2]
    if inner[0] == "name" and inner[1] in num_args:
        return (base, step, inner[1], sub, div)
    return None


def stack_lin_spec(e, num_args):
    """Parse `BASE + STEP * ((ARG - SUB) / DIV)` (with optional `- SUB` and `/ DIV`), or None."""
    if not (e[0] == "bin" and e[1] == "+" and e[2][0] == "num" and e[2][1] >= 0): return None
    base = e[2][1]
    rhs = e[3]
    if not (rhs[0] == "bin" and rhs[1] == "*" and rhs[2][0] == "num" and rhs[2][1] >= 0): return None
    step = rhs[2][1]
    inner = rhs[3]
    sub, div = 0, 1
    if inner[0] == "bin" and inner[1] == "/" and inner[3][0] == "num" and inner[3][1] > 0:
        div = inner[3][1]
        inner = inner[2]
    if inner[0] == "bin" and inner[1] == "-" and inner[3][0] == "num" and inner[3][1] >= 0:
        sub = inner[3][1]
        inner = inner[2]
    if inner[0] == "name" and inner[1] in num_args:
        return (base, step, inner[1], sub, div)
    return None


_X86_GPRS = frozenset(["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"])
_ARM64_GPRS = frozenset([f"x{i}" for i in range(31)] + ["sp"])
_X86_VECS = frozenset([f"{p}{i}" for p in ("xmm", "ymm") for i in range(16)] + [f"zmm{i}" for i in range(32)])
_ARM64_VECS = frozenset([f"v{i}" for i in range(32)])


def _vec_num(vname):
    return int(vname[3:] if vname.startswith(("xmm", "ymm", "zmm")) else vname[1:])


def _calling_lines(cc, name, arg_names, ret_expr, result_name, is_arm64):
    """Validate an optional `calling { ... }` block and emit `argregs`/`retreg`/`keeps`/`keepsvec`."""
    if cc is None:
        return []
    gprs = _ARM64_GPRS if is_arm64 else _X86_GPRS
    vecs = _ARM64_VECS if is_arm64 else _X86_VECS
    arch = "AArch64" if is_arm64 else "x86-64"
    forbidden = {"sp", "x30"} if is_arm64 else {"rsp"}

    def check_gpr(reg, role):
        if reg not in gprs:
            raise SystemExit(f"statement: the contract of {name}: calling `{role}` register {reg!r} is not an {arch} general register")
        if reg in forbidden:
            raise SystemExit(f"statement: the contract of {name}: calling `{role}` cannot use reserved register {reg!r}")

    out = []
    if cc["in"] is not None:
        assigned = cc["in"]
        extra = [p for p in assigned if p not in arg_names]
        if extra:
            raise SystemExit(f"statement: the contract of {name}: calling `in` assigns unknown parameter(s): {', '.join(extra)}")
        missing = [p for p in arg_names if p not in assigned]
        if missing:
            raise SystemExit(f"statement: the contract of {name}: calling `in` must assign every parameter (missing: {', '.join(missing)})")
        regs = [assigned[p] for p in arg_names]
        seen = set()
        for reg in regs:
            check_gpr(reg, "in")
            if reg in seen:
                raise SystemExit(f"statement: the contract of {name}: calling `in` uses register {reg!r} more than once")
            seen.add(reg)
        out.append("argregs" + (" " + " ".join(regs) if regs else ""))

    if cc["out"] is not None:
        if result_name is not None:
            raise SystemExit(f"statement: the contract of {name}: calling `out` cannot be used with abstract `returns {result_name}`")
        if ret_expr is None:
            raise SystemExit(f"statement: the contract of {name}: calling `out` requires a `returns EXPR` clause")
        check_gpr(cc["out"], "out")
        out.append(f"retreg {cc['out']}")

    if cc["preserves"] is not None:
        seen = set()
        for reg in cc["preserves"]:
            check_gpr(reg, "preserves")
            if reg in seen:
                raise SystemExit(f"statement: the contract of {name}: calling `preserves` lists register {reg!r} more than once")
            seen.add(reg)
        out.append("keeps" + (" " + " ".join(cc["preserves"]) if cc["preserves"] else ""))

    if ret_expr is not None or result_name is not None:
        eff_ret = cc["out"] if cc["out"] is not None else ("x0" if is_arm64 else "rax")
        eff_keeps = cc["preserves"] if cc["preserves"] is not None else (
            [f"x{i}" for i in range(19, 30)] if is_arm64 else ["rbx", "rbp", "r12", "r13", "r14", "r15"]
        )
        if eff_ret in eff_keeps:
            raise SystemExit(f"statement: the contract of {name}: calling `out` register {eff_ret!r} cannot also be in `preserves`")

    if cc["preserves_vec"] is not None:
        seen_idx = set()
        for vreg in cc["preserves_vec"]:
            if vreg not in vecs:
                raise SystemExit(f"statement: the contract of {name}: calling `preserves_vec` register {vreg!r} is not an {arch} vector register")
            idx = _vec_num(vreg)
            if idx in seen_idx:
                raise SystemExit(f"statement: the contract of {name}: calling `preserves_vec` lists vector register {idx} more than once ({vreg!r})")
            seen_idx.add(idx)
        out.append("keepsvec" + (" " + " ".join(cc["preserves_vec"]) if cc["preserves_vec"] else ""))

    return out


def contract_lines(c, name, seqs={}, consts=(), layouts={}, is_arm64=False):
    """A contract as the lines Reader.lean reads."""
    out = []
    # the arguments whose names stand for something other than the register's number or the run's bytes: each
    # with how many bytes lie at it (None: it is in a register) and what its name stands for
    laid = {arg: layout_kind(arg, kind, layouts[kind]) for arg, kind in c["args"] if kind in layouts}
    sizes = {arg: KINDS[kind][0] for arg, kind in c["args"] if kind in KINDS}
    sizes.update({arg: laid[arg][0] for arg in laid})
    sizes.update({arg: None for arg, kind in c["args"] if kind == "any"})
    kinds = kinds_of(c, name, layouts)
    names = [arg for arg, _ in c["args"]]
    # `N inputs`: the address of a table of N addresses, each of n blocks of 64 bytes given to read (n: the
    # argument of that name, a number). `N cvs`: the address of N chaining values, one after another.
    # `bytes a b c d`: a number in a register whose four low bytes those names stand for.
    tables = {arg: int(kind.split()[0]) for arg, kind in c["args"] if re.fullmatch(r"\d+ inputs", kind)}
    values = {arg: int(kind.split()[0]) for arg, kind in c["args"] if re.fullmatch(r"\d+ cvs", kind)}
    packed = {arg: kind.split()[1:] for arg, kind in c["args"] if re.fullmatch(r"bytes( \w+)+", kind)}
    if tables and dict(c["args"]).get("n") != "number": raise SystemExit(f"statement: the contract of {name} has a table of inputs and no number n of their blocks")
    sizes.update({arg: 8 * count for arg, count in tables.items()})
    sizes.update({arg: 32 * count for arg, count in values.items()})
    sizes.update({arg: None for arg in packed})
    sizes.update({arg: int(kind.split()[0]) for arg, kind in c["args"] if re.fullmatch(r"\d+ bytes", kind)})
    said = sorted({kind for arg, kind in c["args"] if arg in kinds})     # (for messages)
    # `returns r`, r no name of the specification's (LANGUAGE.md): the number returned is called r in `ensures` lines.
    r = c["returns"]
    result = r[1] if r is not None and r[0] == "name" and r[1] not in names and r[1] not in consts else None
    # A run an `ensures` speaks of is written. In the account in Lean the function may write it and never reads
    # it (which is less than the contract lets it do), and nothing is said of what the run held before.
    written = [leaf["name"] for leaf in c["leaves"]]
    if len(set(written)) != len(written): raise SystemExit(f"statement: the contract of {name} has two `ensures` of one run: the verifier in Lean does not read that yet")
    # A written `N bytes` (N % 4 == 0) whose ensures is `bytes_of(...)` is treated as word-level (`inout` + `ensuresw`),
    # matching `cv` and allowing callees like `compress_in_place` to read back bytes the function wrote to `out`.
    word_out_bytes = {
        leaf["name"] for leaf in c["leaves"]
        if leaf["index"] is None and leaf["each"] is None and leaf["cond"] is None and leaf["part"] is None
        and leaf["name"] not in kinds and leaf["name"] not in laid and leaf["name"] not in values
        and leaf["expr"][0] == "call" and leaf["expr"][1] == "bytes_of"
        and any(arg == leaf["name"] and re.fullmatch(r"\d+ bytes", kind) and int(kind.split()[0]) % 4 == 0
                for arg, kind in c["args"])
    }
    num_args = {arg for arg, kind in c["args"] if kind == "number"}
    given_map = {}
    for g in c["given"]:
        gn, gi, geach = g["name"], g["index"], g["each"]
        if gn in given_map:
            raise SystemExit(f"statement: the contract of {name} has two `requires {gn}[i] == ...` clauses")
        if dict(c["args"]).get(gn) != "cvs" or gn in written:
            raise SystemExit(f"statement: the contract of {name} has `requires {gn}[i] == ...` on an argument that is not a read-only `cvs`")
        if not (geach[0] == ("num", 0) and geach[1][0] == "bin" and geach[1][1] == "/"
                and geach[1][2][0] == "name" and geach[1][2][1] in num_args
                and geach[1][3][0] == "num" and geach[1][3][1] > 0):
            raise SystemExit(f"statement: the contract of {name} has a `requires {gn}[i] == ...` range the verifier in Lean does not read yet")
        if gi in names or gi in kinds:
            raise SystemExit(f"statement: the contract of {name}: `requires {gn}[{gi}] == ...` reuses an argument name")
        given_map[gn] = (geach[1][2][1], geach[1][3][1], g)
    for arg, kind in c["args"]:
        m = re.fullmatch(r"(\w+) bytes", kind)
        if kind == "number" and arg not in written: out.append(f"arg {arg} number")
        elif m and not m.group(1).isdigit() and arg not in written: out.append(f"arg {arg} bytes {m.group(1)}")
        elif m and m.group(1).isdigit() and arg in word_out_bytes: out.append(f"arg {arg} inout {int(m.group(1))}")
        elif m and m.group(1).isdigit() and arg in written: out.append(f"arg {arg} out {int(m.group(1))}")
        elif m and m.group(1).isdigit() and arg not in written: out.append(f"arg {arg} fixed {int(m.group(1))}")
        elif arg in tables and arg not in written: out += [f"arg {arg} fixed {8 * tables[arg]}", f"lanes {arg} n"]
        elif arg in values and arg in written: out.append(f"arg {arg} out {32 * values[arg]}")
        elif kind == "cvs" and arg not in written:
            if arg not in given_map:
                raise SystemExit(f"statement: the contract of {name} has `cvs` argument {arg} without `requires {arg}[i] == ...`")
            len_arg, ch, _ = given_map[arg]
            out.append(f"arg {arg} valarray {len_arg} {ch} 32")
        elif arg in packed and arg not in written: out.append(f"arg {arg} number")
        # a run of words: read and written where an `ensures` speaks of it, only read where none does
        elif kind in KINDS and KINDS[kind][0] is not None: out.append(f"arg {arg} {'inout' if arg in written else 'fixed'} {KINDS[kind][0]}")
        # a record in memory: read and written where an `ensures` speaks of it, only read where none does
        elif arg in laid: out.append(f"arg {arg} {'inout' if arg in written else 'fixed'} {laid[arg][0]}")
        elif (kind in KINDS or kind == "any") and arg not in written: out.append(f"arg {arg} number")
        else: raise SystemExit(f"statement: {name}: an argument of a kind the verifier in Lean does not read yet: {arg}: {kind}")
    for arg, kind in c["args"]:
        if kind in BOUNDS: out.append(f"below {arg} {BOUNDS[kind]}")
        # (what a layout asks of the numbers in a record is asked at entry of a record that is only read; of
        # one that is written it is part of what `ensures` says: `record_words`)
        if arg in laid and arg not in written: out += laid[arg][2]
    in_register = lambda arg: arg in sizes and sizes[arg] is None or dict(c["args"])[arg] == "number"
    for what, more in c["needs"]:
        if not re.fullmatch(r"[a-z0-9]+", what): raise SystemExit(f"statement: the contract of {name} has a `needs` line the verifier in Lean does not read yet")
        if more is None: out.append(f"needs {what}")
        # `needs avx512 if plat == 5`: on the condition that an argument in a register is a number
        elif (more[0] == "bin" and more[1] == "==" and more[2][0] == "name" and more[2][1] in names and in_register(more[2][1])
              and more[3][0] == "num" and 0 <= more[3][1] < 2 ** 64): out.append(f"needsif {what} {more[2][1]} {more[3][1]}")
        else: raise SystemExit(f"statement: the contract of {name} has a `needs` line with a condition the verifier in Lean does not read yet")
    for e in c["asks"]:
        # `requires NAME >= K`, `requires NAME < K`: what the caller sees to, of a number in a register
        # (`NAME <= K` is `NAME < K + 1`)
        if (e[0] == "bin" and e[1] in (">=", "<") and e[2][0] == "name" and dict(c["args"]).get(e[2][1]) == "number"
                and e[3][0] == "num" and 0 <= e[3][1] < 2 ** 64): out.append(f"{'atleast' if e[1] == '>=' else 'below'} {e[2][1]} {e[3][1]}")
        elif (e[0] == "bin" and e[1] == "<=" and e[2][0] == "name" and dict(c["args"]).get(e[2][1]) == "number"
                and e[3][0] == "num" and 0 <= e[3][1] < 2 ** 64 - 1): out.append(f"below {e[2][1]} {e[3][1] + 1}")
        elif (e[0] == "bin" and e[1] == "<=" and e[2][0] == "bin" and e[2][1] == "+"
                and e[2][2][0] == "bin" and e[2][2][1] == "*"
                and e[2][2][2][0] == "num" and e[2][2][2][1] > 0
                and e[2][2][3][0] == "name" and dict(c["args"]).get(e[2][2][3][1]) == "number"
                and e[2][3][0] == "num" and e[3][0] == "num"
                and 0 <= e[2][3][1] <= e[3][1] and (e[3][1] - e[2][3][1]) // e[2][2][2][1] < 2 ** 64 - 1):
            out.append(f"below {e[2][2][3][1]} {(e[3][1] - e[2][3][1]) // e[2][2][2][1] + 1}")
        elif e[0] == "bin" and e[1] == "==":
            la, lb = linear_expr(e[2], num_args), linear_expr(e[3], num_args)
            if la is None or lb is None:
                raise SystemExit(f"statement: the contract of {name} has a `requires` the verifier in Lean does not read yet")
            for k, cs in (
                (lb[0] - la[0], {a: lb[1].get(a, 0) - la[1].get(a, 0) for a in set(la[1]) | set(lb[1])}),
                (la[0] - lb[0], {a: la[1].get(a, 0) - lb[1].get(a, 0) for a in set(la[1]) | set(lb[1])}),
            ):
                pairs = " ".join(f"{a} {cs[a]}" for a, _ in c["args"] if cs.get(a, 0) != 0)
                out.append(f"linpre {k}" + (f" {pairs}" if pairs else ""))
        elif e[0] == "bin" and e[1] in ("<=", "<", ">=", ">"):
            la, lb = linear_expr(e[2], num_args), linear_expr(e[3], num_args)
            if la is None or lb is None:
                raise SystemExit(f"statement: the contract of {name} has a `requires` the verifier in Lean does not read yet")
            if e[1] in ("<=", "<"):
                k = lb[0] - la[0] - (1 if e[1] == "<" else 0)
                cs = {a: lb[1].get(a, 0) - la[1].get(a, 0) for a in set(la[1]) | set(lb[1])}
            else:
                k = la[0] - lb[0] - (1 if e[1] == ">" else 0)
                cs = {a: la[1].get(a, 0) - lb[1].get(a, 0) for a in set(la[1]) | set(lb[1])}
            pairs = " ".join(f"{a} {cs[a]}" for a, _ in c["args"] if cs.get(a, 0) != 0)
            out.append(f"linpre {k}" + (f" {pairs}" if pairs else ""))
        else: raise SystemExit(f"statement: the contract of {name} has a `requires` the verifier in Lean does not read yet")
    for key in ("calls", "conditions", "spoils"):
        if c[key]: raise SystemExit(f"statement: the contract of {name} has `{key}`, which the verifier in Lean does not read yet")
    if c["decreases"]:
        if c["decreases"][0] == "name" and c["decreases"][1] in num_args:
            out.append(f"fndecreases {c['decreases'][1]}")
        else:
            raise SystemExit(f"statement: the contract of {name} has a `decreases` line the verifier in Lean does not read yet")
    # What is written is taken to overlap nothing else given (the account in Lean asks it of the caller), so the
    # contract must ask it of the caller too: `requires no_overlap` (or `requires line_disjoint`) of every address among the arguments.
    addresses = [arg for arg, kind in c["args"] if not in_register(arg)]
    ld_clauses = c.get("line_disjoint") or []
    ld_covers_all = any(sorted(bufs) == sorted(addresses) for bufs, _ in ld_clauses)
    if written and len(addresses) > 1:
        if sorted(c["no_overlap"] or []) != sorted(addresses) and not ld_covers_all:
            raise SystemExit(f"statement: the contract of {name} does not say `requires no_overlap({', '.join(addresses)})`: what it writes is taken to overlap nothing else it is given")
    elif c["no_overlap"]: raise SystemExit(f"statement: the contract of {name} has `requires no_overlap`, which the verifier in Lean reads only with something written")
    for aname, al in (c.get("aligns") or []):
        if aname not in addresses:
            raise SystemExit(f"statement: the contract of {name} has `requires aligned({aname}, {al})`, but `{aname}` is not a buffer parameter")
        if al not in (8, 16, 32, 64, 128, 4096, 16384):
            raise SystemExit(f"statement: the contract of {name} has invalid alignment {al} for `{aname}`")
        out.append(f"align {aname} {al}")
    seen_ld = set()
    for bufs, line_sz in ld_clauses:
        if line_sz not in (64, 128):
            raise SystemExit(f"statement: the contract of {name} has invalid `line_disjoint` line size {line_sz}")
        if len(set(bufs)) != len(bufs):
            raise SystemExit(f"statement: the contract of {name} lists a buffer twice in `requires line_disjoint(...)`")
        for b in bufs:
            if b not in addresses:
                raise SystemExit(f"statement: the contract of {name} has `requires line_disjoint(...)` naming `{b}`, which is not a buffer parameter")
        for i in range(len(bufs)):
            for j in range(i + 1, len(bufs)):
                pair = (bufs[i], bufs[j], line_sz)
                if pair not in seen_ld:
                    seen_ld.add(pair)
                    out.append(f"linedisjoint {bufs[i]} {bufs[j]} {line_sz}")
    # A contract promises that which instructions run and which addresses are touched depend on nothing it is
    # given, but for what a `trace depends on` line names: not on the bytes of a run, and not on a number in a
    # register. In the account in Lean the bytes of a run given to read are not marked (nothing secret), but
    # for a run that a `hidden` line names; and the register of a number given is not marked, but for a number
    # that a `hidden` line names. So a run that is only read, and a number, that `trace depends on` does not
    # name is `hidden`.
    # (An address is never hidden: the function reads or writes there, so it shows. The addresses a table holds
    # are numbers given and read as addresses: a table is never hidden. Of a run that is written nothing is
    # asked: what is read of it is taken as marked.)
    for arg in c["trace"]:
        if arg not in names: raise SystemExit(f"statement: the contract of {name}: `trace depends on {arg}`, and {arg} is no argument")
    out += [f"hidden {arg}" for arg, kind in c["args"] if not in_register(arg) and arg not in c["trace"] and arg not in written and arg not in tables]
    out += [f"hidden {arg}" for arg, kind in c["args"] if in_register(arg) and arg not in c["trace"]]
    if [arg for arg in written if arg in c["trace"] and arg not in kinds]: raise SystemExit(f"statement: the contract of {name}: the trace depends on a run it writes: the verifier in Lean does not read that yet")
    if r is not None and kinds: raise SystemExit(f"statement: the contract of {name} returns a number beside arguments of the kinds {', '.join(said)}: not read yet")
    # A name in an expression of the contract that is no argument's and is a constant of the specification is
    # that constant (as in a definition).
    scope = Scope(consts, frozenset(names) | frozenset(kinds))
    for g in c["given"]:
        out.append(f"valspec {g['name']} {g['index']} " + sexp(by_kind(g["expr"], kinds, name), seqs, scope.with_name(g["index"])))
    for te in c.get("trace_exprs", []):
        out.append("traceexpr " + sexp(te, seqs, scope))
    if c.get("result_dep") is not None:
        if result is None:
            raise SystemExit(f"statement: the contract of {name} has `result depends on`, which applies only to `returns NAME` with no expression")
        for arg in c["result_dep"]:
            if arg not in names:
                raise SystemExit(f"statement: the contract of {name}: `result depends on {arg}`, and {arg} is no argument")
        res_allow = set(c["trace"]) | set(c["result_dep"])
        res_hidden = [arg for arg, _ in c["args"] if not in_register(arg) and arg not in res_allow and arg not in written and arg not in tables]
        res_hidden += [arg for arg, _ in c["args"] if in_register(arg) and arg not in res_allow]
        out.append("resultdep" + (" " + " ".join(res_hidden) if res_hidden else ""))
    if result is not None: out.append(f"result {result}")
    elif r is not None: out.append("returns " + sexp(r, seqs, scope))
    for leaf in c["leaves"]:
        if leaf["name"] in values and leaf["index"] is not None and leaf["cond"] is None and leaf["part"] is None:
            # `ensures NAME[i] = E for i in 0..N`, NAME being N chaining values: for each k from 0 to N - 1, the
            # 32 bytes of the value of number k (from byte 32 * k of the run on) are those of the words of E
            # with k for i. One line a value: `ensuresw NAME FIRST COUNT …`, a part of the run.
            count, var = values[leaf["name"]], leaf["index"]
            if leaf["each"] != (("num", 0), ("num", count)) or var in names or var in kinds:
                raise SystemExit(f"statement: the contract of {name} has an `ensures` of each of some values that is not of all of them, or counts by a name given before")
            for k in range(count):
                e = by_kind(with_number(leaf["expr"], var, k, name), kinds, name)
                out.append(f"ensuresw {leaf['name']} {32 * k} 32 " + sexp(("call", "bytes_of", [e]), seqs, scope))
            continue
        if leaf["index"] is not None or leaf["each"] is not None or leaf["cond"] is not None:
            raise SystemExit(f"statement: the contract of {name} has an `ensures` of a form the verifier in Lean does not read yet")
        if leaf["name"] in laid:
            # a whole record: its bytes are those of its fields' words, one field after another
            if leaf["part"] is not None: raise SystemExit(f"statement: the contract of {name} has an `ensures` of a part of a record, which the verifier in Lean does not read yet")
            # (the record said is had once, by a `let`: each field's words are then of that one value)
            kind = dict(c["args"])[leaf["name"]]
            whole = fresh("record", {arg for arg, _ in c["args"]})
            out.append(f"ensuresw {leaf['name']} (call bytes_of (let {whole} " + sexp(by_kind(leaf["expr"], kinds, name), seqs, scope) + " " +
                       sexp(record_words(kind, layouts[kind], ("name", whole), name), seqs, scope.with_name(whole)) + "))")
            continue
        if leaf["name"] in kinds:
            # a whole run of words: its bytes are those of the words said, the lowest byte of each first
            if leaf["part"] is not None: raise SystemExit(f"statement: the contract of {name} has an `ensures` of a part of a run of words, which the verifier in Lean does not read yet")
            out.append(f"ensuresw {leaf['name']} " + sexp(("call", "bytes_of", [by_kind(leaf["expr"], kinds, name)]), seqs, scope))
            continue
        if leaf["name"] in word_out_bytes:
            out.append(f"ensuresw {leaf['name']} " + sexp(by_kind(leaf["expr"], kinds, name), seqs, scope))
            continue
        if kinds: raise SystemExit(f"statement: the contract of {name} has an `ensures` of bytes beside arguments of the kinds {', '.join(said)}: not read yet")
        arg_kind = dict(c["args"]).get(leaf["name"])
        if arg_kind is None:
            raise SystemExit(
                f"statement: the contract of {name} has `ensures {leaf['name']} = ...`, "
                f"but `{leaf['name']}` is not a parameter of `{name}` (use `ensures result = ...` for the return value)"
            )
        m_fixed = re.fullmatch(r"(\d+) bytes", arg_kind)
        if m_fixed is None:
            if leaf["part"] is None:
                raise SystemExit(
                    f"statement: the contract of {name} has `ensures {leaf['name']} = ...` on `{arg_kind}`; "
                    f"variable-length byte buffers require an explicit slice `ensures {leaf['name']}[lo .. hi] = ...`"
                )
            lo, hi = leaf["part"]
        else:
            count = int(m_fixed.group(1))
            lo, hi = leaf["part"] if leaf["part"] is not None else (("num", 0), ("num", count))
        out.append(f"ensures {leaf['name']} {sexp(lo, seqs, scope)} {sexp(hi, seqs, scope)} {sexp(leaf['expr'], seqs, scope)}")
    if isinstance(c["stack"], int):
        out.append(f"stack {c['stack']}")
    elif isinstance(c["stack"], tuple) and c["stack"][0] == "grows":
        sb = stack_bits_spec(c["stack"][1], num_args)
        if sb is not None:
            base, step, arg, sub, div = sb
            out.append(f"stack {base}")
            out.append(f"stackbits {step} {arg} {sub} {div}")
        else:
            sl = stack_lin_spec(c["stack"][1], num_args)
            if sl is None:
                raise SystemExit(f"statement: the contract of {name} has a `stack` formula the verifier in Lean does not read yet")
            base, step, arg, sub, div = sl
            out.append(f"stack {base}")
            out.append(f"stacklin {step} {arg} {sub} {div}")
    else:
        raise SystemExit(f"statement: the contract of {name} has a `stack` line the verifier in Lean does not read yet")
    out += _calling_lines(c.get("calling"), name, names, r, result, is_arm64)
    return out


def called(obj, symbol):
    """The functions SYMBOL calls (or tail-jumps to), by name, in order of first mention."""
    if arm64(obj): return arm64_obj.called(obj, symbol)
    out = []
    for _, _, text in kdecode.read(obj, symbol, 0, 0)[0]:
        m = re.fullmatch(r"\.(?:call|jmp) (\S+)", text)
        if m and not m.group(1).startswith("0x") and m.group(1) not in out: out.append(m.group(1))
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
            if name == symbol: continue
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


def takes_data(rows):
    """Does the function take an address in its file's read-only data (`lea reg, [rip + data]`)?"""
    return any(text.split()[0] == ".lea_data" for _, _, text in rows)


def pieces(functions):
    """The read-only data of the object files in which a function to be shown takes an address:
    [(object, the boundary the data lies on, its bytes)], each file once, in the order of the functions (a
    function after those it calls). A file's number in the statement is its place in this list."""
    out, seen = [], set()
    for obj, symbol in ordered(functions):
        if arm64(obj): continue           # (no row of the AArch64 table takes an address in a file's data yet)
        rows, rodata = kdecode.read(obj, symbol, 0, 0)
        if takes_data(rows) and os.path.realpath(obj) not in seen:
            seen.add(os.path.realpath(obj))
            out.append((obj, kdecode.boundary(obj, symbol), bytes(rodata)))
    return out


def statement(spec_text, functions):
    """The lines that say what is to be shown of the functions [(object, symbol)]: the read-only data of
    the object files, where a function takes an address there; each function's instructions and its
    contract, a function after those it calls; then the definitions."""
    out = []
    spec = ode.Spec(spec_text)
    seqs = sequences(spec)
    if len({arm64(obj) for obj, _ in functions}) > 1: raise SystemExit("statement: functions for x86-64 and for AArch64 in one statement")
    # Nothing of the specification is left out without a word: what the account in Lean has no meaning for is refused.
    # (A layout says nothing by itself: it is read where an argument of a function to be shown is of its kind.)
    for what, there in (("a lemma", spec.lemmas), ("a kind", spec.kinds)):
        if there: raise SystemExit(f"statement: the specification has {what} ({', '.join(map(str, list(there)[:3]))}), which the verifier in Lean does not read yet")
    # A function may read the read-only data of the program's object files. The statement gives each file's
    # bytes once, before the functions, with the boundary they lie on; what is shown holds wherever the
    # program is loaded (those bytes in memory, each file's at the address its instructions take).
    files = pieces(functions)
    number = {os.path.realpath(obj): k for k, (obj, _, _) in enumerate(files)}
    for _, align, rodata in files: out.append(f"piece {align} {rodata.hex().upper()}")
    for obj, symbol in ordered(functions):
        out.append(f"fn {symbol}")
        if arm64(obj):
            # A function for AArch64: its machine, its instructions by the AArch64 table, its contract.
            out.append("machine arm64")
            for a, b, text in arm64_obj.read(obj, symbol): out.append(f"i {a} {b} {text}")
            if symbol not in spec.contracts: raise SystemExit(f"statement: no contract of {symbol} in the specification")
            if spec.contracts[symbol]["needs"]: raise SystemExit(f"statement: the contract of {symbol}, a function for AArch64, says what it needs of the processor: not read yet")
            out += contract_lines(spec.contracts[symbol], symbol, seqs, spec.consts, spec.layouts, is_arm64=True)
            continue
        rows, rodata = kdecode.read(obj, symbol, 0, 0)
        # A function that takes an address in its file's data says which file's it is (before its instructions).
        if takes_data(rows): out.append(f"data {number[os.path.realpath(obj)]}")
        for a, b, text in rows: out.append(f"i {a} {b} {text}")
        if symbol not in spec.contracts: raise SystemExit(f"statement: no contract of {symbol} in the specification")
        out += contract_lines(spec.contracts[symbol], symbol, seqs, spec.consts, spec.layouts, is_arm64=False)
        # The machine of the account in Lean has every instruction of the table. A processor has those of the
        # kinds it has: so a function's instructions must be of kinds its contract says it needs (as
        # ../kcheck/kspec.py `fits` has it: a processor with AVX-512 has AVX and SSE4.1; one with AVX, SSE4.1).
        # (What the contract says it needs on a condition does not count here: the function's own
        # instructions run whatever the arguments are. A call of a function that needs more is the verifier's
        # to see to, on the path where the condition holds.)
        have = {what for what, more in spec.contracts[symbol]["needs"] if more is None}
        if "avx512" in have: have |= {"avx", "sse41"}
        if "avx" in have: have.add("sse41")
        extra = kdecode.features(obj, symbol) - have
        if extra: raise SystemExit(f"statement: {symbol} holds instructions of a kind its contract does not say it needs: {', '.join(sorted(extra))}")
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
