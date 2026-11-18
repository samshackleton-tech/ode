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


def sexp(e):
    kind = e[0]
    if kind == "num": return f"(num {e[1]})"
    if kind == "name": return f"(name {e[1]})"
    if kind == "bin": return f"(bin {e[1]} {sexp(e[2])} {sexp(e[3])})"
    if kind == "ifx": return f"(ifx {sexp(e[1])} {sexp(e[2])} {sexp(e[3])})"
    if kind == "index": return f"(index {sexp(e[1])} {sexp(e[2])})"
    if kind == "call": return "(call " + " ".join([e[1]] + [sexp(a) for a in e[2]]) + ")"
    raise SystemExit(f"statement: an expression of a kind the verifier in Lean does not read yet: {e!r}")


def contract_lines(c, name):
    """A contract as the lines Reader.lean reads."""
    out = []
    for arg, kind in c["args"]:
        m = re.fullmatch(r"(\w+) bytes", kind)
        if kind == "number": out.append(f"arg {arg} number")
        elif m and not m.group(1).isdigit(): out.append(f"arg {arg} bytes {m.group(1)}")
        else: raise SystemExit(f"statement: {name}: an argument of a kind the verifier in Lean does not read yet: {arg}: {kind}")
    for key in ("asks", "calls", "conditions", "given", "leaves", "needs", "spoils"):
        if c[key]: raise SystemExit(f"statement: the contract of {name} has `{key}`, which the verifier in Lean does not read yet")
    if c["no_overlap"] or c["decreases"]: raise SystemExit(f"statement: the contract of {name} has a line the verifier in Lean does not read yet")
    # A contract promises that which instructions run and which addresses are touched do not depend on the bytes
    # in memory, but for the runs a `trace depends on` line names. The account in Lean says nothing of that.
    quiet = [arg for arg, kind in c["args"] if kind != "number" and arg not in c["trace"]]
    if quiet: raise SystemExit(f"statement: the contract of {name} promises that the trace does not depend on the bytes of {', '.join(quiet)}: "
                               "the verifier in Lean does not show that yet")
    if c["returns"] is not None: out.append("returns " + sexp(c["returns"]))
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
    # Nothing of the specification is left out without a word: what the account in Lean has no meaning for is refused.
    for what, there in (("a sequence", spec.seqs), ("a constant", spec.consts), ("a layout", spec.layouts), ("a machine", spec.machines),
                        ("a lemma", spec.lemmas), ("a kind", spec.kinds)):
        if there: raise SystemExit(f"statement: the specification has {what} ({', '.join(map(str, list(there)[:3]))}), which the verifier in Lean does not read yet")
    for obj, symbol in ordered(functions):
        out.append(f"fn {symbol}")
        rows, _ = kdecode.read(obj, symbol, 0, 0)
        for a, b, text in rows: out.append(f"i {a} {b} {text}")
        if symbol not in spec.contracts: raise SystemExit(f"statement: no contract of {symbol} in the specification")
        out += contract_lines(spec.contracts[symbol], symbol)
    for name, (params, body) in spec.fns.items():
        if len(body) != 1 or body[0][0] != "expr": raise SystemExit(f"statement: the definition {name} is more than one expression")
        out.append(" ".join(["def", name] + params + ["=", sexp(body[0][1])]))
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
