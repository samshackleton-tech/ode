#!/usr/bin/env python3
"""statement: what is to be shown of a function, for the verifier in Lean (Core.lean). RELIED ON.

    python3 statement.py OBJECT SYMBOL SPEC OUT.statement

The function's instructions as ../kcheck/kdecode.py reads them from OBJECT's bytes by the table, the public
contract of SYMBOL in SPEC and the definitions of SPEC as ../kcheck/ode.py reads them, written as the lines
Main.lean reads. A contract or a definition with anything the verifier in Lean does not read yet is refused
here: no line of a contract is left out. The theorem in SoundTop.lean is about what these lines say; that
they say what the file's bytes and the specification's text say rests on this file and the two it reads with."""
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


def statement(obj, symbol, spec_text):
    """The lines that say what is to be shown: the function's instructions, its contract, the definitions."""
    out = []
    rows, _ = kdecode.read(obj, symbol, 0, 0)
    for a, b, text in rows: out.append(f"i {a} {b} {text}")
    spec = ode.Spec(spec_text)
    c = spec.contracts[symbol]
    for name, kind in c["args"]:
        m = re.fullmatch(r"(\w+) bytes", kind)
        if kind == "number": out.append(f"arg {name} number")
        elif m and not m.group(1).isdigit(): out.append(f"arg {name} bytes {m.group(1)}")
        else: raise SystemExit(f"statement: an argument of a kind the verifier in Lean does not read yet: {name}: {kind}")
    for key in ("asks", "calls", "conditions", "given", "leaves", "needs", "spoils"):
        if c[key]: raise SystemExit(f"statement: the contract has `{key}`, which the verifier in Lean does not read yet")
    if c["no_overlap"] or c["decreases"]: raise SystemExit("statement: the contract has a line the verifier in Lean does not read yet")
    # A contract promises that which instructions run and which addresses are touched do not depend on the bytes
    # in memory, but for the runs a `trace depends on` line names. The account in Lean says nothing of that.
    quiet = [name for name, kind in c["args"] if kind != "number" and name not in c["trace"]]
    if quiet: raise SystemExit(f"statement: the contract promises that the trace does not depend on the bytes of {', '.join(quiet)}: "
                               "the verifier in Lean does not show that yet")
    if c["returns"] is not None: out.append("returns " + sexp(c["returns"]))
    out.append(f"stack {c['stack']}")
    for name, (params, body) in spec.fns.items():
        if len(body) != 1 or body[0][0] != "expr": raise SystemExit(f"statement: the definition {name} is more than one expression")
        out.append(" ".join(["def", name] + params + ["=", sexp(body[0][1])]))
    return out


if __name__ == "__main__":
    obj, symbol, spec, out = sys.argv[1:]
    with open(spec) as f: lines = statement(obj, symbol, f.read())
    with open(out, "w") as f: f.write("\n".join(lines) + "\n")
