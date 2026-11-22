# What today's prover and verifier say of the compare functions of compare.ode (x86-64; `odeverify` built).
# Run in `proof-core`: `python3 ../paper/trial/trace/compare_verify.py`.
#   equal      with its whole contract (compare.spec): `returns same(a, b)` and `trace depends on a, b, n`;
#              then with `trace depends on n` alone, judged with the proof just found
#   equal_ct   with a number returned (the contract does not say which) and `trace depends on a, b, n`: is there a
#              proof at all?
#   differ_ct  the same two questions as of equal: `trace depends on a, b, n`, then `trace depends on n` alone
#              with the proof just found
import os, subprocess, sys, tempfile
sys.path[:0] = [".", "../kcheck", "../lang"]
import odec, prove, statement
here = os.path.dirname(os.path.abspath(__file__))
EXE, TABLE = os.path.join(".lake", "build", "bin", "odeverify"), os.path.join("..", "core", "x86.tab")

EARLY_PLACE = """place +0x2 {
    name i = rcx
    fact i <= n
    fact same_from(a, b, i) == same(a, b)
    decreases n - i
}
"""
CT_PLACE = """place +0x5 {
    name i = rcx
    fact i <= n
    decreases n - i
}
"""
CT_RETURNS_ALL = """contract ode_equal_ct(a: n bytes, b: n bytes, n: number) {
    returns r
    trace depends on a, b, n
    stack 0
}
"""
CT_RETURNS = CT_RETURNS_ALL.replace("trace depends on a, b, n", "trace depends on n")

def said(st, pf):
    r = subprocess.run([EXE, TABLE, st, pf], capture_output=True, text=True)
    return " | ".join(r.stdout.strip().splitlines())

if sys.argv[1:2] == ["--prove"]:
    spec, obj, symbol, places, st, pf = sys.argv[2:8]
    with open(spec) as f, open(places) as g: prove.prove(f.read(), [(obj, symbol, g.read())], st, pf)
    sys.exit(0)

with open(os.path.join(here, "compare.spec")) as f: spec = f.read()
with tempfile.TemporaryDirectory() as d:
    def path(name): return os.path.join(d, name)
    def proved(tag, spec_text, obj, symbol, places):
        with open(path(tag + ".spec"), "w") as f: f.write(spec_text)
        with open(path(tag + ".places"), "w") as f: f.write(places)
        try:
            r = subprocess.run([sys.executable, os.path.abspath(__file__), "--prove", path(tag + ".spec"), obj, symbol, path(tag + ".places"), path(tag + ".st"), path(tag + ".pf")],
                               capture_output=True, text=True, timeout=120)
        except subprocess.TimeoutExpired:
            return "the prover had not stopped after 120 seconds"
        if r.returncode != 0: return "no proof found; the last lines: " + " | ".join([l.strip() for l in (r.stdout + r.stderr).split("\n") if l.strip() and not l.startswith(("f ", "g ", "Traceback", "  File", "    "))][-4:])[:420]
        return f"{said(path(tag + '.st'), path(tag + '.pf'))} (statement {os.path.getsize(path(tag + '.st'))} bytes, proof {os.path.getsize(path(tag + '.pf'))} bytes)"

    for fn in ("equal", "equal_ct", "differ_ct"): odec.build(os.path.join(here, "compare.ode"), fn, path(fn + ".o"))
    print("equal, `returns same(a, b)` and `trace depends on a, b, n`:", proved("early", spec, path("equal.o"), "ode_equal_early", EARLY_PLACE))
    if os.path.exists(path("early.pf")):
        less = spec.replace("trace depends on a, b, n", "trace depends on n")
        assert less != spec
        with open(path("early_n.st"), "w") as f: f.write("\n".join(statement.statement(less, [(path("equal.o"), "ode_equal_early")])) + "\n")
        print("equal, `returns same(a, b)` and `trace depends on n` alone, with that proof:", said(path("early_n.st"), path("early.pf")))
    print("equal_ct, a number returned, `trace depends on a, b, n`:", proved("ct_all", CT_RETURNS_ALL, path("equal_ct.o"), "ode_equal_ct", CT_PLACE))
    if os.path.exists(path("ct_all.pf")):
        with open(path("ct_n.st"), "w") as f: f.write("\n".join(statement.statement(CT_RETURNS, [(path("equal_ct.o"), "ode_equal_ct")])) + "\n")
        print("equal_ct, a number returned, `trace depends on n`, with that proof:", said(path("ct_n.st"), path("ct_all.pf")))
    differ_all, differ_n = (c.replace("ode_equal_ct", "ode_differ_ct") for c in (CT_RETURNS_ALL, CT_RETURNS))
    print("differ_ct, a number returned, `trace depends on a, b, n`:", proved("differ", differ_all, path("differ_ct.o"), "ode_differ_ct", CT_PLACE))
    if os.path.exists(path("differ.pf")):
        with open(path("differ_n.st"), "w") as f: f.write("\n".join(statement.statement(differ_n, [(path("differ_ct.o"), "ode_differ_ct")])) + "\n")
        # The proof just found, with one line added to the loop's place: on a later turn r10 (the differences so far)
        # may be computed from the bytes. (The prover adds such a line by itself where the verifier asks for it.)
        with open(path("differ.pf")) as f: lines = f.read().split("\n")
        at = next(i for i, line in enumerate(lines) if line.startswith("decreases "))
        with open(path("differ_n.pf"), "w") as f: f.write("\n".join(lines[:at] + ["marked r10"] + lines[at:]))
        print("differ_ct, a number returned, `trace depends on n` alone, with that proof and that line:", said(path("differ_n.st"), path("differ_n.pf")))
