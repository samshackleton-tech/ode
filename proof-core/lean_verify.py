#!/usr/bin/env python3
"""lean_verify: are functions of binaries shown to meet their contracts, by the verifier in Lean?

    python3 lean_verify.py SPEC PROOF OBJECT:SYMBOL [OBJECT:SYMBOL …]     (needs Lean's `lake`, to build the verifier once)

    python3 lean_verify.py ../kcheck/programs/common/common.spec proofs/ode_common.proof ../kcheck/programs/common/odecommon.o:ode_common
    python3 lean_verify.py examples/equal/equal.spec proofs/ode_equal.proof ../kcheck/programs/common/odecommon.o:ode_common examples/equal/odeequal.o:ode_equal

What is to be shown is written from each OBJECT's bytes and SPEC's text (statement.py); PROOF is the
maker's and adds nothing to it. Every function that one of the functions calls must be among them: a call
is taken by the contract of a function that is itself shown, never unchecked. The verifier (Core.lean, built
by `lake build`) says `shown` of all of them, or why not. Exit 0 only for shown. README.md says what a
`shown` rests on, and what it does not cover."""
import os, re, shutil, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import built, statement

TABLE = os.path.join(HERE, "..", "core", "x86.tab")
EXE = os.path.join(HERE, ".lake", "build", "bin", "odeverify")
LAKE = shutil.which("lake") or (os.path.expanduser("~/.elan/bin/lake") if os.path.exists(os.path.expanduser("~/.elan/bin/lake")) else None)


def verify(spec_text, functions, proof_path):
    """functions: [(object, symbol)]. (shown?, what the verifier said)."""
    if not LAKE: raise SystemExit("lean_verify: Lean's `lake` is not installed (https://lean-lang.org): the verifier is built with it")
    try: built.built("odeverify")
    except AssertionError as e: raise SystemExit(f"lean_verify: the verifier does not build: {e}")
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, "statement")
        with open(path, "w") as f: f.write("\n".join(statement.statement(spec_text, functions)) + "\n")
        r = subprocess.run([EXE, TABLE, path, proof_path], capture_output=True, text=True)
    return r.returncode == 0 and r.stdout == "shown\n", r.stdout.strip()


if __name__ == "__main__":
    if len(sys.argv) < 4: raise SystemExit(__doc__)
    spec, proof = sys.argv[1:3]
    functions = statement.functions_of(sys.argv[3:])
    with open(spec) as f: spec_text = f.read()
    for _, symbol in functions:
        m = re.search(r"^contract " + re.escape(symbol) + r"\(.*?^\}", spec_text, re.S | re.M)
        print(m.group(0) if m else f"(no contract of {symbol} in {spec})")
    shown, said = verify(spec_text, functions, proof)
    if shown:
        for obj, symbol in functions: print(f"\nshown: {symbol} in {os.path.basename(obj)} meets its contract, with the definitions of {os.path.basename(spec)} it uses.")
    else:
        lines = said.splitlines()
        where = lines[-1][3:] if lines and lines[-1].startswith("in ") else "(no function)"
        print(f"\nNOT shown. The verifier's word, of {where}: {lines[0] if lines else '(nothing)'}")
    sys.exit(0 if shown else 1)
