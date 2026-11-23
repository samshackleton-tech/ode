#!/usr/bin/env python3
"""lean_verify: are functions of binaries shown to meet their contracts, by the verifier in Lean?

    python3 lean_verify.py SPEC PROOF OBJECT:SYMBOL [OBJECT:SYMBOL …]     (needs Lean's `lake`, to build the verifier once)

    python3 lean_verify.py ../kcheck/programs/common/common.spec proofs/ode_common.proof ../kcheck/programs/common/odecommon.o:ode_common
    python3 lean_verify.py examples/equal/equal.spec proofs/ode_equal.proof ../kcheck/programs/common/odecommon.o:ode_common examples/equal/odeequal.o:ode_equal

What is to be shown is written from each OBJECT's bytes and SPEC's text (statement.py); PROOF is the
maker's and adds nothing to it. Every function that one of the functions calls must be among them: a call
is taken by the contract of a function that is itself shown, never by one accepted without checking. The verifier (Core.lean, built
by `lake build`) says `shown` of all of them, or why not. Exit 0 only for shown. README.md says what a
`shown` rests on, and what it does not cover."""
import os, re, shutil, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import built, statement

TABLE = statement.TABLES["x86-64"]         # (a statement of functions for AArch64 is given AArch64's table: statement.table_of)
EXE = os.path.join(HERE, ".lake", "build", "bin", "odeverify")
LAKE = shutil.which("lake") or (os.path.expanduser("~/.elan/bin/lake") if os.path.exists(os.path.expanduser("~/.elan/bin/lake")) else None)


def verify(spec_text, functions, proof_path):
    """functions: [(object, symbol)]. (shown?, what the verifier said)."""
    if not LAKE: raise SystemExit("lean_verify: Lean's `lake` is not installed (https://lean-lang.org): the verifier is built with it")
    try: built.built("odeverify")
    except AssertionError as e: raise SystemExit(f"lean_verify: the verifier does not build: {e}")
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, "statement")
        lines = statement.statement(spec_text, functions)
        with open(path, "w") as f: f.write("\n".join(lines) + "\n")
        r = subprocess.run([EXE, statement.table_of(lines), path, proof_path], capture_output=True, text=True)
    return r.returncode == 0 and r.stdout == "shown\n", r.stdout.strip()


def with_data(functions):
    """[(an object file's name, how many bytes of read-only data the statement gives for it)]: the files in
    which a function to be shown takes the address of a constant."""
    return [(os.path.basename(obj), len(rodata)) for obj, _, rodata in statement.pieces(functions)]


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
        for obj, symbol in functions:
            print(f"\nshown: {symbol} in {os.path.basename(obj)} meets its contract, with the definitions of {os.path.basename(spec)} it uses.")
        data = with_data(functions)
        if data:
            files = ", ".join(f"{name} ({n} bytes of read-only data)" for name, n in data)
            print(f"\nFunctions here read constants of their files: {files}. What is shown holds wherever the program is\n"
                  "loaded: that each file's bytes lie in memory where its instructions look for them is the linker's and the\n"
                  "loader's part. This verification relies on them for it and does not show it.")
    else:
        lines = said.splitlines()
        where = lines[-1][3:] if lines and lines[-1].startswith("in ") else "(no function)"
        print(f"\nNOT shown. The verifier's word, of {where}: {lines[0] if lines else '(nothing)'}")
    sys.exit(0 if shown else 1)
