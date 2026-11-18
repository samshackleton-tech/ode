#!/usr/bin/env python3
"""lean_verify: is a function of a binary shown to meet its public contract, by the verifier in Lean?

    python3 lean_verify.py OBJECT SYMBOL SPEC PROOF        (needs Lean's `lake`, to build the verifier once)

    python3 lean_verify.py ../kcheck/programs/common/odecommon.o ode_common ../kcheck/programs/common/common.spec proofs/ode_common.proof

What is to be shown is written from OBJECT's bytes and SPEC's text (statement.py); PROOF is the maker's
and adds nothing to it. The verifier (Core.lean, built by `lake build`) says `shown` or why not. Exit 0
only for shown. README.md says what a `shown` rests on, and what it does not cover."""
import os, re, shutil, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import statement

TABLE = os.path.join(HERE, "..", "core", "x86.tab")
EXE = os.path.join(HERE, ".lake", "build", "bin", "odeverify")
LAKE = shutil.which("lake") or (os.path.expanduser("~/.elan/bin/lake") if os.path.exists(os.path.expanduser("~/.elan/bin/lake")) else None)


def verify(obj, symbol, spec_text, proof_path):
    """(shown?, what the verifier said)."""
    if not LAKE: raise SystemExit("lean_verify: Lean's `lake` is not installed (https://lean-lang.org): the verifier is built with it")
    env = dict(os.environ, PATH=os.path.dirname(LAKE) + os.pathsep + os.environ["PATH"])
    r = subprocess.run([LAKE, "build", "odeverify"], cwd=HERE, capture_output=True, text=True, env=env)
    if r.returncode != 0: raise SystemExit("lean_verify: the verifier does not build:\n" + r.stdout[-2000:] + r.stderr[-2000:])
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, "statement")
        with open(path, "w") as f: f.write("\n".join(statement.statement(obj, symbol, spec_text)) + "\n")
        r = subprocess.run([EXE, TABLE, path, proof_path], capture_output=True, text=True)
    return r.returncode == 0 and r.stdout == "shown\n", r.stdout.strip()


if __name__ == "__main__":
    if len(sys.argv) != 5: raise SystemExit(__doc__)
    obj, symbol, spec, proof = sys.argv[1:]
    with open(spec) as f: spec_text = f.read()
    m = re.search(r"^contract " + re.escape(symbol) + r"\(.*?^\}", spec_text, re.S | re.M)
    print(m.group(0) if m else f"(no contract of {symbol} in {spec})")
    shown, said = verify(obj, symbol, spec_text, proof)
    if shown: print(f"\nshown: {symbol} in {os.path.basename(obj)} meets this contract, with the definitions of {os.path.basename(spec)} it uses.")
    else: print(f"\nNOT shown. The verifier's word: {said.splitlines()[0] if said else '(nothing)'}")
    sys.exit(0 if shown else 1)
