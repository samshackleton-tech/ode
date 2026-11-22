# Today's rule for a returned number, seen on `ode_far`: the contract without `trace depends on x`.
# Run in `proof-core`, with `odeverify` built: `python3 ../paper/trial/trace/far_trace.py`.
import os, subprocess, sys, tempfile
sys.path[:0] = [".", "../kcheck", "../lang"]
import statement
spec = open("examples/far/far.spec").read()
old = """    returns x + 9223372036854775808
    trace depends on x
"""
assert spec.count(old) == 1
changed = spec.replace(old, "    returns x + 9223372036854775808\n")
with tempfile.TemporaryDirectory() as d:
    for tag, text in (("as kept", spec), ("without `trace depends on x`", changed)):
        st = os.path.join(d, "far.st")
        with open(st, "w") as f: f.write("\n".join(statement.statement(text, [("examples/far/odefar.o", "ode_far")])) + "\n")
        r = subprocess.run([".lake/build/bin/odeverify", "../core/x86.tab", st, "proofs/ode_far.proof"], capture_output=True, text=True)
        print(f"{tag}: exit {r.returncode}: " + " | ".join(r.stdout.strip().splitlines()))
