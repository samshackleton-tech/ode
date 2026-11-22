# Today's rule at a call, seen on `ode_equal`, which calls `ode_common`: the caller's clause names less than the
# called function's. The kept proofs, the contract changed.
# Run in `proof-core`, with `odeverify` built: `python3 ../paper/trial/trace/equal_trace.py`.
import os, subprocess, sys, tempfile
sys.path[:0] = [".", "../kcheck", "../lang"]
import statement
spec = open("examples/equal/equal.spec").read()
old = "    returns equal(a, b)\n    trace depends on a, b, n\n"
assert spec.count(old) == 1
objs = [("../kcheck/programs/common/odecommon.o", "ode_common"), ("examples/equal/odeequal.o", "ode_equal")]
with tempfile.TemporaryDirectory() as d:
    for tag, line in (("as kept", "    trace depends on a, b, n\n"), ("the caller names n alone", "    trace depends on n\n"),
                      ("the caller names a, b", "    trace depends on a, b\n"), ("the caller has no line", "")):
        st = os.path.join(d, "equal.st")
        with open(st, "w") as f: f.write("\n".join(statement.statement(spec.replace(old, "    returns equal(a, b)\n" + line), objs)) + "\n")
        r = subprocess.run([".lake/build/bin/odeverify", "../core/x86.tab", st, "proofs/ode_equal.proof"], capture_output=True, text=True)
        print(f"{tag}: exit {r.returncode}: " + " | ".join(r.stdout.strip().splitlines()))
