# Today's reader and an expression in `trace depends on`: the contract of `ode_equal` with a value named.
# Run in `proof-core`: `python3 ../paper/trial/trace/line_today.py`.
import sys
sys.path[:0] = [".", "../kcheck", "../lang"]
import statement
spec = open("examples/equal/equal.spec").read()
old = "    returns equal(a, b)\n    trace depends on a, b, n\n"
assert spec.count(old) == 1
objs = [("../kcheck/programs/common/odecommon.o", "ode_common"), ("examples/equal/odeequal.o", "ode_equal")]
for clause in ("trace depends on a, b, n", "trace depends on n, common(a, b)"):
    try:
        lines = statement.statement(spec.replace(old, "    returns equal(a, b)\n    " + clause + "\n"), objs)
        print(f"`{clause}`: read, {len(lines)} lines of statement")
    except BaseException as e:
        print(f"`{clause}`: not read: {e}")
