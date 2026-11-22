# Why today's prover finds no proof of `equal_ct` (compare.ode), whatever its `trace depends on` line lists:
# four copies of the function, each with a number returned (the contract does not say which) and
# `trace depends on a, b, n`.
# Run in `proof-core`: `python3 ../paper/trial/trace/compare_diag.py`.
import os, subprocess, sys, tempfile
sys.path[:0] = [".", "../kcheck", "../lang"]
import odec, prove
here = os.path.dirname(os.path.abspath(__file__))
with open(os.path.join(here, "compare.ode")) as f: SRC = f.read()
start = SRC.index('fn equal_ct as "ode_equal_ct" {')
FN = SRC[start:SRC.index("\n}\n", start) + 3]
PLACE = "place +0x5 {\n    name i = rcx\n    fact i <= n\n    decreases n - i\n}\n"
SPEC = "contract ode_equal_ct(a: n bytes, b: n bytes, n: number) {\n    returns r\n    trace depends on a, b, n\n    stack 0\n}\n"
LAST = ("  sub r10, 1 ", "  // sub r10, 1 ")                              # the subtraction of 1 from what may be 0, taken out
BYTES = ("  sub rax, r9\n", "  add rax, 256\n  sub rax, r9\n")           # 256 added before one byte is subtracted from another
COPIES = [("as written", []), ("the subtraction of 1 taken out", [LAST]), ("256 added before the bytes are subtracted", [BYTES]), ("both", [LAST, BYTES])]

if sys.argv[1:2] == ["--one"]:
    src, obj, st, pf = sys.argv[2:6]
    odec.build(src, "equal_ct", obj)
    prove.prove(SPEC, [(obj, "ode_equal_ct", PLACE)], st, pf)
    r = subprocess.run([os.path.join(".lake", "build", "bin", "odeverify"), os.path.join("..", "core", "x86.tab"), st, pf], capture_output=True, text=True)
    print(r.stdout.strip())
    sys.exit(0)

with tempfile.TemporaryDirectory() as d:
    for name, edits in COPIES:
        fn = FN
        for a, b in edits:
            assert fn.count(a) == 1, a
            fn = fn.replace(a, b)
        src = os.path.join(d, "copy.ode")
        with open(src, "w") as f: f.write(fn)
        try:
            r = subprocess.run([sys.executable, os.path.abspath(__file__), "--one", src] + [os.path.join(d, "copy" + end) for end in (".o", ".st", ".pf")],
                               capture_output=True, text=True, timeout=120)
            print(f"equal_ct, {name}:", r.stdout.strip() if r.returncode == 0 else "no proof found")
        except subprocess.TimeoutExpired:
            print(f"equal_ct, {name}: the prover had not stopped after 120 seconds")
