# The three compare functions of compare.ode on a processor: do they compute what C computes, and how many
# instructions does one call execute for arrays that are the same, that differ in the first byte, and that
# differ in the last? (x86-64 Linux with cc and perf.)
# Run in `proof-core`: `python3 ../paper/trial/trace/compare_run.py`.
import os, subprocess, sys, tempfile
sys.path[:0] = [".", "../kcheck", "../lang"]
import odec
here = os.path.dirname(os.path.abspath(__file__))

def instructions(exe, which, kind, calls):
    """The instructions the processor counts in user mode for a run of CALLS calls."""
    r = subprocess.run(["perf", "stat", "-x,", "-e", "instructions:u", exe, which, kind, str(calls)], capture_output=True, text=True, check=True)
    return int(next(line for line in r.stderr.splitlines() if "instructions" in line).split(",")[0])

with tempfile.TemporaryDirectory() as d:
    objs = []
    for fn in ("equal", "equal_ct", "differ_ct"):
        objs.append(os.path.join(d, fn + ".o"))
        odec.build(os.path.join(here, "compare.ode"), fn, objs[-1])
    exe = os.path.join(d, "compare_check")
    subprocess.run(["cc", "-O2", "-o", exe, os.path.join(here, "compare_check.c")] + objs, check=True)
    print(subprocess.run([exe], capture_output=True, text=True, check=True).stdout.strip())
    print("instructions executed by one call on two arrays of 32 bytes (the difference between runs of two and of one million calls, divided by a million):")
    for which, name in (("early", "equal"), ("ct", "equal_ct"), ("differ", "differ_ct")):
        for kind, words in (("same", "the arrays are the same"), ("first", "they differ in the first byte"), ("last", "they differ in the last byte")):
            per_call = (instructions(exe, which, kind, 2000000) - instructions(exe, which, kind, 1000000)) / 1000000
            print(f"  {name}, {words}: {per_call:.2f}")
