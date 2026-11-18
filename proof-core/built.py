"""Lean's lake builds a target of this folder, once a process; and Python's hash order is fixed.

    built.built("odeverify")      before a test or a tool runs the program of that name
    built.same_every_run()        at the start of a program that looks for proofs

tests.sh builds everything first and says so (ODE_LEAN_BUILT=1), so that the tests can run side by side
without each asking lake again. Without that, a verification asked lake to build before every run.

The prover's choices go by the order Python walks its sets in, and Python changes that order from run to
run unless PYTHONHASHSEED is set. With it at 0 the same proof is found every time, on every machine; a
failure can then be seen again, and a kept proof can be compared with what the prover finds."""
import os, shutil, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
LAKE = shutil.which("lake") or (os.path.expanduser("~/.elan/bin/lake") if os.path.exists(os.path.expanduser("~/.elan/bin/lake")) else None)
_DONE = set()


def built(target):
    """`lake build TARGET`, once; AssertionError with lake's last words where it does not build."""
    if target in _DONE or os.environ.get("ODE_LEAN_BUILT"): return
    if not LAKE: raise AssertionError("Lean's `lake` is not installed (https://lean-lang.org)")
    env = dict(os.environ, PATH=os.path.dirname(LAKE) + os.pathsep + os.environ["PATH"])
    r = subprocess.run([LAKE, "build", target], cwd=HERE, capture_output=True, text=True, env=env)
    if r.returncode != 0: raise AssertionError("lake build failed:\n" + r.stdout[-2000:] + r.stderr[-2000:])
    _DONE.add(target)


def same_every_run():
    """Start this program again with PYTHONHASHSEED=0, unless it was started so."""
    if os.environ.get("PYTHONHASHSEED") != "0":
        os.execve(sys.executable, [sys.executable] + sys.argv, dict(os.environ, PYTHONHASHSEED="0"))
