"""Lean's lake builds a target of this folder once per process.

    built.built("odeverify")      before a test or a tool runs the program of that name

tests.sh builds everything first and says so (ODE_LEAN_BUILT=1), so that the tests can run side by side
without each asking lake again. Without that, a verification asked lake to build before every run."""
import os, shutil, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
LAKE = shutil.which("lake") or (os.path.expanduser("~/.elan/bin/lake") if os.path.exists(os.path.expanduser("~/.elan/bin/lake")) else None)
_DONE = set()


def built(target):
    """`lake build TARGET`, once; AssertionError with lake's last words where it does not build."""
    if target in _DONE or os.environ.get("ODE_LEAN_BUILT"): return
    if not LAKE: raise AssertionError("Lean's `lake` is not installed (https://lean-lang.org)")
    env = dict(os.environ, PATH=os.path.dirname(LAKE) + os.pathsep + os.environ["PATH"])
    # (with the verifier, the prover's helper that stands in for it while a proof is being found: session.py)
    r = subprocess.run([LAKE, "build", target] + (["odeprove"] if target == "odeverify" else []), cwd=HERE, capture_output=True, text=True, env=env)
    if r.returncode != 0: raise AssertionError("lake build failed:\n" + r.stdout[-2000:] + r.stderr[-2000:])
    _DONE.add(target)
