"""Lean's lake builds a target of this folder once per process.

    built.built("odeverify")      before a test or a tool runs the program of that name

tests.sh builds everything first and says so (ODE_LEAN_BUILT=1), so that the tests can run side by side
without each asking lake again. Without that, a verification asked lake to build before every run."""
import os, shutil, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
LAKE = shutil.which("lake") or (os.path.expanduser("~/.elan/bin/lake") if os.path.exists(os.path.expanduser("~/.elan/bin/lake")) else None)
_DONE = set()


def _stamp(target):
    return os.path.join(HERE, ".lake", "build", "bin", f".built_{target}")


def _up_to_date(target, targets):
    """True when every requested executable exists in .lake/build/bin and is at least as new as every Lean source."""
    if os.environ.get("ODE_LEAN_FORCE_BUILD"): return False
    bin_dir = os.path.join(HERE, ".lake", "build", "bin")
    bin_mtimes = []
    for t in targets:
        p = os.path.join(bin_dir, t)
        if not os.path.isfile(p): return False
        bin_mtimes.append(os.path.getmtime(p))
    stamp = _stamp(target)
    ref_mtime = os.path.getmtime(stamp) if os.path.isfile(stamp) else min(bin_mtimes)
    for name in os.listdir(HERE):
        if name.endswith(".lean") or name in ("lakefile.toml", "lean-toolchain", "lake-manifest.json"):
            if os.path.getmtime(os.path.join(HERE, name)) > ref_mtime:
                return False
    return True


def built(target):
    """`lake build TARGET`, once; AssertionError with lake's last words where it does not build."""
    if target in _DONE or os.environ.get("ODE_LEAN_BUILT"): return
    targets = [target] + (["odeprove"] if target == "odeverify" else [])
    if _up_to_date(target, targets):
        _DONE.add(target)
        return
    if not LAKE: raise AssertionError("Lean's `lake` is not installed (https://lean-lang.org)")
    env = dict(os.environ, PATH=os.path.dirname(LAKE) + os.pathsep + os.environ["PATH"])
    # (with the verifier, the prover's helper that stands in for it while a proof is being found: session.py)
    r = subprocess.run([LAKE, "build"] + targets, cwd=HERE, capture_output=True, text=True, env=env)
    if r.returncode != 0: raise AssertionError("lake build failed:\n" + r.stdout[-2000:] + r.stderr[-2000:])
    if all(os.path.isfile(os.path.join(HERE, ".lake", "build", "bin", t)) for t in targets):
        with open(_stamp(target), "w") as f: f.write("ok\n")
    _DONE.add(target)
