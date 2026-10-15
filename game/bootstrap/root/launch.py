#!/usr/bin/env pypy3
"""The root: everything Bob must get from Sam, besides ~300 bytes of hashes.

    pypy3 root/launch.py PACKAGE_RELIANCE ODE_BASE_DIR STORE TARGET word...

ODE_BASE_DIR may come from anywhere -- a mirror, a cache, Mallory. The
root reads every file under it into memory once, computes its tree hash
(below), and requires it to equal the (ode-base #hash) pinned in the
package's RELIANCE. On any difference it stops. Otherwise it runs
ode-base's bob.py from those same in-memory bytes, with every `ode`
import served from them, so nothing read after the hash can run.

Tree hash: BLAKE3 over the sorted entries, each the file's path (UTF-8,
'/'-separated, relative to ODE_BASE_DIR), a zero byte, and the 32-byte
BLAKE3 of its contents. __pycache__ directories are skipped.
Root code: this file and blake3.py; nothing else is imported from disk
except Python's standard library.
"""
import importlib.abc
import importlib.util
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from blake3 import blake3  # noqa: E402  (the root's own copy)
sys.path.pop(0)


def read_tree(root):
    files = {}
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d != "__pycache__"]
        for name in filenames:
            path = os.path.join(dirpath, name)
            rel = os.path.relpath(path, root).replace(os.sep, "/")
            with open(path, "rb") as f:
                files[rel] = f.read()
    return files


def tree_hash(files):
    entries = sorted(rel.encode("utf-8") + b"\0" + blake3(data)
                     for rel, data in files.items())
    return blake3(b"".join(entries))


class _MemoryFinder(importlib.abc.MetaPathFinder, importlib.abc.Loader):
    """Serves `ode` and `ode.*` only from the hashed bytes."""

    def __init__(self, files):
        self.files = files

    def find_spec(self, name, path=None, target=None):
        if name != "ode" and not name.startswith("ode."):
            return None
        rel = name.replace(".", "/")
        if rel + "/__init__.py" in self.files:
            return importlib.util.spec_from_loader(
                name, self, is_package=True)
        if rel + ".py" in self.files:
            return importlib.util.spec_from_loader(name, self)
        raise ImportError(f"{name} is not in the hashed ode-base")

    def create_module(self, spec):
        return None

    def exec_module(self, module):
        rel = module.__name__.replace(".", "/")
        key = rel + "/__init__.py" if rel + "/__init__.py" in self.files \
            else rel + ".py"
        if key.endswith("__init__.py"):
            module.__path__ = []
        exec(compile(self.files[key], "ode-base/" + key, "exec"),
             module.__dict__)


def main(argv):
    if len(argv) < 4:
        print("usage: launch.py PACKAGE_RELIANCE ODE_BASE_DIR STORE TARGET word...")
        return 2
    with open(argv[0], "rb") as f:
        reliance = f.read()
    pins = re.findall(rb"\(ode-base #([0-9a-f]{64})\)", reliance)
    if len(pins) != 1:
        print("REJECT package RELIANCE must pin exactly one ode-base")
        return 1
    files = read_tree(argv[1])
    if tree_hash(files).hex().encode() != pins[0]:
        print("REJECT ode-base is not the one the package pins")
        return 1
    for name in list(sys.modules):
        if name == "ode" or name.startswith("ode."):
            del sys.modules[name]
    sys.meta_path.insert(0, _MemoryFinder(files))
    if "bob.py" not in files:
        print("REJECT ode-base has no bob.py")
        return 1
    bob = {"__name__": "bob"}
    exec(compile(files["bob.py"], "ode-base/bob.py", "exec"), bob)
    return bob["main"](reliance, argv[2:])


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
