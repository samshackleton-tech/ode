#!/usr/bin/env pypy3
"""Refresh game/ode-base from the toolchain, and pin it.

    pypy3 game/pin_ode_base.py

Copies the modules Bob runs from ode/ into game/ode-base/ode/, then
writes ode-base's tree hash (the root's own, bootstrap/root/launch.py)
into game-targets/RELIANCE as (ode-base #hash). One command, so the copy
and its pin cannot drift apart; tests/test_game.py fails if they do.
"""
import os
import re
import shutil
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
TOOLCHAIN = os.path.join(os.path.dirname(HERE), "ode")
BASE = os.path.join(HERE, "ode-base")
MODULES = ("__init__.py", "a64.py", "canon.py", "check.py", "native.py",
           "store.py", "word.py")  # blake3 is the root's own; bob.py lives here

shutil.rmtree(os.path.join(BASE, "ode"), ignore_errors=True)
os.makedirs(os.path.join(BASE, "ode"))
for name in MODULES:
    shutil.copy(os.path.join(TOOLCHAIN, name), os.path.join(BASE, "ode", name))
sys.path.insert(0, os.path.join(HERE, "bootstrap", "root"))
from launch import read_tree, tree_hash  # noqa: E402
h = tree_hash(read_tree(BASE)).hex()
path = os.path.join(HERE, "bootstrap", "game-targets", "RELIANCE")
with open(path) as f:
    text = f.read()
with open(path, "w") as f:
    f.write(re.sub(r"\(ode-base #[0-9a-f]*\)", f"(ode-base #{h})", text))
print(h)
