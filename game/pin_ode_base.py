#!/usr/bin/env pypy3
"""Refresh both recipient packages from the toolchain, and pin their code.

    pypy3 game/pin_ode_base.py

Copies each recipient's modules, then pins each package tree using the
unchanged root launcher. Owner-selected theorem and specification pins
are preserved. Tests check both copies and pins for drift.
"""
import os
import re
import shutil
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
TOOLCHAIN = os.path.join(os.path.dirname(HERE), "ode")
sys.path.insert(0, os.path.join(HERE, "bootstrap", "root"))
from launch import read_tree, tree_hash  # noqa: E402


def refresh(base_name, target, modules):
    """Refresh one delivery package; owner theorem/spec pins stay unchanged."""
    base = os.path.join(HERE, base_name)
    shutil.rmtree(os.path.join(base, "ode"), ignore_errors=True)
    os.makedirs(os.path.join(base, "ode"))
    for name in modules:
        shutil.copy(os.path.join(TOOLCHAIN, name), os.path.join(base, "ode", name))
    h = tree_hash(read_tree(base)).hex()
    path = os.path.join(HERE, "bootstrap", target, "RELIANCE")
    with open(path) as stream:
        text = stream.read()
    with open(path, "w") as stream:
        stream.write(re.sub(r"\(ode-base #[0-9a-f]*\)", f"(ode-base #{h})", text))
    print(base_name, h)


refresh("ode-base", "game-targets", (
    "__init__.py", "a64.py", "canon.py", "check.py", "native.py", "store.py", "word.py"))
refresh("kernel-base", "kernel-targets", (
    "__init__.py", "canon.py", "kernel.py", "proof_cli.py", "encoding_cli.py", "word_literal.py"))
