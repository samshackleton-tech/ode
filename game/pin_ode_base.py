#!/usr/bin/env pypy3
"""Write game/ode-base's tree hash into game-targets/RELIANCE as (ode-base #hash).

Uses the root's own tree hash (bootstrap/root/launch.py). Run after any
change to game/ode-base/; tests/test_game.py fails until the pin matches.
"""
import os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "bootstrap", "root"))
from launch import read_tree, tree_hash
h = tree_hash(read_tree(os.path.join(HERE, "ode-base"))).hex()
p = os.path.join(HERE, "bootstrap", "game-targets", "RELIANCE")
s = open(p).read()
s = re.sub(r"\n  \(ode-base #[0-9a-f]*\)", "", s)
s = s.replace("(reliance\n", f"(reliance\n  (ode-base #{h})\n", 1)
open(p, "w").write(s)
print(h)
