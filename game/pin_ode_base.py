#!/usr/bin/env pypy3
"""Write ode-base's tree hash into blake3/RELIANCE as (ode-base #hash).

Run after any change to game/bootstrap/ode-base/; tests/test_game.py
fails until the pin matches.
"""
import os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
BASE = os.path.join(HERE, "bootstrap", "ode-base")
sys.path.insert(0, BASE)
from ode.store import tree_hash
h = tree_hash(BASE).hex()
p = os.path.join(HERE, "bootstrap", "blake3", "RELIANCE")
s = open(p).read()
s = re.sub(r"\n  \(ode-base #[0-9a-f]*\)", "", s)
s = s.replace("(reliance\n", f"(reliance\n  (ode-base #{h})\n", 1)
open(p, "w").write(s)
print(h)
