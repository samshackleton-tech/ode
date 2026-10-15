#!/usr/bin/env pypy3
"""Emit a natural-addition normalization proof; no kernel import."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from ode.canon import canonical_bytes, parse
from ode.nat_proof import prove


def main():
    directory = ROOT / 'examples' / 'proofs'
    theory = parse((directory / 'nat-add.theory.sexp').read_bytes())
    parameters = parse('((a Nat) (b Nat) (c Nat) (d Nat))')
    left = parse('(add (add a b) (add c (add d (zero))))')
    right = parse('(add (add d c) (add b a))')
    goal, proof = prove(theory, parameters, left, right)
    for kind, value in (('goal', goal), ('proof', proof)):
        (directory / f'nat-add.{kind}.sexp').write_bytes(canonical_bytes(value))


if __name__ == '__main__':
    main()
