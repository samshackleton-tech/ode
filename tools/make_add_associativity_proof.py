#!/usr/bin/env pypy3
"""Emit Word32 associativity from the ripple-carry theory."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT))
from ode.canon import canonical_bytes,parse
from ode.add_associativity_proof import artifacts


def main():
    d=ROOT/'examples'/'proofs'
    t=parse((d/'add32.theory.sexp').read_bytes())
    g,p=artifacts(t)
    for kind,value in (('goal',g),('proof',p)):
        (d/f'add32-assoc.{kind}.sexp').write_bytes(canonical_bytes(value))


if __name__=='__main__':
    main()
