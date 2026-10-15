#!/usr/bin/env pypy3
"""Connect register execution to normalization for G's most complex output."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT))
from ode.canon import canonical_bytes,parse
from ode.register_proof import normalized_output


def main():
    d=ROOT/'examples'/'proofs'
    t=parse((d/'register.theory.sexp').read_bytes())
    g,p=[parse((d/f'register-g.{k}.sexp').read_bytes()) for k in ('goal','proof')]
    g,p=normalized_output(t,g,p,'b')
    for kind,value in (('goal',g),('proof',p)):
        (d/f'register-g-normalized-b.{kind}.sexp').write_bytes(canonical_bytes(value))


if __name__=='__main__':
    main()
