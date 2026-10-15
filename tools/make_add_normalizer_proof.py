#!/usr/bin/env pypy3
"""Export the actual symbolic addition-normalizer result with a proof."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT))
from ode.canon import canonical_bytes,parse
from ode.add_normalizer_proof import export_normalizer


def main():
    d=ROOT/'examples'/'proofs'
    t=parse((d/'add32.theory.sexp').read_bytes())
    g,p=export_normalizer(t,parse('(add32 (add32 x y) (add32 z x))'))
    for kind,value in (('goal',g),('proof',p)):
        (d/f'add32-normalize.{kind}.sexp').write_bytes(canonical_bytes(value))


if __name__=='__main__':
    main()
