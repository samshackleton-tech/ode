#!/usr/bin/env pypy3
"""Export a concrete overflow result from Dag, using the addition theory."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT))
from ode.canon import canonical_bytes, parse
from ode.word_literal import literal
from ode.arx_proof import export_normalizer
from ode.xor32_proof import app


def main():
    d=ROOT/'examples'/'proofs'
    t=parse((d/'add32.theory.sexp').read_bytes())
    term=app('xor32',app('add32',literal(0xffffffff),literal(1)),literal(0xdeadbeef))
    g,p=export_normalizer(t,term)
    for kind,value in (('goal',g),('proof',p)):
        (d/f'constant.{kind}.sexp').write_bytes(canonical_bytes(value))


if __name__=='__main__':
    main()
