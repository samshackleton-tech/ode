#!/usr/bin/env pypy3
"""Emit the full-adder column's natural-number conservation theorem."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT))
from tools.proof_files import write_theory
from ode.canon import canonical_bytes,parse
from ode.adder_value_proof import theory,artifacts


def main():
    d=ROOT/'examples'/'proofs'
    t=theory(parse((d/'bits.theory.sexp').read_bytes()),parse((d/'nat-add.theory.sexp').read_bytes()))
    g,p=artifacts(t)
    write_theory(d/'adder-value.theory.sexp', t, [
        '; A Boolean full-adder column preserves the natural-number value.',
        '; sum-bit + 2*carry-bit = a+b+carry-in, with bit values zero or one.',
    ])
    for kind,value in (('goal',g),('proof',p)):
        (d/f'adder-value.{kind}.sexp').write_bytes(canonical_bytes(value))


if __name__=='__main__':
    main()
