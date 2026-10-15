#!/usr/bin/env pypy3
"""Emit numeric correctness of finite-width ripple carry, keeping final carry."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT))
from ode.canon import canonical_bytes,parse
from ode.bit_sum_value_proof import theory,artifacts


def main():
    d=ROOT/'examples'/'proofs'
    t=theory(parse((d/'bits.theory.sexp').read_bytes()),parse((d/'nat-add.theory.sexp').read_bytes()))
    g,p=artifacts(t)
    text=['; Paired input bits have equal widths by construction; the output keeps final carry.',
          '; Least significant bit first; bits-value is a mathematical natural number.',
          '(theory 3','  (']
    text+=['    '+canonical_bytes(x).decode() for x in t[2]]
    text+=['  )','  ()','  (']
    text+=['    '+canonical_bytes(x).decode() for x in t[4]]
    text+=['  ))']
    (d/'bit-sum-value.theory.sexp').write_text('\n'.join(text)+'\n')
    for kind,value in (('goal',g),('proof',p)):
        (d/f'bit-sum-value.{kind}.sexp').write_bytes(canonical_bytes(value))


if __name__=='__main__':
    main()
