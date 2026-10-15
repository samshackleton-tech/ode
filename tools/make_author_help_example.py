#!/usr/bin/env pypy3
"""An end-to-end residual-proof handoff for a missing complement identity."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT))
from ode.canon import canonical_bytes,hash_of,parse
from ode.complement_proof import artifacts
from ode.equation_proof import NeedProof,produce
from ode.word_literal import literal
from ode.equational_proof import app, var


def main():
    d=ROOT/'examples'/'proofs'
    t=parse((d/'arx.theory.sexp').read_bytes());x=var('x');ones=literal(0xffffffff)
    goal=[var('goal'),3,hash_of(t),[[x,var('Word32')]],
          app('eq',app('add32',x,app('xor32',x,ones)),ones)]
    try:
        produce(t,goal)
    except NeedProof as request:
        residual=request.goal
    else:
        raise AssertionError('this example expects an unresolved identity')
    answer_goal,answer=artifacts(t)
    assert answer_goal==residual, 'author answer must address the exact requested goal'
    proof=produce(t,goal,answer)
    for name,g,p in (('complement',goal,proof),('complement-residual',residual,answer)):
        for kind,value in (('goal',g),('proof',p)):
            (d/f'{name}.{kind}.sexp').write_bytes(canonical_bytes(value))


if __name__=='__main__':
    main()
