"""Prove a Word32 equation, or ask for a proof of the residual equation.

A request is an ordinary owner-theory goal, not a new hint language.
A supplied proof becomes a checked lemma in the final derivation.
Normalization failure makes no claim that the equation is false.
"""
from .canon import hash_of
from .arx_proof import Normalization
from .proof_slice import slice_proof
from .xor32_proof import equation,var


class NeedProof(Exception):
    """The producer needs a proof of goal to finish the requested equation."""
    def __init__(self,goal):
        super().__init__('normalization leaves a residual equality to prove')
        self.goal=goal


def produce(theory,goal,residual_proof=None):
    """Produce a proof of a supplied Word32 equation or raise NeedProof.

    Requires a version-3 owner goal in this theory, with Word32 parameters
    and arithmetic expressions supported by the common exporter. Extra
    unused parameters are permitted. A supplied residual proof must name
    exactly the requested residual goal; the recipient kernel checks it.
    """
    assert goal[0:2]==[var('goal'),3] and len(goal)==5, 'requires a version-3 goal'
    assert goal[2]==hash_of(theory), 'goal names a different theory'
    assert all(sort=='Word32' for _,sort in goal[3]), 'requires Word32 parameters'
    assert goal[4][0]=='eq' and len(goal[4])==3, 'requires an equation'
    declared={name for name,_ in goal[3]}
    assert len(declared)==len(goal[3]), 'goal parameters must be distinct'
    context=Normalization(theory)
    left,left_proof=context.normalize(goal[4][1])
    right,right_proof=context.normalize(goal[4][2])
    assert context.variables <= declared, 'equation contains undeclared inputs'
    residual=[var('goal'),3,goal[2],goal[3],equation(context.output(left),context.output(right))]
    if left!=right and residual_proof is None:
        raise NeedProof(residual)
    if left==right:
        assert residual_proof is None, 'no residual proof is needed for this equation'

    p=context.proof
    steps=[left_proof]
    if residual_proof is not None:
        hint=context.library.include(residual,residual_proof)
        steps.append(p.lemma(hint,*[name for name,_ in goal[3]]))
    steps.append(p.sym(right_proof))
    p.trans(*steps)
    return slice_proof([var('proof'),3,hash_of(goal),context.library.lemmas,[var('derive'),p.steps]])
