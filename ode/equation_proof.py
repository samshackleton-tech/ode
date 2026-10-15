"""Prove a Word32 equation, or ask for a proof of the residual equation.

A request is an ordinary owner-theory goal, not a new hint language.
A supplied proof becomes a checked lemma in the final derivation.
Normalization failure makes no claim that the equation is false.
"""
from .canon import hash_of
from .arx_proof import export_normalizer
from .proof_library import Library
from .proof_slice import slice_proof
from .xor32_proof import ZERO,Proof,app,equation,prove as prove_xor,var


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
    left,right=goal[4][1:]
    difference=app('xor32',left,right)
    normal_goal,normal_proof=export_normalizer(theory,difference)
    declared={name for name,_ in goal[3]}
    assert len(declared)==len(goal[3]), 'goal parameters must be distinct'
    assert all(name in declared for name,_ in normal_goal[3]), 'equation contains undeclared inputs'
    remainder=normal_goal[4][2]
    residual=[var('goal'),3,goal[2],goal[3],equation(remainder,ZERO)]
    if remainder!=ZERO and residual_proof is None:
        raise NeedProof(residual)
    if remainder==ZERO:
        assert residual_proof is None, 'no residual proof is needed for this equation'

    library=Library(goal[2])
    normalization=library.include(normal_goal,normal_proof)
    hint=library.include(residual,residual_proof) if residual_proof is not None else None
    # XOR cancellation turns a proof that left XOR right is zero into the
    # requested equality. These bridge identities are themselves proved.
    bridge=app('xor32',difference,right)
    left_bridge=library.include(*prove_xor(theory,goal[3],bridge,left))
    right_bridge=library.include(*prove_xor(theory,goal[3],app('xor32',ZERO,right),right))
    args=[name for name,_ in goal[3]]
    p=Proof()
    first=p.sym(p.lemma(left_bridge,*args))
    middle=p.lemma(normalization,*[name for name,_ in normal_goal[3]])
    if hint is not None:
        middle=p.trans(middle,p.lemma(hint,*args))
    middle=p.cong('xor32',middle,p.refl(right))
    p.trans(first,middle,p.lemma(right_bridge,*args))
    return slice_proof([var('proof'),3,hash_of(goal),library.lemmas,[var('derive'),p.steps]])
