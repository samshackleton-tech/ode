"""Export symbolic addition-normalizer results using proved Word32 laws.

Variables, literal Word32 constants, and add32: flattening, reordering,
zero elimination, and constant folding. Multiplicity is preserved.
"""
from .canon import hash_of
from .add32_proof import artifacts as commutativity, identity_artifacts
from .add_associativity_proof import artifacts as associativity
from .proof_library import Library
from .proof_slice import slice_proof
from .mixed_constant_proof import NormalizerWithConstants
from .xor32_proof import ZERO, Proof, app, equation, var


def library(t):
    lib = Library(hash_of(t))
    laws = {}
    for name,maker in (('comm',commutativity),('right',identity_artifacts),('assoc',associativity)):
        laws[name] = lib.include(*maker(t))
    x,y,z = map(var,('x','y','z'))
    p = Proof()
    p.trans(p.lemma(laws['comm'],ZERO,x),p.lemma(laws['right'],x))
    laws['left'] = lib.add([var('lemma'),[[x,var('Word32')]],
                            equation(app('add32',ZERO,x),x),[var('derive'),p.steps]])
    p = Proof()
    first = p.sym(p.lemma(laws['assoc'],x,y,z))
    middle = p.cong('add32',p.lemma(laws['comm'],x,y),p.refl(z))
    p.trans(first,middle,p.lemma(laws['assoc'],y,x,z))
    laws['exchange'] = lib.add([var('lemma'),[[v,var('Word32')] for v in (x,y,z)],
        equation(app('add32',x,app('add32',y,z)),app('add32',y,app('add32',x,z))),
        [var('derive'),p.steps]])
    return lib,laws


def prove(t, parameters, left, right):
    lib,laws = library(t)
    p = NormalizerWithConstants(t,lib,'add32',laws)
    a,lhs = p.normalize(left)
    b,rhs = p.normalize(right)
    if a != b:
        raise ValueError('addition expressions have different operand multisets')
    p.trans(lhs,p.sym(rhs))
    goal = [var('goal'),3,hash_of(t),parameters,equation(left,right)]
    proof = [var('proof'),3,hash_of(goal),lib.lemmas,[var('derive'),p.steps]]
    return goal,slice_proof(proof)
