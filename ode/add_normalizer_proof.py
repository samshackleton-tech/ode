"""Export symbolic addition-normalizer results using proved Word32 laws.

Variables, zero, and add32: flattening, reordering, and zero elimination.
Multiplicity is preserved. Nonzero constant folding is a separate export.
"""
from .canon import Sym, hash_of
from .add32_proof import artifacts as commutativity, identity_artifacts
from .add_associativity_proof import artifacts as associativity
from .proof_library import Library
from .proof_slice import slice_proof
from .xor32_proof import ZERO, Normalizer, Proof, app, equation, operation_term, var


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
    p = Normalizer('add32',ZERO,laws)
    a,lhs = p.normalize(left)
    b,rhs = p.normalize(right)
    if a != b:
        raise ValueError('addition expressions have different operand multisets')
    p.trans(lhs,p.sym(rhs))
    goal = [var('goal'),3,hash_of(t),parameters,equation(left,right)]
    proof = [var('proof'),3,hash_of(goal),lib.lemmas,[var('derive'),p.steps]]
    return goal,slice_proof(proof)


def export_normalizer(t, expression):
    from .check import Dag
    dag, variables = Dag(), set()

    def input_node(term):
        if isinstance(term,Sym):
            variables.add(term)
            return dag.var(term)
        if term == ZERO:
            return dag.const(0)
        if isinstance(term,list) and len(term)==3 and term[0]=='add32':
            return dag.add(input_node(term[1]),input_node(term[2]))
        raise ValueError('symbolic addition export supports variables, zero, and add32')

    def output_term(i):
        node=dag.nodes[i]
        if node[0]=='var':
            return var(node[1])
        if node[0]=='const' and node[1]==0:
            return ZERO
        if node[0]=='add' and node[2]==0:
            return operation_term('add32',ZERO,[output_term(j) for j in node[1]])
        raise ValueError('normalizer returned an unsupported addition result')

    result = output_term(input_node(expression))
    parameters = [[v,var('Word32')] for v in sorted(variables)]
    return prove(t,parameters,expression,result)
