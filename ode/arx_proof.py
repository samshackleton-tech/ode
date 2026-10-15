"""Compose addition, rotation and XOR derivations for mixed expressions.

Dag proposes each normalized result. Arithmetic producers prove local
rewrites over abstract operands; lemma instantiation substitutes the actual
subexpressions. Congruence connects those rewrites to the original term.
The kernel checks the complete assembled proof against one Word32 theory.
"""
from .canon import Sym,canonical_bytes,hash_of
from .add32_proof import theory as addition_theory
from .rotate32_proof import theory as rotation_theory,rotation_count,prove as prove_rotation
from .add_normalizer_proof import prove as prove_addition
from .xor32_proof import ZERO,Proof,app,equation,operation_term,prove as prove_xor,var
from .constant_proof import literal,word_value
from .proof_library import Library
from .proof_slice import slice_proof


def theory(bit_theory):
    """One theory containing the existing addition, rotation and XOR definitions."""
    t=addition_theory(bit_theory)
    rotations=rotation_theory(bit_theory)
    assert t[2:4]==rotations[2:4], 'arithmetic theories must share their sorts and symbols'
    definitions={d[0]:d for d in t[4]}
    for definition in rotations[4]:
        name=definition[0]
        if name in definitions:
            assert definitions[name]==definition, 'arithmetic theories disagree on a shared definition'
        else:
            t[4].append(definition)
    return t


def abstract(left,right,operation):
    """Expose only the local algebra; name all other subexpressions as operands."""
    names,values={},[]

    def visit(term):
        if isinstance(term,list) and term:
            name=term[0]
            if name=='word32':
                return term
            relevant=(name==operation or
                      (operation=='rotation' and (name=='xor32' or rotation_count(term) is not None)))
            if relevant:
                return app(name,*[visit(a) for a in term[1:]])
        key=canonical_bytes(term)
        if key not in names:
            names[key]=var(f'v{len(values)}')
            values.append(term)
        return names[key]

    a,b=visit(left),visit(right)
    params=[[var(f'v{i}'),var('Word32')] for i in range(len(values))]
    return params,a,b,values


def export_normalizer(t,expression):
    """Export a complete mixed arithmetic expression, with explicit local proofs.

    Input consists of variables, literal Word32 constructors, add32, xor32,
    and immediate ror-N. Repeated input terms reuse a derivation. This is
    arithmetic expression normalization, not yet binary/ISA execution.
    """
    from .check import Dag
    dag,p,library=Dag(),Proof(),Library(hash_of(t))
    variables,cache,outputs=set(),{},{}

    def output(i):
        if i in outputs:
            return outputs[i]
        node=dag.nodes[i]
        if node[0]=='var':
            result=var(node[1])
        elif node[0]=='const':
            result=literal(node[1])
        elif node[0] in ('add','xor'):
            atoms=[output(j) for j in node[1]]
            if node[2]:
                atoms.append(literal(node[2]))
            result=operation_term(node[0]+'32',ZERO,atoms)
        elif node[0]=='rotr':
            result=app(f'ror-{node[2]}',output(node[1]))
        else:
            raise ValueError('normalizer returned an unsupported arithmetic node')
        outputs[i]=result
        return result

    def normalize(term):
        key=canonical_bytes(term)
        if key in cache:
            return cache[key]
        if isinstance(term,Sym):
            variables.add(term)
            result=dag.var(term),p.refl(term)
        elif isinstance(term,list) and term and term[0]=='word32':
            result=dag.const(word_value(term)),p.refl(term)
        else:
            assert isinstance(term,list) and term, 'requires a Word32 arithmetic expression'
            n=rotation_count(term)
            if n is not None:
                child,proof=normalize(term[1])
                index=dag.rotr(child,n)
                children=[child];proofs=[proof]
                maker,operation=prove_rotation,'rotation'
            else:
                assert len(term)==3 and term[0] in ('add32','xor32'), 'unsupported arithmetic operation'
                children,proofs=map(list,zip(*[normalize(a) for a in term[1:]]))
                if term[0]=='add32':
                    index=dag.add(*children)
                    maker,operation=prove_addition,'add32'
                else:
                    index=dag.xor(*children)
                    maker,operation=prove_xor,'xor32'
            normalized_input=app(term[0],*[output(i) for i in children])
            normalized_output=output(index)
            first=p.cong(term[0],*proofs)
            if normalized_input==normalized_output:
                result=index,first
            else:
                params,left,right,args=abstract(normalized_input,normalized_output,operation)
                goal,proof=maker(t,params,left,right)
                theorem=library.include(goal,proof)
                result=index,p.trans(first,p.lemma(theorem,*args))
        cache[key]=result
        return result

    index,last=normalize(expression)
    p.trans(last,p.refl(output(index)))
    params=[[v,var('Word32')] for v in sorted(variables)]
    goal=[var('goal'),3,hash_of(t),params,equation(expression,output(index))]
    proof=[var('proof'),3,hash_of(goal),library.lemmas,[var('derive'),p.steps]]
    return goal,slice_proof(proof)
