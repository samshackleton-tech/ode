"""Emit explicit evaluation derivations; no kernel import or evaluator oracle.

Memoized constructor evaluation shares repeated carry stages. Every
reduction emits unfolding and congruence steps checked independently.
"""
from .canon import Sym, canonical_bytes, hash_of
from .xor32_proof import Proof, app, var


def prove(t, left, right):
    """Prove a closed term equals a proposed constructor value.

    Requires a valid version-3 theory and a well-sorted closed term whose
    evaluation terminates in constructor values. Uninterpreted functions
    cannot be evaluated. The recipient checks the emitted proof with the
    kernel against its independently selected theory and goal.
    """
    assert t[0] == 'theory' and t[1] == 3, 'requires a version-3 theory'
    definitions = {d[0]:d for d in t[4]}
    constructors = {'zero', 'succ'}
    for sort in t[2]:
        if isinstance(sort, list):
            constructors.update(c[0] for c in sort[1])
    p, cache = Proof(), {}

    def substitute(term, env):
        if isinstance(term,Sym):
            return env[term]
        return [term[0]]+[substitute(a,env) for a in term[1:]]

    def evaluate(term):
        key=canonical_bytes(term)
        if key in cache:
            return cache[key]
        args=[evaluate(a) for a in term[1:]]
        values=[a for a,_ in args]
        reduced=app(term[0],*values)
        start=p.cong(term[0],*[proof for _,proof in args])
        if term[0] in definitions:
            _,params,_,cases=definitions[term[0]]
            constructor,fields,body=next(c for c in cases if c[0]==values[0][0])
            env={param[0]:value for param,value in zip(params,values)}
            env.update(zip(fields,values[0][1:]))
            unfolded=p.unfold(term[0],*values)
            value,end=evaluate(substitute(body,env))
            result=value,p.trans(start,unfolded,end)
        else:
            assert term[0] in constructors, 'closed evaluation requires constructor values'
            result=reduced,start
        cache[key]=result
        return result

    value,last=evaluate(left)
    assert value==right, 'proposed result differs from constructor evaluation'
    # evaluate() may return a cached earlier step; explicitly conclude it.
    p.trans(last,p.refl(right))
    g=[var('goal'),3,hash_of(t),[],app('eq',left,right)]
    proof=[var('proof'),3,hash_of(g),[],[var('derive'),p.steps]]
    return g,proof

