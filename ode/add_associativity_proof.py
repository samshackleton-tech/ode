"""Prove Word32 addition associativity using a two-carry invariant.

The two carry bits from chained additions are compared as sorted pairs
(AND, OR). Proved five-bit identities transport that invariant through
one bit position; only 32 such positions are needed for Word32.
"""
from .canon import hash_of
from .add32_proof import artifacts as commutativity
from .carry_proof import artifacts as carry_artifacts
from .proof_slice import slice_proof
from .proof_library import Library
from .equational_proof import Proof, app, equation, var


def artifacts(t):
    library = Library(hash_of(t))
    comm_index = library.include(*commutativity(t))
    rules = {name: library.include(g,p) for name,g,p in carry_artifacts(t)}
    lemmas = library.lemmas
    x,y,z = map(var,('x','y','z'))
    params = [[v,var('Word32')] for v in (x,y,z)]
    xy,yz = app('add32',x,y),app('add32',y,z)
    left,right = app('add32',xy,z),app('add32',yz,x)
    invariants = {}

    def pair(i,u,v,w):
        return app(f'carry-{i}',u,v),app(f'carry-{i}',app('add32',u,v),w)

    def advance(p,i,u,v,w):
        """Prove the two carry recurrences in terms of input bits."""
        at = f'bit-at-{i-1}'
        first = p.lemma(8+i,u,v)
        second = p.lemma(8+i,app('add32',u,v),w)
        if i:
            inner = p.cong('carry-bit',p.lemma(72+i-1,u,v),p.refl(app(at,w)),
                           p.refl(pair(i-1,u,v,w)[1]))
            second = p.trans(second,inner)
        return first,second

    def canonical_transport(p,op,a,b,c,lo,hi):
        """Transport an outgoing encoded pair using the previous invariant."""
        first = p.cong('carry-bit',p.refl(a),p.refl(b),lo)
        summed = p.cong('xor-bit',p.refl(app('xor-bit',a,b)),lo)
        second = p.cong('carry-bit',summed,p.refl(c),hi)
        return p.cong(op,first,second)

    for i in range(32):
        for op in ('and-bit','or-bit'):
            p = Proof()
            lhs = p.cong(op,*advance(p,i,x,y,z))
            rhs = p.cong(op,*advance(p,i,y,z,x))
            if i==0:
                p.trans(lhs,p.sym(rhs))
            else:
                a,b,c = (app(f'bit-at-{i-1}',v) for v in (x,y,z))
                lp,lq = pair(i-1,x,y,z)
                rp,rq = pair(i-1,y,z,x)
                first = p.lemma(rules[f'carry-left-{op}'],a,b,c,lp,lq)
                lo = p.lemma(invariants[i-1,'and-bit'],x,y,z)
                hi = p.lemma(invariants[i-1,'or-bit'],x,y,z)
                middle = canonical_transport(p,op,a,b,c,lo,hi)
                last = p.lemma(rules[f'carry-right-{op}'],a,b,c,rp,rq)
                p.trans(lhs,first,middle,p.sym(last),p.sym(rhs))
            invariants[i,op] = len(lemmas)
            lemmas.append([var('lemma'),params,
                equation(app(op,*pair(i,x,y,z)),app(op,*pair(i,y,z,x))),
                [var('derive'),p.steps]])

    def sum_projection(p,i,u,v,w):
        at = f'bit-at-{i}'
        inner = p.cong('xor-bit',p.lemma(72+i,u,v),p.refl(app(at,w)))
        outer = p.cong('xor-bit',inner,p.refl(pair(i,u,v,w)[1]))
        return p.trans(p.lemma(72+i,app('add32',u,v),w),outer)

    p, components = Proof(), []
    for i in range(32):
        a,b,c = (app(f'bit-at-{i}',v) for v in (x,y,z))
        lp,lq = pair(i,x,y,z)
        rp,rq = pair(i,y,z,x)
        lhs = sum_projection(p,i,x,y,z)
        first = p.lemma(rules['carry-left-sum'],a,b,c,lp,lq)
        lo = p.lemma(invariants[i,'and-bit'],x,y,z)
        hi = p.lemma(invariants[i,'or-bit'],x,y,z)
        middle = p.cong('xor-bit',p.refl(app('xor-bit',app('xor-bit',a,b),c)),
                        p.cong('xor-bit',lo,hi))
        last = p.lemma(rules['carry-right-sum'],a,b,c,rp,rq)
        rhs = sum_projection(p,i,y,z,x)
        components.append(p.trans(lhs,first,middle,p.sym(last),p.sym(rhs)))
    middle = p.cong('word32',*components)
    p.trans(p.sym(p.lemma(4,left)),middle,p.lemma(4,right),p.lemma(comm_index,yz,x))
    goal = [var('goal'),3,hash_of(t),params,equation(left,app('add32',x,yz))]
    proof = [var('proof'),3,hash_of(goal),lemmas,[var('derive'),p.steps]]
    return goal,slice_proof(proof)
