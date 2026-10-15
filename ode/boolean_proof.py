"""Produce Boolean identities by exhaustive, kernel-checked constructor cases.

Each leaf emits evaluation derivations from the theory. Each internal
node is an ordinary two-case induction referencing its earlier child
lemmas. No truth-table rule, axiom, or kernel callback is involved.
"""
from itertools import product
from .canon import Sym, canonical_bytes, hash_of
from .ground_proof import Evaluation, substitute
from .xor32_proof import app, equation, var


def prove(theory, variables, left, right):
    """Prove an equation universally over at most eight Boolean variables.

    The theory must be valid and define Bit with bit0/bit1 constructors.
    Both terms must be well-sorted and closed after substituting variables.
    Case enumeration costs 2**len(variables); the limit bounds the producer's
    enumeration, not the mathematical domain of Word32 proofs that use it.
    """
    assert len(variables) <= 8, 'Boolean enumeration supports at most eight variables'
    assert all(type(v) is Sym for v in variables), 'variables must be symbols'
    assert len(set(variables)) == len(variables), 'variables must be distinct'
    lemmas, reductions = [], {}
    # Repeated case leaves share the small closed evaluations they use.
    # This table contains proved equations, not assumed truth values.
    used = set()
    pending = [left,right]
    while pending:
        term = pending.pop()
        if isinstance(term,list):
            used.add(term[0])
            pending.extend(term[1:])
    for name,params,result,_ in theory[4]:
        if (name not in used or result!='Bit' or len(params)>3
                or any(sort!='Bit' for _,sort in params)):
            continue
        for bits in product(('bit0','bit1'),repeat=len(params)):
            term = app(name,*[app(bit) for bit in bits])
            p = Evaluation(theory)
            value,last = p.evaluate(term)
            p.trans(last,p.refl(value))
            reductions[canonical_bytes(term)] = value,len(lemmas)
            lemmas.append([var('lemma'),[],equation(term,value),[var('derive'),p.steps]])

    def cases(remaining, a, b):
        params = [[v, var('Bit')] for v in remaining]
        if not remaining:
            p = Evaluation(theory,reductions)
            lhs, x = p.evaluate(a)
            rhs, y = p.evaluate(b)
            if lhs != rhs:
                raise ValueError('Boolean identity has a false constructor instance')
            p.trans(x, p.sym(y))
            derivation = [var('derive'), p.steps]
        else:
            v, *tail = remaining
            branches = []
            for constructor in ('bit0', 'bit1'):
                mapping = {v: app(constructor)}
                index = cases(tail, substitute(a, mapping), substitute(b, mapping))
                branches.append([var(constructor), [], [app('lemma', index, *tail)]])
            derivation = [var('induct'), v, branches]
        index = len(lemmas)
        lemmas.append([var('lemma'), params, equation(a,b), derivation])
        return index

    cases(list(variables), left, right)
    _, params, eq, derivation = lemmas.pop()
    goal = [var('goal'), 3, hash_of(theory), params, eq]
    proof = [var('proof'), 3, hash_of(goal), lemmas, derivation]
    return goal, proof
