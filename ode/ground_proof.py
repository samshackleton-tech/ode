"""Emit explicit evaluation derivations; no kernel import or evaluator oracle.

Memoized constructor evaluation shares repeated carry stages. Every
reduction emits unfolding and congruence steps checked independently.
"""
from .canon import Sym, canonical_bytes, hash_of
from .xor32_proof import Proof, app, var


def substitute(term, env):
    """Simultaneous substitution; variables outside env stay unchanged."""
    if isinstance(term, Sym):
        return env.get(term, term)
    return [term[0]] + [substitute(a, env) for a in term[1:]]


class Evaluation(Proof):
    """Memoized closed evaluation with explicit proof steps.

    Requires a valid version-3 theory and well-sorted closed terms whose
    evaluation terminates in constructor values. Uninterpreted functions
    cannot be evaluated. This producer is outside the kernel's reliance set.
    """

    def __init__(self, theory):
        super().__init__()
        assert theory[0] == 'theory' and theory[1] == 3, 'requires a version-3 theory'
        self.definitions = {d[0]: d for d in theory[4]}
        self.constructors = {'zero', 'succ'}
        for sort in theory[2]:
            if isinstance(sort, list):
                self.constructors.update(c[0] for c in sort[1])
        self.cache = {}

    def evaluate(self, term):
        key = canonical_bytes(term)
        if key in self.cache:
            return self.cache[key]
        args = [self.evaluate(a) for a in term[1:]]
        values = [a for a, _ in args]
        reduced = app(term[0], *values)
        start = self.cong(term[0], *[proof for _, proof in args])
        if term[0] in self.definitions:
            _, params, _, cases = self.definitions[term[0]]
            _, fields, body = next(c for c in cases if c[0] == values[0][0])
            env = {param[0]: value for param, value in zip(params, values)}
            env.update(zip(fields, values[0][1:]))
            unfolded = self.unfold(term[0], *values)
            value, end = self.evaluate(substitute(body, env))
            result = value, self.trans(start, unfolded, end)
        else:
            assert term[0] in self.constructors, 'closed evaluation requires constructor values'
            result = reduced, start
        self.cache[key] = result
        return result


def prove(t, left, right):
    """Prove a closed term equals a proposed constructor value.

    Evaluation's preconditions apply. The recipient checks the emitted
    proof against its independently selected theory and goal.
    """
    p = Evaluation(t)
    value, last = p.evaluate(left)
    assert value == right, 'proposed result differs from constructor evaluation'
    # Evaluation may return a cached earlier step; explicitly conclude it.
    p.trans(last, p.refl(right))
    g = [var('goal'), 3, hash_of(t), [], app('eq', left, right)]
    proof = [var('proof'), 3, hash_of(g), [], [var('derive'), p.steps]]
    return g, proof
