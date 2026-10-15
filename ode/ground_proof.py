"""Emit explicit definition-reduction proofs; no kernel import or evaluator oracle.

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
    """Memoized definition reduction with explicit proof steps.

    Requires a valid version-3 theory and well-sorted terms. A definition
    unfolds when its structural argument has a constructor head. Variables
    and applications whose structural argument is symbolic remain terms.
    This producer is outside the kernel's reliance set. The closed prove()
    interface additionally requires a constructor value as its result.
    """

    def __init__(self, theory, reductions=None):
        super().__init__()
        assert theory[0] == 'theory' and theory[1] == 3, 'requires a version-3 theory'
        self.definitions = {d[0]: d for d in theory[4]}
        self.constructors = {'zero', 'succ'}
        for sort in theory[2]:
            if isinstance(sort, list):
                self.constructors.update(c[0] for c in sort[1])
        self.symbols = self.constructors | set(self.definitions) | {d[0] for d in theory[3]}
        # Producer-supplied closed evaluation lemmas, already earlier in the
        # enclosing proof: canonical application -> (value, lemma index).
        # The kernel checks their derivations and every use independently.
        self.reductions = {} if reductions is None else reductions
        self.cache = {}

    def evaluate(self, term):
        key = canonical_bytes(term)
        if key in self.cache:
            return self.cache[key]
        if isinstance(term, Sym):
            result = term, self.refl(term)
            self.cache[key] = result
            return result
        assert term[0] in self.symbols, 'evaluation requires declared functions or constructors'
        args = [self.evaluate(a) for a in term[1:]]
        values = [a for a, _ in args]
        reduced = app(term[0], *values)
        start = self.cong(term[0], *[proof for _, proof in args])
        definition = self.definitions.get(term[0])
        known = self.reductions.get(canonical_bytes(reduced))
        if known is not None:
            value, index = known
            result = value, self.trans(start, self.lemma(index))
        elif (definition is not None and isinstance(values[0], list)
                and values[0][0] in self.constructors):
            _, params, _, cases = definition
            _, fields, body = next(c for c in cases if c[0] == values[0][0])
            env = {param[0]: value for param, value in zip(params, values)}
            env.update(zip(fields, values[0][1:]))
            unfolded = self.unfold(term[0], *values)
            value, end = self.evaluate(substitute(body, env))
            result = value, self.trans(start, unfolded, end)
        else:
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
    pending = [value]
    while pending:
        term = pending.pop()
        assert isinstance(term,list) and term[0] in p.constructors, 'closed proof requires constructor values'
        pending.extend(term[1:])
    # Evaluation may return a cached earlier step; explicitly conclude it.
    p.trans(last, p.refl(right))
    g = [var('goal'), 3, hash_of(t), [], app('eq', left, right)]
    proof = [var('proof'), 3, hash_of(g), [], [var('derive'), p.steps]]
    return g, proof
