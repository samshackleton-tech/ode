"""Shared equality-step construction and proved-law algebraic normalization.

This producer code knows no word width or numeric domain. The caller
supplies the operation, zero term, and proof steps for its laws.
The kernel independently checks all statements and every emitted step.
"""
from .canon import Sym, canonical_bytes


def app(f, *args):
    return [Sym(f), *args]


def var(name):
    return Sym(name)


def equation(a, b):
    return app('eq', a, b)


class Proof:
    def __init__(self):
        self.steps = []

    def emit(self, rule, *args):
        i = len(self.steps)
        self.steps.append(app(rule, *args))
        return i

    def refl(self, t):
        return self.emit('refl', t)

    def sym(self, p):
        return self.emit('sym', p)

    def trans(self, *proofs):
        assert proofs, 'transitivity needs at least one proof reference'
        p = proofs[0]
        for q in proofs[1:]:
            p = self.emit('trans', p, q)
        return p

    def cong(self, f, *proofs):
        return self.emit('cong', Sym(f), *proofs)

    def unfold(self, f, *args):
        return self.emit('unfold', Sym(f), *args)

    def lemma(self, n, *args):
        return self.emit('lemma', n, *args)


def operation_term(operation, zero, atoms):
    if not atoms:
        return zero
    out = atoms[-1]
    for a in reversed(atoms[:-1]):
        out = app(operation, a, out)
    return out


def lemma_rules(indices):
    """Proof-instruction prefixes for a named collection of earlier lemmas."""
    return {name:app('lemma',index) for name,index in indices.items()}


class Normalizer(Proof):
    """Producer-side commutative-monoid normalization, with proved cancellation.

    laws maps named identities to proof-instruction prefixes, such as
    (lemma 40) or (unfold add (zero)). The optional cancel/pair laws enable
    XOR cancellation; addition keeps multiplicities.
    Every operation emits a proof; the kernel checks those lemmas and the
    resulting steps, regardless of the producer's configuration.
    """

    def __init__(self, operation, zero, laws):
        super().__init__()
        self.operation, self.zero = operation, zero
        self.laws = laws
        assert set(self.laws) in ({'right','comm','assoc','left','exchange'},
                                  {'right','comm','assoc','cancel','left','pair','exchange'})

    def order_key(self, atom):
        return canonical_bytes(atom)

    def term(self, atoms):
        return operation_term(self.operation, self.zero, atoms)

    def law(self, name, *args):
        return self.emit(*self.laws[name], *args)

    def insert(self, atom, ordered):
        if not ordered:
            return [atom], self.law('right', atom)
        head, *tail = ordered
        if atom == head and 'cancel' in self.laws:
            return tail, (self.law('cancel', atom) if not tail
                          else self.law('pair', atom, self.term(tail)))
        if self.order_key(atom) <= self.order_key(head):
            return [atom] + ordered, self.refl(app(self.operation, atom, self.term(ordered)))
        if not tail:
            return [head, atom], self.law('comm', atom, head)
        rest, q = self.insert(atom, tail)
        p = self.law('exchange', atom, head, self.term(tail))
        r = self.cong(self.operation, self.refl(head), q)
        if not rest:
            return [head], self.trans(p, r, self.law('right', head))
        return [head] + rest, self.trans(p, r)

    def merge(self, left, right):
        if not left:
            return right, self.law('left', self.term(right))
        if not right:
            return left, self.law('right', self.term(left))
        head, *tail = left
        if not tail:
            return self.insert(head, right)
        p = self.law('assoc', head, self.term(tail), self.term(right))
        rest, q = self.merge(tail, right)
        r = self.cong(self.operation, self.refl(head), q)
        out, s = self.insert(head, rest)
        return out, self.trans(p, r, s)

    def normalize(self, term):
        if term == self.zero:
            return [], self.refl(term)
        if not (isinstance(term, list) and len(term) == 3 and term[0] == self.operation):
            return [term], self.refl(term)
        left, p = self.normalize(term[1])
        right, q = self.normalize(term[2])
        r = self.cong(self.operation, p, q)
        atoms, s = self.merge(left, right)
        return atoms, self.trans(r, s)

