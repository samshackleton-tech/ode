"""An untrusted proof producer for natural-number addition.

It emits proofs of identity, successor, commutativity, associativity,
and exchange from the defining equations of add; then it uses those
proved lemmas to normalize sums. No kernel, evaluator, or solver import.
The kernel independently checks every inference, including all lemmas.
This is natural arithmetic, not modular-u32 arithmetic.
"""
from .canon import Sym, canonical_bytes, hash_of, parse


def arithmetic_lemmas():
    """Closed lemmas, in dependency order; indices are used by the producer."""
    return parse('''(
      (lemma ((a Nat)) (eq (add a (zero)) a)
        (induct a k
          ((unfold add (zero) (zero)))
          ((unfold add (succ k) (zero)) (ih) (cong succ 1) (trans 0 2))))

      (lemma ((a Nat) (b Nat)) (eq (add a (succ b)) (succ (add a b)))
        (induct a k
          ((unfold add (zero) (succ b))
           (unfold add (zero) b) (cong succ 1) (sym 2) (trans 0 3))
          ((unfold add (succ k) (succ b))
           (ih b) (cong succ 1) (trans 0 2)
           (unfold add (succ k) b) (cong succ 4) (sym 5) (trans 3 6))))

      (lemma ((a Nat) (b Nat)) (eq (add a b) (add b a))
        (induct a k
          ((unfold add (zero) b) (lemma 0 b) (sym 1) (trans 0 2))
          ((unfold add (succ k) b) (ih b) (cong succ 1) (trans 0 2)
           (lemma 1 b k) (sym 4) (trans 3 5))))

      (lemma ((a Nat) (b Nat) (c Nat))
        (eq (add (add a b) c) (add a (add b c)))
        (induct a k
          ((unfold add (zero) b) (refl c) (cong add 0 1)
           (unfold add (zero) (add b c)) (sym 3) (trans 2 4))
          ((unfold add (succ k) b) (refl c) (cong add 0 1)
           (unfold add (succ (add k b)) c) (trans 2 3)
           (ih b c) (cong succ 5) (trans 4 6)
           (unfold add (succ k) (add b c)) (sym 8) (trans 7 9))))

      (lemma ((a Nat) (b Nat) (c Nat))
        (eq (add a (add b c)) (add b (add a c)))
        (derive
          ((lemma 3 a b c) (sym 0) (lemma 2 a b) (refl c)
           (cong add 2 3) (trans 1 4) (lemma 3 b a c) (trans 5 6))))
    )''')


def add(a, b):
    return [Sym('add'), a, b]


def sum_term(atoms):
    """Right-associated sum; zero and singleton have their own terms."""
    if not atoms:
        return [Sym('zero')]
    out = atoms[-1]
    for atom in reversed(atoms[:-1]):
        out = add(atom, out)
    return out


class Producer:
    def __init__(self):
        self.steps = []
        self.ids = {}

    def emit(self, rule, *args):
        step = [Sym(rule), *args]
        key = canonical_bytes(step)
        if key not in self.ids:
            self.ids[key] = len(self.steps)
            self.steps.append(step)
        return self.ids[key]

    def refl(self, t):
        return self.emit('refl', t)

    def trans(self, *proofs):
        out = proofs[0]
        for proof in proofs[1:]:
            out = self.emit('trans', out, proof)
        return out

    def insert(self, atom, ordered):
        """Proof: add(atom, sum(ordered)) = sum(sorted insertion)."""
        if not ordered:
            return [atom], self.emit('lemma', 0, atom)
        head, *tail = ordered
        if canonical_bytes(atom) <= canonical_bytes(head):
            return [atom] + ordered, self.refl(add(atom, sum_term(ordered)))
        if not tail:
            return [head, atom], self.emit('lemma', 2, atom, head)
        rest, q = self.insert(atom, tail)
        p = self.emit('lemma', 4, atom, head, sum_term(tail))
        r = self.emit('cong', Sym('add'), self.refl(head), q)
        return [head] + rest, self.trans(p, r)

    def merge(self, left, right):
        """Proof: add(sum(left), sum(right)) = sum(merged)."""
        if not left:
            return right, self.emit('unfold', Sym('add'), [Sym('zero')], sum_term(right))
        if not right:
            return left, self.emit('lemma', 0, sum_term(left))
        head, *tail = left
        if not tail:
            return self.insert(head, right)
        p = self.emit('lemma', 3, head, sum_term(tail), sum_term(right))
        rest, q = self.merge(tail, right)
        r = self.emit('cong', Sym('add'), self.refl(head), q)
        result, s = self.insert(head, rest)
        return result, self.trans(p, r, s)

    def normalize(self, term):
        """Return ordered atoms and a proof term = sum(atoms)."""
        if term == [Sym('zero')]:
            return [], self.refl(term)
        if not (isinstance(term, list) and len(term) == 3 and term[0] == 'add'):
            return [term], self.refl(term)
        left, p = self.normalize(term[1])
        right, q = self.normalize(term[2])
        r = self.emit('cong', Sym('add'), p, q)
        atoms, s = self.merge(left, right)
        return atoms, self.trans(r, s)


def prove(theory, parameters, left, right):
    """Propose a goal and a proof. The owner selects the actual goal.

    The producer claims equality only when flattening and sorting sums
    gives the same list, counting multiplicity. Sorting is proof search,
    not a rule: the kernel checks the derivation it produces.
    """
    p = Producer()
    lhs, a = p.normalize(left)
    rhs, b = p.normalize(right)
    if lhs != rhs:
        raise ValueError('the two sums have different multisets of terms')
    # A deduplicated final step can refer back to an earlier proof. End the
    # block with an explicit reference via two symmetries in that case.
    last = p.trans(a, p.emit('sym', b))
    if last != len(p.steps) - 1:
        p.steps.append([Sym('sym'), last])
        p.steps.append([Sym('sym'), len(p.steps) - 1])
    goal = [Sym('goal'), 2, hash_of(theory), parameters, [Sym('eq'), left, right]]
    proof = [Sym('proof'), 2, hash_of(goal), arithmetic_lemmas(),
             [Sym('derive'), p.steps]]
    return goal, proof
