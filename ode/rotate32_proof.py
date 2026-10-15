"""Proof-producing Word32 rotation/XOR normalization, outside the kernel.

Each ror-N is defined as a permutation of exactly 32 bit fields, with
field 0 the least significant bit. Projection lemmas and XOR proofs use
only the existing constructor, equality, and induction rules. The kernel
never runs this producer's arithmetic on bit indices.
"""
from .canon import Sym, hash_of
from .xor32_proof import bit_lemmas, theory as xor_theory, word_lemmas
from .equational_proof import Normalizer, Proof, app, equation, var, lemma_rules


BIT_LAWS = {'right': 1, 'comm': 3, 'assoc': 5, 'cancel': 6,
            'left': 40, 'pair': 41, 'exchange': 42}


def rotation_count(term):
    """Return the count for a ror-N application, otherwise None."""
    if not (isinstance(term, list) and len(term) == 2
            and isinstance(term[0], Sym) and term[0].startswith('ror-')):
        return None
    digits = term[0][4:]
    if not digits.isascii() or not digits.isdigit():
        raise ValueError('rotation name must be ror-N, with 0 <= N < 32')
    n = int(digits)
    if str(n) != digits or not 0 <= n < 32:
        raise ValueError('rotation name must be ror-N, with 0 <= N < 32')
    return n


def theory(bit_theory):
    t = xor_theory(bit_theory)
    names = [var(f'b{i}') for i in range(32)]
    for n in range(32):
        body = app('word32', *[names[(i + n) % 32] for i in range(32)])
        t[4].append([var(f'ror-{n}'), [[var('x'), var('Word32')]], var('Word32'),
                     [[var('word32'), names, body]]])
    return t


def helpers():
    """Boolean left identity, double cancellation, and exchange (40..42)."""
    a,b,c = map(var, ('a','b','c'))
    xor = lambda x,y: app('xor-bit',x,y)
    bit0 = app('bit0')
    result = []
    p = Proof()
    p.unfold('xor-bit', bit0, a)
    result.append([var('lemma'), [[a,var('Bit')]], equation(xor(bit0,a),a),
                   [var('derive'),p.steps]])
    p = Proof()
    one = p.sym(p.lemma(5,a,a,b))
    two = p.cong('xor-bit',p.lemma(6,a),p.refl(b))
    p.trans(one,two,p.lemma(40,b))
    result.append([var('lemma'), [[a,var('Bit')],[b,var('Bit')]],
                   equation(xor(a,xor(a,b)),b), [var('derive'),p.steps]])
    p = Proof()
    one = p.sym(p.lemma(5,a,b,c))
    two = p.cong('xor-bit',p.lemma(3,a,b),p.refl(c))
    p.trans(one,two,p.lemma(5,b,a,c))
    result.append([var('lemma'), [[v,var('Bit')] for v in (a,b,c)],
                   equation(xor(a,xor(b,c)),xor(b,xor(a,c))), [var('derive'),p.steps]])
    return result


def projection_lemma(n, i):
    """bit-at-i(ror-N(x)) = bit-at-((i+N) mod 32)(x), derived by cases."""
    x = var('x')
    names = [var(f'b{j}') for j in range(32)]
    value = app('word32', *names)
    rotated = app('word32', *[names[(j+n) % 32] for j in range(32)])
    before, after = f'bit-at-{i}', f'bit-at-{(i+n) % 32}'
    p = Proof()
    one = p.unfold(f'ror-{n}',value)
    two = p.cong(before,one)
    three = p.unfold(before,rotated)
    left = p.trans(two,three)
    right = p.unfold(after,value)
    p.trans(left,p.sym(right))
    return [var('lemma'), [[x,var('Word32')]],
            equation(app(before,app(f'ror-{n}',x)),app(after,x)),
            [var('induct'),x,[[var('word32'),names,p.steps]]]]


class Producer:
    def __init__(self):
        # Use one XOR proof algorithm for bits and words. Only proved lemma
        # indices and the operation/identity differ; no new kernel rule.
        self.p = Normalizer('xor-bit', app('bit0'), lemma_rules(BIT_LAWS))
        self.lemmas = bit_lemmas() + word_lemmas() + helpers()
        self.rotations = {}

    def projection_rule(self, n, i):
        if (n,i) not in self.rotations:
            self.rotations[n,i] = len(self.lemmas)
            self.lemmas.append(projection_lemma(n,i))
        return self.rotations[n,i]

    def project(self, i, term):
        """Prove a projection equal to a Boolean XOR expression."""
        p, at = self.p, f'bit-at-{i}'
        if isinstance(term,list) and term and term[0]=='word32':
            from .word_literal import word_value
            word_value(term)  # Validate the exact constructor width and fields.
            return term[i+1], p.unfold(at,term)
        n = rotation_count(term)
        if n is not None:
            value, inner = self.project((i+n) % 32, term[1])
            outer = p.lemma(self.projection_rule(n,i),term[1])
            return value, p.trans(outer,inner)
        if isinstance(term,list) and len(term)==3 and term[0]=='xor32':
            a,b = term[1:]
            x,pa = self.project(i,a)
            y,pb = self.project(i,b)
            outer = p.lemma(8+i,a,b)
            inner = p.cong('xor-bit',pa,pb)
            return app('xor-bit',x,y), p.trans(outer,inner)
        if isinstance(term,Sym):
            return app(at,term), p.refl(app(at,term))
        raise ValueError('rotation/XOR export supports variables, Word32 literals, xor32, and ror-N')


def prove(t, parameters, left, right):
    producer = Producer()
    p, components = producer.p, []
    for i in range(32):
        lhs,a = producer.project(i,left)
        rhs,b = producer.project(i,right)
        xs,c = p.normalize(lhs)
        ys,d = p.normalize(rhs)
        if xs != ys:
            raise ValueError(f'bit {i} has different parity-normal forms')
        components.append(p.trans(a,c,p.sym(d),p.sym(b)))
    middle = p.cong('word32',*components)
    p.trans(p.sym(p.lemma(7,left)),middle,p.lemma(7,right))
    goal = [var('goal'),3,hash_of(t, 'theory'),parameters,equation(left,right)]
    proof = [var('proof'),3,hash_of(goal, 'goal'),producer.lemmas,[var('derive'),p.steps]]
    return goal,proof
