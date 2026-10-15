"""A proof producer for Word32 ripple-carry addition.

The theory defines the Boolean carry function and 32 carry stages.
Addition discards carry-out of bit 31, hence is modulo 2**32. The
producer proves carry symmetry and lifts it to addition commutativity;
no arithmetic axiom, native evaluator, or kernel import is involved.
"""
from .canon import hash_of, parse
from .xor32_proof import bit_lemmas, theory as xor_theory, word_lemmas
from .equational_proof import Proof, app, equation, var


def theory(bit_theory):
    t = xor_theory(bit_theory)
    t[4] += parse('''(
      (and-bit ((a Bit) (b Bit)) Bit ((bit0 () (bit0)) (bit1 () b)))
      (or-bit ((a Bit) (b Bit)) Bit ((bit0 () b) (bit1 () (bit1))))
      (carry-bit ((a Bit) (b Bit) (c Bit)) Bit
        ((bit0 () (and-bit b c)) (bit1 () (or-bit b c))))
    )''')
    fields = [var(f'b{i}') for i in range(32)]
    x, y = app('word32',*fields), var('y')
    params = parse('((x Word32) (y Word32))')
    for i in range(32):
        body = (app('bit0') if i==0 else
                app('carry-bit',fields[i-1],app(f'bit-at-{i-1}',y),
                    app(f'carry-{i-1}',x,y)))
        t[4].append([var(f'carry-{i}'),params,var('Bit'),
                     [[var('word32'),fields,body]]])
    bits = [app('xor-bit',app('xor-bit',fields[i],app(f'bit-at-{i}',y)),
                app(f'carry-{i}',x,y)) for i in range(32)]
    t[4].append([var('add32'),params,var('Word32'),
                 [[var('word32'),fields,app('word32',*bits)]]])
    return t


def carry_bit_lemmas():
    """Indices 5,6,7 after four Boolean XOR lemmas and Word32 eta."""
    def induct(eq, params, zero, one):
        return parse(f'''(lemma {params} {eq}
          (induct a ((bit0 () {zero}) (bit1 () {one}))))''')
    return [
        induct('(eq (carry-bit a (bit0) c) (and-bit a c))',
               '((a Bit) (c Bit))',
               '((unfold carry-bit (bit0) (bit0) c))',
               '''((unfold carry-bit (bit1) (bit0) c) (unfold or-bit (bit0) c)
                   (trans 0 1) (unfold and-bit (bit1) c) (sym 3) (trans 2 4))'''),
        induct('(eq (carry-bit a (bit1) c) (or-bit a c))',
               '((a Bit) (c Bit))',
               '''((unfold carry-bit (bit0) (bit1) c) (unfold and-bit (bit1) c)
                   (trans 0 1) (unfold or-bit (bit0) c) (sym 3) (trans 2 4))''',
               '((unfold carry-bit (bit1) (bit1) c))'),
        induct('(eq (carry-bit a b c) (carry-bit b a c))',
               '((a Bit) (b Bit) (c Bit))',
               '((unfold carry-bit (bit0) b c) (lemma 5 b c) (sym 1) (trans 0 2))',
               '((unfold carry-bit (bit1) b c) (lemma 6 b c) (sym 1) (trans 0 2))'),
    ]


def artifacts(t):
    lemmas = bit_lemmas()[:4] + [word_lemmas()[0]] + carry_bit_lemmas()
    params = parse('((x Word32) (y Word32))')
    x,y = var('x'),var('y')
    fields = [var(f'b{i}') for i in range(32)]
    value = app('word32',*fields)
    recurrences, symmetries, projections = [], [], []

    def save(eq, p, induct=False):
        i = len(lemmas)
        derivation = ([var('induct'),x,[[var('word32'),fields,p.steps]]]
                      if induct else [var('derive'),p.steps])
        lemmas.append([var('lemma'),params,eq,derivation])
        return i

    # Each recurrence is derived, not assumed: expose a word's fields,
    # unfold its defining case, then fold the projections back to x.
    for i in range(32):
        p = Proof()
        lhs = app(f'carry-{i}',x,y)
        if i==0:
            rhs = app('bit0')
            p.unfold('carry-0',value,y)
        else:
            at = f'bit-at-{i-1}'
            prev = app(f'carry-{i-1}',value,y)
            rhs = app('carry-bit',app(at,x),app(at,y),app(f'carry-{i-1}',x,y))
            a = p.unfold(f'carry-{i}',value,y)
            b = p.cong('carry-bit',p.unfold(at,value),p.refl(app(at,y)),p.refl(prev))
            p.trans(a,p.sym(b))
        recurrences.append(save(equation(lhs,rhs),p,induct=True))

    # Symmetry of successive carries, using only the previous stage's
    # proved symmetry and the proved Boolean carry law.
    for i in range(32):
        p = Proof()
        a = p.lemma(recurrences[i],x,y)
        if i==0:
            p.trans(a,p.sym(p.lemma(recurrences[i],y,x)))
        else:
            at = f'bit-at-{i-1}'
            b = p.cong('carry-bit',p.refl(app(at,x)),p.refl(app(at,y)),
                       p.lemma(symmetries[i-1],x,y))
            c = p.lemma(7,app(at,x),app(at,y),app(f'carry-{i-1}',y,x))
            p.trans(a,b,c,p.sym(p.lemma(recurrences[i],y,x)))
        symmetries.append(save(equation(app(f'carry-{i}',x,y),app(f'carry-{i}',y,x)),p))

    # The sum's ith bit, derived from add32's constructor definition.
    for i in range(32):
        p = Proof()
        at = f'bit-at-{i}'
        body = app('word32', *[
            app('xor-bit',app('xor-bit',fields[j],app(f'bit-at-{j}',y)),
                app(f'carry-{j}',value,y)) for j in range(32)])
        a = p.cong(at,p.unfold('add32',value,y))
        b = p.unfold(at,body)
        lhs = p.trans(a,b)
        inner = p.cong('xor-bit',p.unfold(at,value),p.refl(app(at,y)))
        rhs = p.cong('xor-bit',inner,p.refl(app(f'carry-{i}',value,y)))
        p.trans(lhs,p.sym(rhs))
        eq = equation(app(at,app('add32',x,y)),
                      app('xor-bit',app('xor-bit',app(at,x),app(at,y)),app(f'carry-{i}',x,y)))
        projections.append(save(eq,p,induct=True))

    # Word commutativity, derived from its 32 components and proved eta.
    p, components = Proof(), []
    for i in range(32):
        at = f'bit-at-{i}'
        lhs = p.lemma(projections[i],x,y)
        inner = p.lemma(3,app(at,x),app(at,y))  # XOR commutativity
        carry = p.lemma(symmetries[i],x,y)
        middle = p.cong('xor-bit',inner,carry)
        rhs = p.lemma(projections[i],y,x)
        components.append(p.trans(lhs,middle,p.sym(rhs)))
    middle = p.cong('word32',*components)
    left,right = app('add32',x,y),app('add32',y,x)
    p.trans(p.sym(p.lemma(4,left)),middle,p.lemma(4,right))
    goal = [var('goal'),3,hash_of(t),params,equation(left,right)]
    proof = [var('proof'),3,hash_of(goal),lemmas,[var('derive'),p.steps]]
    return goal,proof


def identity_artifacts(t):
    """Prove add32(x, zero32) = x, reusing checked carry/sum projections."""
    from .word_literal import ZERO
    _, previous = artifacts(t)
    lemmas = previous[3]
    # Boolean carry with two zero inputs is zero for either constructor.
    lemmas.append(parse('''(lemma ((a Bit))
      (eq (carry-bit a (bit0) (bit0)) (bit0))
      (induct a (
        (bit0 () ((unfold carry-bit (bit0) (bit0) (bit0))
                  (unfold and-bit (bit0) (bit0)) (trans 0 1)))
        (bit1 () ((unfold carry-bit (bit1) (bit0) (bit0))
                  (unfold or-bit (bit0) (bit0)) (trans 0 1))))))'''))
    carry_zero = len(lemmas)-1
    x = var('x')
    params = [[x,var('Word32')]]
    zero_carries = []
    for i in range(32):
        p = Proof()
        recurrence = p.lemma(8+i,x,ZERO)
        if i:
            at = f'bit-at-{i-1}'
            reduced = p.cong('carry-bit',p.refl(app(at,x)),p.unfold(at,ZERO),
                             p.lemma(zero_carries[i-1],x))
            p.trans(recurrence,reduced,p.lemma(carry_zero,app(at,x)))
        zero_carries.append(len(lemmas))
        lemmas.append([var('lemma'),params,
                       equation(app(f'carry-{i}',x,ZERO),app('bit0')),
                       [var('derive'),p.steps]])
    p, components = Proof(), []
    for i in range(32):
        at = f'bit-at-{i}'
        projection = p.lemma(72+i,x,ZERO)
        inner = p.cong('xor-bit',p.refl(app(at,x)),p.unfold(at,ZERO))
        inner = p.trans(inner,p.lemma(1,app(at,x)))
        outer = p.cong('xor-bit',inner,p.lemma(zero_carries[i],x))
        components.append(p.trans(projection,outer,p.lemma(1,app(at,x))))
    middle = p.cong('word32',*components)
    left = app('add32',x,ZERO)
    p.trans(p.sym(p.lemma(4,left)),middle,p.lemma(4,x))
    goal = [var('goal'),3,hash_of(t),params,equation(left,x)]
    proof = [var('proof'),3,hash_of(goal),lemmas,[var('derive'),p.steps]]
    from .proof_slice import slice_proof
    return goal,slice_proof(proof)
