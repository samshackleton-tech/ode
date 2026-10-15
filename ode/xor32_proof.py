"""Produce proofs of 32-bit XOR laws from Boolean constructor semantics.

No kernel import. Word32 has one constructor with exactly 32 Bit fields.
Its XOR operates on those fields. The producer proves Boolean laws,
projection laws and word extensionality, then lifts the Boolean laws to
words. The kernel checks every step, including all supporting lemmas.
"""
from .canon import hash_of, parse
from .equational_proof import Proof, app, var, equation, operation_term, lemma_rules
from .word_literal import ZERO


def bit_lemmas():
    """Indices: involution, right-zero, right-one, comm, complement, assoc, cancel."""
    def induction(params, eq, zero, one):
        return parse(f'''(lemma {params} {eq}
          (induct a ((bit0 () {zero}) (bit1 () {one}))))''')

    return [
        induction('((a Bit))', '(eq (not-bit (not-bit a)) a)',
                  '''((unfold not-bit (bit0)) (cong not-bit 0)
                      (unfold not-bit (bit1)) (trans 1 2))''',
                  '''((unfold not-bit (bit1)) (cong not-bit 0)
                      (unfold not-bit (bit0)) (trans 1 2))'''),
        induction('((a Bit))', '(eq (xor-bit a (bit0)) a)',
                  '((unfold xor-bit (bit0) (bit0)))',
                  '''((unfold xor-bit (bit1) (bit0))
                      (unfold not-bit (bit0)) (trans 0 1))'''),
        induction('((a Bit))', '(eq (xor-bit a (bit1)) (not-bit a))',
                  '''((unfold xor-bit (bit0) (bit1)) (unfold not-bit (bit0))
                      (sym 1) (trans 0 2))''',
                  '((unfold xor-bit (bit1) (bit1)))'),
        induction('((a Bit) (b Bit))', '(eq (xor-bit a b) (xor-bit b a))',
                  '((unfold xor-bit (bit0) b) (lemma 1 b) (sym 1) (trans 0 2))',
                  '((unfold xor-bit (bit1) b) (lemma 2 b) (sym 1) (trans 0 2))'),
        induction('((a Bit) (b Bit))',
                  '(eq (xor-bit (not-bit a) b) (not-bit (xor-bit a b)))',
                  '''((unfold not-bit (bit0)) (refl b) (cong xor-bit 0 1)
                      (unfold xor-bit (bit1) b) (trans 2 3)
                      (unfold xor-bit (bit0) b) (cong not-bit 5)
                      (sym 6) (trans 4 7))''',
                  '''((unfold not-bit (bit1)) (refl b) (cong xor-bit 0 1)
                      (unfold xor-bit (bit0) b) (trans 2 3)
                      (unfold xor-bit (bit1) b) (cong not-bit 5)
                      (lemma 0 b) (trans 6 7) (sym 8) (trans 4 9))'''),
        induction('((a Bit) (b Bit) (c Bit))',
                  '(eq (xor-bit (xor-bit a b) c) (xor-bit a (xor-bit b c)))',
                  '''((unfold xor-bit (bit0) b) (refl c) (cong xor-bit 0 1)
                      (unfold xor-bit (bit0) (xor-bit b c)) (sym 3) (trans 2 4))''',
                  '''((unfold xor-bit (bit1) b) (refl c) (cong xor-bit 0 1)
                      (lemma 4 b c) (trans 2 3)
                      (unfold xor-bit (bit1) (xor-bit b c)) (sym 5) (trans 4 6))'''),
        induction('((a Bit))', '(eq (xor-bit a a) (bit0))',
                  '((unfold xor-bit (bit0) (bit0)))',
                  '((unfold xor-bit (bit1) (bit1)) (unfold not-bit (bit1)) (trans 0 1))'),
    ]


def theory(bit_theory):
    """Word32 over the Bit definitions in the owner's bit-string theory.
    The generated flat theory carries those same definitions explicitly.
    """
    bit = next(d for d in bit_theory[2] if isinstance(d, list) and d[0] == 'Bit')
    word = [var('Word32'), [[var('word32'), [var('Bit')] * 32]]]
    names = [var(f'b{i}') for i in range(32)]
    definitions = {d[0]: d for d in bit_theory[4]}
    defs = [definitions[var('not-bit')], definitions[var('xor-bit')]]
    for i in range(32):
        defs.append([var(f'bit-at-{i}'), [[var('x'), var('Word32')]], var('Bit'),
                     [[var('word32'), names, names[i]]]])
    body = app('word32', *[app('xor-bit', names[i], app(f'bit-at-{i}', var('y')))
                           for i in range(32)])
    defs.append([var('xor32'), parse('((x Word32) (y Word32))'), var('Word32'),
                 [[var('word32'), names, body]]])
    return [var('theory'), 3, [bit, word], [], defs]


XOR_LAWS = {'right': 40, 'comm': 41, 'assoc': 42, 'cancel': 43,
            'left': 44, 'pair': 45, 'exchange': 46}


def word_lemmas():
    """Prove Word32's eta and XOR projection equations, using definitions."""
    x, y = var('x'), var('y')
    names = [var(f'b{i}') for i in range(32)]
    value = app('word32', *names)
    p = Proof()
    refs = [p.unfold(f'bit-at-{i}', value) for i in range(32)]
    p.cong('word32', *refs)
    eta = [var('lemma'), [[x, var('Word32')]],
           equation(app('word32', *[app(f'bit-at-{i}', x) for i in range(32)]), x),
           [var('induct'), x, [[var('word32'), names, p.steps]]]]
    result = [eta]  # index 7 in the combined library
    for i in range(32):
        p = Proof()
        projection = f'bit-at-{i}'
        body = app('word32', *[app('xor-bit', names[j], app(f'bit-at-{j}', y))
                               for j in range(32)])
        a = p.unfold('xor32', value, y)
        b = p.cong(projection, a)
        c = p.unfold(projection, body)
        lhs = p.trans(b, c)
        d = p.unfold(projection, value)
        rhs = p.cong('xor-bit', d, p.refl(app(projection, y)))
        p.trans(lhs, p.sym(rhs))
        eq = equation(app(projection, app('xor32', x, y)),
                      app('xor-bit', app(projection, x), app(projection, y)))
        result.append([var('lemma'), [[x, var('Word32')], [y, var('Word32')]], eq,
                       [var('induct'), x, [[var('word32'), names, p.steps]]]])
    return result


def project(p, i, term):
    """Prove bit-at-i(term) equal to a Boolean expression."""
    at = f'bit-at-{i}'
    if term == ZERO:
        return app('bit0'), p.unfold(at, ZERO)
    if isinstance(term, list) and term[0] == 'xor32':
        a, b = term[1:]
        x, pa = project(p, i, a)
        y, pb = project(p, i, b)
        outer = p.lemma(8 + i, a, b)
        inner = p.cong('xor-bit', pa, pb)
        return app('xor-bit', x, y), p.trans(outer, inner)
    return app(at, term), p.refl(app(at, term))


def lift(left, right, params, bit_rule):
    """Lift a pointwise Boolean identity to Word32 using proved eta.

    bit_rule(p,i) emits the equality of the projected normal forms.
    No extensionality rule is built into the kernel: eta is proved above.
    """
    p, components = Proof(), []
    for i in range(32):
        _, a = project(p, i, left)
        _, b = project(p, i, right)
        components.append(p.trans(a, bit_rule(p, i), p.sym(b)))
    middle = p.cong('word32', *components)
    p.trans(p.sym(p.lemma(7, left)), middle, p.lemma(7, right))
    return [var('lemma'), [[var(n), var('Word32')] for n in params],
            equation(left, right), [var('derive'), p.steps]]


def law_library():
    x, y, z = map(var, ('x', 'y', 'z'))
    xor = lambda a, b: app('xor32', a, b)
    proj = lambda i, a: app(f'bit-at-{i}', a)
    lemmas = bit_lemmas() + word_lemmas()  # 0..39
    lemmas += [
        lift(xor(x, ZERO), x, ('x',), lambda p, i: p.lemma(1, proj(i, x))), # 40
        lift(xor(x, y), xor(y, x), ('x','y'),
             lambda p, i: p.lemma(3, proj(i, x), proj(i, y))),              # 41
        lift(xor(xor(x,y), z), xor(x, xor(y,z)), ('x','y','z'),
             lambda p, i: p.lemma(5, proj(i,x), proj(i,y), proj(i,z))),     # 42
        lift(xor(x,x), ZERO, ('x',), lambda p, i: p.lemma(6, proj(i,x))),   # 43
    ]
    # Left identity, derived from commutativity and right identity.
    p = Proof()
    p.trans(p.lemma(41, ZERO, x), p.lemma(40, x))
    lemmas.append([var('lemma'), [[x,var('Word32')]], equation(xor(ZERO,x), x),
                   [var('derive'), p.steps]])                            # 44
    # Double cancellation: x XOR (x XOR y) = y.
    p = Proof()
    a = p.sym(p.lemma(42, x, x, y))
    b = p.cong('xor32', p.lemma(43, x), p.refl(y))
    p.trans(a, b, p.lemma(44, y))
    lemmas.append([var('lemma'), [[x,var('Word32')],[y,var('Word32')]],
                   equation(xor(x,xor(x,y)), y), [var('derive'),p.steps]]) # 45
    # Exchange: x XOR (y XOR z) = y XOR (x XOR z).
    p = Proof()
    a = p.sym(p.lemma(42, x, y, z))
    b = p.cong('xor32', p.lemma(41, x, y), p.refl(z))
    p.trans(a, b, p.lemma(42, y, x, z))
    lemmas.append([var('lemma'), [[v,var('Word32')] for v in (x,y,z)],
                   equation(xor(x,xor(y,z)), xor(y,xor(x,z))),
                   [var('derive'), p.steps]])                            # 46
    return lemmas


def xor_term(atoms):
    return operation_term('xor32', ZERO, atoms)


def prove(t, parameters, left, right):
    """Emit a proposed equality and proof for XOR expressions on Word32.

    Flattening, reordering, zero elimination, duplicate cancellation,
    and constructor-checked constant folding are performed. The relying
    party must supply the actual theory and goal to verify.
    """
    from .mixed_constant_proof import NormalizerWithConstants
    from .proof_library import Library
    library = Library(hash_of(t))
    for lemma in law_library():
        library.add(lemma)
    p = NormalizerWithConstants(t,library,'xor32',lemma_rules(XOR_LAWS))
    a, lhs = p.normalize(left)
    b, rhs = p.normalize(right)
    if a != b:
        raise ValueError('the XOR expressions have different parity-normal forms')
    p.trans(lhs, p.sym(rhs))
    goal = [var('goal'), 3, hash_of(t), parameters, equation(left,right)]
    proof = [var('proof'), 3, hash_of(goal), library.lemmas, [var('derive'),p.steps]]
    return goal, proof


def artifacts(t):
    x, y = var('x'), var('y')
    return prove(t, [[x,var('Word32')],[y,var('Word32')]],
                 app('xor32',x,app('xor32',y,x)), y)
