"""An author-supplied proof of x + (x XOR all-ones) = all-ones.

Each bit is complementary, so every incoming carry is zero and every
sum bit is one. The producer reuses explicit carry recurrences, sum/XOR
projections, Boolean case proofs, and Word32 reconstruction. No kernel
import and no appeal to a normalizer's verdict.
"""
from .canon import canonical_bytes,hash_of
from .add32_proof import artifacts as addition_laws
from .boolean_proof import prove as prove_boolean
from .proof_library import Library
from .proof_slice import slice_proof
from .word_literal import literal
from .xor32_proof import word_lemmas
from .equational_proof import Proof, app, equation, var

ONES=literal(0xffffffff)


def artifacts(t):
    library=Library(hash_of(t))
    library.include(*addition_laws(t))
    word_rules=[library.add(lemma) for lemma in word_lemmas()]
    a,x,y=map(var,('a','x','y'))
    bit0,bit1=app('bit0'),app('bit1')
    bit_complement=app('xor-bit',a,bit1)
    carry_zero=library.include(*prove_boolean(t,[a],app('carry-bit',a,bit_complement,bit0),bit0))
    sum_one=library.include(*prove_boolean(t,[a],app('xor-bit',a,bit_complement),bit1))

    def find(params,eq):
        # Identify a supporting theorem by its complete statement, rather
        # than by a producer-specific numeric position in the library.
        return library.index[canonical_bytes([params,eq])]

    bit_identity=find([[a,var('Bit')]],equation(app('xor-bit',a,bit0),a))
    params=[[x,var('Word32')]]
    xy_params=params+[[y,var('Word32')]]
    complement=app('xor32',x,ONES)
    carries=[]

    def complement_projection(p,i):
        at=f'bit-at-{i}'
        first=p.lemma(word_rules[i+1],x,ONES)
        second=p.cong('xor-bit',p.refl(app(at,x)),p.unfold(at,ONES))
        return p.trans(first,second)

    for i in range(32):
        p=Proof()
        rhs=bit0 if i==0 else app('carry-bit',app(f'bit-at-{i-1}',x),
            app(f'bit-at-{i-1}',y),app(f'carry-{i-1}',x,y))
        recurrence=find(xy_params,equation(app(f'carry-{i}',x,y),rhs))
        first=p.lemma(recurrence,x,complement)
        if i:
            at=f'bit-at-{i-1}'
            middle=p.cong('carry-bit',p.refl(app(at,x)),complement_projection(p,i-1),
                          p.lemma(carries[i-1],x))
            p.trans(first,middle,p.lemma(carry_zero,app(at,x)))
        carries.append(library.add([var('lemma'),params,
            equation(app(f'carry-{i}',x,complement),bit0),[var('derive'),p.steps]]))

    p,components=Proof(),[]
    total=app('add32',x,complement)
    for i in range(32):
        at=f'bit-at-{i}';bit=app(at,x)
        rhs=app('xor-bit',app('xor-bit',app(at,x),app(at,y)),app(f'carry-{i}',x,y))
        projection=find(xy_params,equation(app(at,app('add32',x,y)),rhs))
        first=p.lemma(projection,x,complement)
        inner=p.cong('xor-bit',p.refl(bit),complement_projection(p,i))
        middle=p.cong('xor-bit',inner,p.lemma(carries[i],x))
        pair=app('xor-bit',bit,app('xor-bit',bit,bit1))
        components.append(p.trans(first,middle,p.lemma(bit_identity,pair),p.lemma(sum_one,bit)))
    middle=p.cong('word32',*components)
    p.trans(p.sym(p.lemma(word_rules[0],total)),middle)
    goal=[var('goal'),3,hash_of(t),params,equation(total,ONES)]
    proof=[var('proof'),3,hash_of(goal),library.lemmas,[var('derive'),p.steps]]
    return goal,slice_proof(proof)
