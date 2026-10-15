"""Interpret one Boolean full-adder column as natural-number addition.

The bit and carry definitions are exactly those used by Word32 addition.
Only those definitions are carried into this small theory. Natural add is
structural recursion, and bit-value maps bit0/bit1 to zero/one.
"""
from .canon import parse
from .add32_proof import theory as word_theory
from .boolean_proof import prove
from .equational_proof import app,var


def theory(bit_theory,nat_theory):
    words=word_theory(bit_theory)
    bit=next(d for d in words[2] if d[0]=='Bit')
    names={'not-bit','xor-bit','and-bit','or-bit','carry-bit'}
    definitions=[d for d in words[4] if d[0] in names]
    definitions.append(next(d for d in nat_theory[4] if d[0]=='add'))
    definitions.append(parse('''(bit-value ((a Bit)) Nat
      ((bit0 () (zero)) (bit1 () (succ (zero)))))'''))
    return [var('theory'),3,[bit],[],definitions]


def artifacts(t):
    a,b,c=map(var,('a','b','c'))
    value=lambda bit:app('bit-value',bit)
    sum_bit=app('xor-bit',app('xor-bit',a,b),c)
    carry_bit=app('carry-bit',a,b,c)
    left=app('add',value(sum_bit),app('add',value(carry_bit),value(carry_bit)))
    right=app('add',value(a),app('add',value(b),value(c)))
    return prove(t,[a,b,c],left,right)
