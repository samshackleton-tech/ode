"""Exact Word32 constructor literals, least significant bit first."""
from .canon import Sym


def literal(n):
    """Encode a u32 as 32 Boolean constructor fields, least significant first."""
    assert type(n) is int and 0 <= n < 2**32, 'literal requires a u32'
    return [Sym('word32'), *[[Sym('bit1' if n & (1 << i) else 'bit0')] for i in range(32)]]


def word_value(term):
    """Decode exactly 32 Boolean constructor fields, least significant first."""
    if not (isinstance(term,list) and len(term)==33 and term[0]=='word32'):
        raise ValueError('Word32 requires exactly 32 fields')
    n = 0
    for i,bit in enumerate(term[1:]):
        if bit not in ([Sym('bit0')],[Sym('bit1')]):
            raise ValueError('requires Boolean constructor fields')
        if bit[0]=='bit1':
            n |= 1 << i
    return n


ZERO = literal(0)
