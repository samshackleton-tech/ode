"""Exact Word32 constructor literals, least significant bit first."""
from .xor32_proof import app


def literal(n):
    """Encode a u32 as 32 Boolean constructor fields, least significant first."""
    assert type(n) is int and 0 <= n < 2**32, 'literal requires a u32'
    return app('word32', *[app('bit1' if n & (1 << i) else 'bit0') for i in range(32)])


def word_value(term):
    """Decode exactly 32 Boolean constructor fields, least significant first."""
    assert isinstance(term,list) and len(term)==33 and term[0]=='word32', 'Word32 requires exactly 32 fields'
    n = 0
    for i,bit in enumerate(term[1:]):
        assert bit in (app('bit0'),app('bit1')), 'requires Boolean constructor fields'
        if bit[0]=='bit1':
            n |= 1 << i
    return n
