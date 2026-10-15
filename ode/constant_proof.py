"""Export concrete Dag arithmetic results as constructor-evaluation proofs.

The old normalizer proposes a Word32 value. ground_proof emits a
separate derivation from the owner's definitions; the kernel checks it.
Supports closed Word32 expressions: literal words, add32, xor32, ror-N.
The supplied theory must define each operation used by the expression.
"""
from .ground_proof import prove
from .rotate32_proof import rotation_count
from .xor32_proof import app


def literal(n):
    """Encode a u32 as 32 Boolean constructor fields, least significant first."""
    assert type(n) is int and 0 <= n < 2**32, 'literal requires a u32'
    return app('word32', *[app('bit1' if n & (1 << i) else 'bit0') for i in range(32)])


def export_normalizer(t, expression):
    from .check import Dag
    dag = Dag()

    def input_node(term):
        assert isinstance(term,list) and term, 'requires a closed Word32 expression'
        if term[0] == 'word32':
            assert len(term)==33, 'Word32 requires exactly 32 fields'
            n = 0
            for i,bit in enumerate(term[1:]):
                assert bit in (app('bit0'),app('bit1')), 'requires Boolean constructor fields'
                if bit[0]=='bit1':
                    n |= 1 << i
            return dag.const(n)
        n = rotation_count(term)
        if n is not None:
            return dag.rotr(input_node(term[1]),n)
        if term[0] in ('add32','xor32'):
            assert len(term)==3, 'binary arithmetic requires two operands'
            operation = dag.add if term[0]=='add32' else dag.xor
            return operation(input_node(term[1]),input_node(term[2]))
        raise ValueError('unsupported constant-folding operation')

    node = dag.nodes[input_node(expression)]
    assert node[0]=='const', 'normalizer must return a constant for a closed expression'
    return prove(t,expression,literal(node[1]))
