"""Boolean carry relations used to compare two groupings of three sums.

Two incoming carry bits encode their count without choosing an order:
AND is the lower sorted bit and OR the upper sorted bit. The outgoing
carry pair and sum bit can be computed from that encoding in either
addition grouping. Every identity is proved by explicit Boolean cases.
"""
from .boolean_proof import prove
from .xor32_proof import app, var


def xor(a, b):
    return app('xor-bit', a, b)


def outgoing(a, b, c, p, q):
    """Carries from (a+b+p), then adding c+q to its sum bit."""
    return (app('carry-bit', a, b, p),
            app('carry-bit', xor(xor(a,b),p), c, q))


def canonical_inputs(p, q):
    return app('and-bit', p, q), app('or-bit', p, q)


def equations():
    a,b,c,p,q = map(var, ('a','b','c','p','q'))
    low,high = canonical_inputs(p,q)
    variables = [a,b,c,p,q]
    for grouping, bits in (('left',(a,b,c)), ('right',(b,c,a))):
        for operation in ('and-bit','or-bit'):
            left = app(operation,*outgoing(*bits,p,q))
            right = app(operation,*outgoing(a,b,c,low,high))
            yield f'carry-{grouping}-{operation}', variables, left, right
        x,y,z = bits
        left = xor(xor(xor(xor(x,y),p),z),q)
        right = xor(xor(xor(a,b),c),xor(low,high))
        yield f'carry-{grouping}-sum', variables, left, right


def artifacts(theory):
    for name, variables, left, right in equations():
        goal, proof = prove(theory,variables,left,right)
        yield name,goal,proof
