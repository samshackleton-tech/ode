"""The specification layer, toy scale (SPEC s3.1).

A specification is a definite function of byte inputs given by one
expression. Expressions (canonical-form arrays):

    ["const", n]        byte constant, 0 <= n < 256
    ["var", i]          the i-th input
    ["add", a, b]       (a + b) mod 256
    ["xor", a, b]       a XOR b
    ["rotl", a, n]      rotate a left by n bits, 1 <= n < 8

Every expression evaluates to exactly one byte or is rejected as
ill-formed: definite, pure, strict. This evaluator is the reference
semantics of the layer; certificates are checked against it.
"""

OPS_NULLARY = ()


def _byte(n, what):
    if not isinstance(n, int) or isinstance(n, bool) or not (0 <= n < 256):
        raise ValueError(f"{what}: expected a byte, got {n!r}")
    return n


def validate_expr(e, n_inputs):
    if not isinstance(e, list) or not e or not isinstance(e[0], str):
        raise ValueError(f"bad expression: {e!r}")
    op = e[0]
    if op == "const":
        if len(e) != 2:
            raise ValueError("const takes one operand")
        _byte(e[1], "const")
    elif op == "var":
        if len(e) != 2 or not isinstance(e[1], int) or not (0 <= e[1] < n_inputs):
            raise ValueError(f"var: index out of range in {e!r}")
    elif op in ("add", "xor"):
        if len(e) != 3:
            raise ValueError(f"{op} takes two operands")
        validate_expr(e[1], n_inputs)
        validate_expr(e[2], n_inputs)
    elif op == "rotl":
        if len(e) != 3 or not isinstance(e[2], int) or not (1 <= e[2] < 8):
            raise ValueError(f"rotl: bad rotation in {e!r}")
        validate_expr(e[1], n_inputs)
    else:
        raise ValueError(f"unknown operator {op!r}")


def validate_spec(defn):
    from .canon import Sym, field
    if not isinstance(defn, list) or not defn or defn[0] != "spec":
        raise ValueError("not a spec definition")
    name = field(defn, "name")
    if not isinstance(name, Sym):
        raise ValueError("spec needs a symbol name")
    n = field(defn, "inputs")
    if not isinstance(n, int) or not (1 <= n <= 2):
        raise ValueError("spec inputs must be 1..2 (toy domain: the checker proves by exhaustion)")
    validate_expr(field(defn, "body"), n)
    return defn


def spec_inputs(defn):
    from .canon import field
    return field(defn, "inputs")


def spec_body(defn):
    from .canon import field
    return field(defn, "body")


def eval_expr(e, inputs):
    op = e[0]
    if op == "const":
        return e[1]
    if op == "var":
        return inputs[e[1]]
    if op == "add":
        return (eval_expr(e[1], inputs) + eval_expr(e[2], inputs)) & 0xFF
    if op == "xor":
        return eval_expr(e[1], inputs) ^ eval_expr(e[2], inputs)
    if op == "rotl":
        x, n = eval_expr(e[1], inputs), e[2]
        return ((x << n) | (x >> (8 - n))) & 0xFF
    raise AssertionError(op)


def eval_spec(defn, inputs):
    validate_spec(defn)
    if len(inputs) != spec_inputs(defn):
        raise ValueError("wrong number of inputs")
    for x in inputs:
        _byte(x, "input")
    return eval_expr(spec_body(defn), list(inputs))
