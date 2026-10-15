"""The specification layer, and W32: word programs and their meaning.

A specification is an s-expression definition in SSA steps over u32
words:

    (spec (name blake3-g)
      (inputs (a b c d x y))
      (steps ((a1 (add (add a b) x)) (d1 (rotr (xor d a1) 16)) ...))
      (outputs (a2 b2 c2 d2)))

An atom is a name (an input or an earlier step) or an integer constant;
compound forms are (add e e), (xor e e), (rotr e n), all modulo 2**32.
A step may also call another specification it names by hash -- the
step ((o1 o2 ...) (call #hash e1 e2 ...)) binds the callee's outputs, in
order -- and the callee travels inside the caller, under (defs (#hash
definition) ...), so a definition is closed over everything it means.
Every computation is definite: it yields one value or is rejected.

A W32 program (w32 ...) has the same shape, with each step a single
operation on atoms: the portable, branch-free word machine the producer
emits, the checker proves, and run_program interprets. A W32 call step,
((o1 ...) (call #certificate a1 ...)), calls another *proved* program,
named by its certificate; the checker checks that certificate and
treats the call as the function its spec computes. decode_w32 reads the
binary form.
"""
from .canon import Bytes, Sym, field, hash_of

MASK = 0xFFFFFFFF
OPS = ("add", "xor", "rotr")


def _const(n):
    if not isinstance(n, int) or isinstance(n, bool) or not (0 <= n <= MASK):
        raise ValueError(f"bad u32 constant {n!r}")
    return n


def validate_expr(e, names, defs=None):
    if isinstance(e, int):
        _const(e)
        return
    if isinstance(e, Sym):
        if e not in names:
            raise ValueError(f"unknown name {e}")
        return
    if isinstance(e, list) and e and e[0] in OPS:
        if e[0] in ("add", "xor"):
            if len(e) != 3:
                raise ValueError(f"{e[0]} takes two operands")
            validate_expr(e[1], names)
            validate_expr(e[2], names)
            return
        if len(e) != 3 or not isinstance(e[2], int) or not (0 <= e[2] < 32):
            raise ValueError("rotr takes an expression and a count in 0..31")
        validate_expr(e[1], names)
        return
    raise ValueError(f"bad expression {e!r}")


def _validate_call(e, names, defs):
    """(call #hash arg ...) -> the callee; args are atoms or expressions."""
    if not (isinstance(e, list) and len(e) >= 2 and e[0] == "call"
            and isinstance(e[1], Bytes)):
        raise ValueError(f"bad call {e!r}")
    callee = (defs or {}).get(e[1])
    if callee is None:
        raise ValueError(f"call to unknown definition {e[1].hex()}")
    if len(e) - 2 != len(inputs_of(callee)):
        raise ValueError("call arity differs from callee's inputs")
    for arg in e[2:]:
        validate_expr(arg, names, defs)
    return callee


def _defs_of(defn):
    """(defs (#hash definition) ...) -> {hash: definition}, each checked."""
    raw = field(defn, "defs") or []
    defs = {}
    for item in raw:
        if not (isinstance(item, list) and len(item) == 2
                and isinstance(item[0], Bytes)):
            raise ValueError("defs entries are (#hash definition)")
        if hash_of(item[1]) != item[0]:
            raise ValueError(f"def named {item[0].hex()} hashes differently")
        validate_spec(item[1])
        defs[item[0]] = item[1]
    return defs


def _program(defn, kind):
    if not isinstance(defn, list) or not defn or defn[0] != kind:
        raise ValueError(f"not a {kind} definition")
    inputs = field(defn, "inputs")
    steps = field(defn, "steps")
    outputs = field(defn, "outputs")
    if not isinstance(inputs, list) or not all(isinstance(x, Sym) for x in inputs):
        raise ValueError("inputs must be a list of names")
    if len(set(inputs)) != len(inputs):
        raise ValueError("duplicate input name")
    if not isinstance(steps, list) or not isinstance(outputs, list) or not outputs:
        raise ValueError("program needs steps and outputs")
    names = set(inputs)
    defs = _defs_of(defn) if kind == "spec" else {}
    for step in steps:
        if not (isinstance(step, list) and len(step) == 2):
            raise ValueError(f"bad step {step!r}")
        targets = step[0] if isinstance(step[0], list) else [step[0]]
        if not all(isinstance(t, Sym) for t in targets):
            raise ValueError(f"bad step {step!r}")
        for t in targets:
            if t in names:
                raise ValueError(f"step redefines {t} (SSA: one assignment)")
        if isinstance(step[0], list) and kind == "w32":
            e = step[1]  # arity is checked against the callee's certificate
            if not (isinstance(e, list) and len(e) >= 2 and e[0] == "call"
                    and isinstance(e[1], Bytes) and len(e[1]) == 32
                    and all(isinstance(a, (int, Sym)) for a in e[2:])):
                raise ValueError(f"bad W32 call {e!r}")
            for a in e[2:]:
                validate_expr(a, names)
        elif isinstance(step[0], list):
            callee = _validate_call(step[1], names, defs)
            if len(targets) != len(outputs_of(callee)):
                raise ValueError("call binds a different number of outputs")
        else:
            validate_expr(step[1], names, defs)
        names.update(targets)
    for o in outputs:
        if not isinstance(o, Sym) or o not in names:
            raise ValueError(f"bad output {o!r}")
    return inputs, steps, outputs


def validate_spec(defn):
    _program(defn, "spec")
    if not isinstance(field(defn, "name"), Sym):
        raise ValueError("spec needs a symbol name")
    return defn


def validate_w32(defn):
    inputs, steps, outputs = _program(defn, "w32")
    for name, e in steps:
        if not isinstance(name, list):
            _validate_machine_expr(e)
    return defn


def _validate_machine_expr(e):
    # One operation on atoms: (add a b), (rotr a 7), or a bare atom.
    if isinstance(e, (int, Sym)):
        return
    if isinstance(e, list) and e and e[0] in OPS:
        if e[0] == "rotr":
            if not (len(e) == 3 and isinstance(e[1], (Sym, int))
                    and isinstance(e[2], int)):
                raise ValueError(f"machine step not a single operation: {e!r}")
        elif not (len(e) == 3 and all(isinstance(x, (Sym, int))
                                      for x in e[1:])):
            raise ValueError(f"machine step not a single operation: {e!r}")
        return
    raise ValueError(f"machine step not a single operation: {e!r}")


def inputs_of(defn):
    return field(defn, "inputs")


def steps_of(defn):
    return field(defn, "steps")


def outputs_of(defn):
    return field(defn, "outputs")


def eval_expr(e, env, defs=None):
    if isinstance(e, int):
        return e
    if isinstance(e, Sym):
        return env[e]
    op = e[0]
    if op == "call":
        callee = defs[e[1]]
        return run_program(callee, [eval_expr(a, env, defs) for a in e[2:]])
    if op == "add":
        return (eval_expr(e[1], env) + eval_expr(e[2], env)) & MASK
    if op == "xor":
        return eval_expr(e[1], env) ^ eval_expr(e[2], env)
    x, n = eval_expr(e[1], env), e[2] % 32
    return ((x >> n) | (x << ((32 - n) % 32))) & MASK if n else x


# --- The W32 binary form (written by produce.emit_w32) ------------------
# Header: inputs u16, steps u32, outputs u16, output name-indices u32 each.
# Step: opcode (0 copy, 1 add, 2 xor, 3 rotr); an operand is tag 0 + name
# index u32 (inputs first, then steps) or tag 1 + constant u32. rotr's
# second operand is a count u8. Deterministic: same definition, same bytes.
import struct as _struct

_W_DECODE = {0: "copy", 1: "add", 2: "xor", 3: "rotr", 4: "call"}


def decode_w32(data, input_names):
    """Bytes -> machine definition: exactly the program the bytes run."""
    assert isinstance(data, bytes)
    pos = 0

    def take(n):
        nonlocal pos
        if pos + n > len(data):
            raise ValueError("truncated W32 binary")
        b, pos = data[pos:pos + n], pos + n
        return b

    (n_inputs,) = _struct.unpack("<H", take(2))
    if n_inputs != len(input_names):
        raise ValueError("W32 binary input count mismatch")
    (n_steps,) = _struct.unpack("<I", take(4))
    (n_outputs,) = _struct.unpack("<H", take(2))
    out_idx = [_struct.unpack("<I", take(4))[0] for _ in range(n_outputs)]
    prefix = "s"  # step names must not collide with any input name
    while any(str(n).startswith(prefix) for n in input_names):
        prefix += "s"
    names = list(input_names) + [Sym(f"{prefix}{i}") for i in range(n_steps)]

    def operand():
        tag = take(1)[0]
        if tag == 1:
            return _struct.unpack("<I", take(4))[0]
        if tag == 0:
            (i,) = _struct.unpack("<I", take(4))
            if i >= len(names):
                raise ValueError("operand index out of range")
            return names[i]
        raise ValueError("bad operand tag")

    # n_steps counts names defined; a call defines one per output.
    steps, defined = [], 0
    while defined < n_steps:
        op = _W_DECODE.get(take(1)[0])
        if op is None:
            raise ValueError("bad W32 opcode")
        here = len(input_names) + defined
        if op == "call":
            h = Bytes(take(32))
            (n_args,) = _struct.unpack("<H", take(2))
            args = [operand() for _ in range(n_args)]
            (n_outs,) = _struct.unpack("<H", take(2))
            if n_outs == 0 or defined + n_outs > n_steps:
                raise ValueError("bad W32 call output count")
            steps.append([names[here:here + n_outs], [Sym("call"), h] + args])
            defined += n_outs
            continue
        if op == "copy":
            e = operand()
        elif op == "rotr":
            e = [Sym("rotr"), operand(), take(1)[0]]
        else:
            e = [Sym(op), operand(), operand()]
        steps.append([names[here], e])
        defined += 1
    if pos != len(data):
        raise ValueError("trailing bytes in W32 binary")
    if any(i >= len(names) for i in out_idx):
        raise ValueError("output index out of range")
    from .canon import assoc
    defn = assoc("w32", ("inputs", list(input_names)),
                 ("steps", steps),
                 ("outputs", [names[i] for i in out_idx]))
    validate_w32(defn)
    return defn


def run_program(defn, values, call=None):
    """Concrete execution of a spec or a W32 program. A W32 program's
    call steps run through call(certificate_hash, args) -> outputs."""
    inputs, steps, outputs = _program(
        defn, "spec" if defn[0] == "spec" else "w32")
    if len(values) != len(inputs):
        raise ValueError("wrong number of inputs")
    defs = _defs_of(defn) if defn[0] == "spec" else {}
    env = {name: _const(v) for name, v in zip(inputs, values)}
    for name, e in steps:
        if isinstance(name, list) and defn[0] == "w32":
            outs = call(e[1], [eval_expr(a, env) for a in e[2:]])
            for n, v in zip(name, outs):
                env[n] = v
        elif isinstance(name, list):
            for n, v in zip(name, eval_expr(e, env, defs)):
                env[n] = v
        else:
            env[name] = eval_expr(e, env, defs)
    return [env[o] for o in outputs]
