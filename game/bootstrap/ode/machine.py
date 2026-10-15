"""The machine layer, toy scale (SPEC s3.3): the ODE8 ISA.

ODE8 is a straight-line stack machine over bytes. It has no branches at
all, computed or otherwise, so every program's instruction and address
trace depends only on its inputs' count -- the toy form of constant-time.
A program receives its inputs as values (capabilities, in the full
design, SPEC s6); it can touch nothing else: this VM has no memory, no
I/O, and no ambient authority.

Instructions (canonical-form arrays) and their binary encoding (s3.4):

    ["load", i]    push input i            0x01 i
    ["const", n]   push byte n             0x02 n
    ["add"]        push (a + b) mod 256    0x03
    ["xor"]        push a XOR b            0x04
    ["rotl", n]    push rotl(a, n)         0x05 n

A program is well-formed when it never underflows its stack and ends
with exactly one value on it: that value is its result.
"""

OPCODES = {"load": 0x01, "const": 0x02, "add": 0x03, "xor": 0x04, "rotl": 0x05}
DECODE = {v: k for k, v in OPCODES.items()}
WITH_OPERAND = {"load", "const", "rotl"}


def validate_program(code, n_inputs):
    if not isinstance(code, list) or not code:
        raise ValueError("program must be a non-empty array")
    depth = 0
    for ins in code:
        if not isinstance(ins, list) or not ins or ins[0] not in OPCODES:
            raise ValueError(f"bad instruction {ins!r}")
        op = ins[0]
        if op in WITH_OPERAND:
            if len(ins) != 2 or not isinstance(ins[1], int):
                raise ValueError(f"{op} takes one integer operand")
            if op == "load" and not (0 <= ins[1] < n_inputs):
                raise ValueError("load: input index out of range")
            if op == "const" and not (0 <= ins[1] < 256):
                raise ValueError("const: not a byte")
            if op == "rotl" and not (1 <= ins[1] < 8):
                raise ValueError("rotl: rotation out of range")
            if op == "rotl":
                if depth < 1:
                    raise ValueError("rotl: stack underflow")
            else:
                depth += 1
        else:
            if len(ins) != 1:
                raise ValueError(f"{op} takes no operand")
            if depth < 2:
                raise ValueError(f"{op}: stack underflow")
            depth -= 1
    if depth != 1:
        raise ValueError("program must leave exactly one value on the stack")
    return code


def validate_machine(defn):
    from .canon import field
    if not isinstance(defn, list) or not defn or defn[0] != "machine":
        raise ValueError("not a machine definition")
    if field(defn, "isa") != "ODE8":
        raise ValueError(f"unknown ISA {field(defn, 'isa')!r}")
    n = field(defn, "inputs")
    if not isinstance(n, int) or not (1 <= n <= 2):
        raise ValueError("machine inputs must be 1..2 (toy domain: the checker proves by exhaustion)")
    validate_program(field(defn, "code"), n)
    return defn


def machine_inputs(defn):
    from .canon import field
    return field(defn, "inputs")


def machine_code(defn):
    from .canon import field
    return field(defn, "code")


def emit(defn) -> bytes:
    """The deterministic emitter (s3.4): machine definition -> bytes."""
    validate_machine(defn)
    out = bytearray()
    for ins in machine_code(defn):
        out.append(OPCODES[ins[0]])
        if ins[0] in WITH_OPERAND:
            out.append(ins[1])
    return bytes(out)


def decode(data: bytes, n_inputs):
    """Bytes -> program. Rejects anything emit would never produce."""
    assert isinstance(data, bytes)
    code, i = [], 0
    while i < len(data):
        op = DECODE.get(data[i])
        if op is None:
            raise ValueError(f"unknown opcode 0x{data[i]:02x}")
        i += 1
        if op in WITH_OPERAND:
            if i >= len(data):
                raise ValueError("truncated instruction")
            code.append([op, data[i]])
            i += 1
        else:
            code.append([op])
    validate_program(code, n_inputs)
    # Round-trip: the only accepted bytes are exactly emit's output.
    from .canon import Sym, assoc
    if emit(assoc("machine", ("isa", Sym("ODE8")), ("inputs", n_inputs),
                  ("code", code))) != data:
        raise ValueError("bytes are not the emitter's output")
    return code


def run(code, inputs):
    stack = []
    for ins in code:
        op = ins[0]
        if op == "load":
            stack.append(inputs[ins[1]] & 0xFF)
        elif op == "const":
            stack.append(ins[1])
        elif op == "add":
            b, a = stack.pop(), stack.pop()
            stack.append((a + b) & 0xFF)
        elif op == "xor":
            b, a = stack.pop(), stack.pop()
            stack.append(a ^ b)
        elif op == "rotl":
            x, n = stack.pop(), ins[1]
            stack.append(((x << n) | (x >> (8 - n))) & 0xFF)
    assert len(stack) == 1
    return stack[0]


def run_binary(data: bytes, inputs):
    return run(decode(data, len(inputs)), list(inputs))
