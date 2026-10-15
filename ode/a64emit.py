"""The AArch64 producer (carrying no reliance): W32 machine -> A64 bytes.

Naive and honest: every W32 value lives in a scratch word; each step
loads its operands into w9/w10, computes into w11, and stores. The
checker (ode/a64.py) proves whatever bytes arrive, so a faster
producer -- register allocation, NEON -- can replace this one without
changing what Bob relies on.
"""
from . import word
from .canon import Sym

RET = 0xD65F03C0


def _ldr(rt, base, idx):
    assert idx < 4096
    return 0xB9400000 | (idx << 10) | (base << 5) | rt


def _str(rt, base, idx):
    assert idx < 4096
    return 0xB9000000 | (idx << 10) | (base << 5) | rt


def _load(r, atom, where):
    if isinstance(atom, int):
        out = [0x52800000 | ((atom & 0xFFFF) << 5) | r]
        if atom >> 16:
            out.append(0x72800000 | (1 << 21) | ((atom >> 16) << 5) | r)
        return out
    base, idx = where[atom]
    return [_ldr(r, base, idx)]


def emit_a64(machine_defn):
    """Returns (bytes, scratch_words)."""
    word.validate_wmachine(machine_defn)
    where = {n: (0, i) for i, n in enumerate(word.inputs_of(machine_defn))}
    code, slot = [], 0
    for name, e in word.steps_of(machine_defn):
        if isinstance(e, (int, Sym)):
            code += _load(11, e, where)
        elif e[0] == "rotr":
            code += _load(9, e[1], where)
            code.append(0x13800000 | (9 << 16) | (e[2] << 10) | (9 << 5) | 11)
        else:
            code += _load(9, e[1], where) + _load(10, e[2], where)
            op = 0x0B000000 if e[0] == "add" else 0x4A000000
            code.append(op | (10 << 16) | (9 << 5) | 11)
        code.append(_str(11, 2, slot))
        where[name] = (2, slot)
        slot += 1
    for k, o in enumerate(word.outputs_of(machine_defn)):
        code += _load(9, o, where)
        code.append(_str(9, 1, k))
    code.append(RET)
    return b"".join(w.to_bytes(4, "little") for w in code), slot
