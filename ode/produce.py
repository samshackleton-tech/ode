"""The producer: specification -> W32 program -> W32 or AArch64 bytes.

Everything here is outside the reliance set: the checker (ode/check.py)
proves whatever bytes arrive, so any other producer -- smarter, faster,
or hostile -- changes no verdict. compile_spec inlines calls into a
straight-line W32 program; emit_w32 and emit_a64 turn it into bytes;
build writes a store a relying party can check.

The AArch64 emitter is naive and honest: every value lives in a scratch
word, each step loads its operands into w9/w10, computes into w11, and
stores. Register allocation and NEON are the obvious next producers.
"""
import os
import struct as _struct

from . import word
from .blake3 import blake3
from .canon import Bytes, Sym, assoc, canonical_bytes, hash_of


def put_definition(store_dir, defn):
    """File a definition in a store under its hash; return the hash."""
    h = hash_of(defn)
    with open(os.path.join(store_dir, h.hex() + ".sexp"), "wb") as f:
        f.write(canonical_bytes(defn))
    return h


_W_OPS = {"copy": 0, "add": 1, "xor": 2, "rotr": 3}


def _operand(e, index):
    if isinstance(e, int):
        return b"\x01" + _struct.pack("<I", e)
    return b"\x00" + _struct.pack("<I", index[e])


def emit_w32(defn) -> bytes:
    word.validate_w32(defn)
    inputs, steps, outputs = word.inputs_of(defn), word.steps_of(defn), word.outputs_of(defn)
    names = list(inputs) + [name for name, _ in steps]
    index = {n: i for i, n in enumerate(names)}
    out = bytearray()
    out += _struct.pack("<H", len(inputs))
    out += _struct.pack("<I", len(steps))
    out += _struct.pack("<H", len(outputs))
    for o in outputs:
        out += _struct.pack("<I", index[o])
    for _, e in steps:
        if isinstance(e, (int, Sym)):
            out.append(0)
            out += _operand(e, index)
        elif e[0] == "rotr":
            out.append(3)
            out += _operand(e[1], index)
            out.append(e[2])
        else:
            out.append(_W_OPS[e[0]])
            out += _operand(e[1], index)
            out += _operand(e[2], index)
    return bytes(out)





def _all_names(defn, acc):
    """Every name a specification and its callees mention."""
    acc.update(word.inputs_of(defn))
    for name, _ in word.steps_of(defn):
        acc.update(name if isinstance(name, list) else [name])
    for callee in word._defs_of(defn).values():
        _all_names(callee, acc)
    return acc


class _Fresh:
    """Mints step names that collide with nothing the spec names.

    The prefix is chosen so that no name in the spec or its callees
    starts with it (the game found a collision with an input named t0).
    """

    def __init__(self, spec_defn):
        names = _all_names(spec_defn, set())
        prefix = "t"
        while any(n.startswith(prefix) for n in names):
            prefix += "t"
        self.prefix, self.n = prefix, 0

    def __call__(self):
        name = Sym(f"{self.prefix}{self.n}")
        self.n += 1
        return name


def _flatten(e, steps, fresh):
    """Append single-operation steps for e; return its operand atom."""
    if isinstance(e, (int, Sym)):
        return e
    op = e[0]
    if op == "rotr":
        a = _flatten(e[1], steps, fresh)
        name = fresh()
        steps.append([name, [Sym("rotr"), a, e[2]]])
        return name
    a = _flatten(e[1], steps, fresh)
    b = _flatten(e[2], steps, fresh)
    name = fresh()
    steps.append([name, [Sym(op), a, b]])
    return name


def _rename(e, env):
    """Substitute names in an expression (callee body under its env)."""
    if isinstance(e, int):
        return e
    if isinstance(e, Sym):
        return env[e]
    if e[0] == "rotr":
        return [e[0], _rename(e[1], env), e[2]]
    return [e[0], _rename(e[1], env), _rename(e[2], env)]


def _inline(spec_defn, args, steps, fresh, defs):
    """Append the callee's steps, renamed; return its output atoms."""
    env = {}
    for name, a in zip(word.inputs_of(spec_defn), args):
        env[name] = a
    inner_defs = word._defs_of(spec_defn)
    for name, e in word.steps_of(spec_defn):
        if isinstance(name, list):
            outs = _inline(inner_defs[e[1]],
                           [_flatten(_rename(a, env), steps, fresh)
                            for a in e[2:]], steps, fresh, inner_defs)
            for n, o in zip(name, outs):
                env[n] = o
        else:
            new = fresh()
            steps.append([new, _flatten(_rename(e, env), steps, fresh)])
            env[name] = new
    return [env[o] for o in word.outputs_of(spec_defn)]


def compile_spec(spec_defn):
    word.validate_spec(spec_defn)
    steps, fresh = [], _Fresh(spec_defn)
    defs = word._defs_of(spec_defn)
    env = {n: n for n in word.inputs_of(spec_defn)}
    for name, e in word.steps_of(spec_defn):
        if isinstance(name, list):
            outs = _inline(defs[e[1]],
                           [_flatten(_rename(a, env), steps, fresh)
                            for a in e[2:]], steps, fresh, defs)
            for n, o in zip(name, outs):
                steps.append([n, o])
                env[n] = n
        else:
            steps.append([name, _flatten(_rename(e, env), steps, fresh)])
            env[name] = name
    return assoc("w32",
                 ("inputs", word.inputs_of(spec_defn)),
                 ("steps", steps), ("outputs", word.outputs_of(spec_defn)))


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
    word.validate_w32(machine_defn)
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


def build(spec_defn, store_dir, isa="w32"):
    """Write a store: the spec by hash, binary.bin, certificate.sexp."""
    os.makedirs(store_dir, exist_ok=True)
    program = compile_spec(spec_defn)
    if isa == "w32":
        binary = emit_w32(program)
        extra = ()
    elif isa == "a64":
        binary, scratch = emit_a64(program)
        extra = (("scratch", scratch),)
    else:
        raise ValueError(f"unknown isa {isa!r}")
    spec_hash = put_definition(store_dir, spec_defn)
    with open(os.path.join(store_dir, "binary.bin"), "wb") as f:
        f.write(binary)
    cert = assoc("certificate", ("cert", Sym("correctness")),
                 ("property", Sym(f"equals-spec-{isa}-v1")),
                 ("spec", spec_hash), ("binary-hash", Bytes(blake3(binary))),
                 *extra)
    cert_hash = put_definition(store_dir, cert)
    with open(os.path.join(store_dir, "certificate.sexp"), "wb") as f:
        f.write(canonical_bytes(cert))
    return {"spec": spec_hash.hex(), "certificate": cert_hash.hex(),
            "binary_hash": blake3(binary).hex(), "binary_len": len(binary)}
