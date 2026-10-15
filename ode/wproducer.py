"""The word producer (carrying no reliance): wspec -> W32 + certificate."""
import os

from . import word
from .blake3 import blake3
from .canon import Bytes, Sym, assoc, canonical_bytes, hash_of
from .producer import put_definition

PROPERTY = Sym("equals-wspec-v1")


import struct as _struct

_W_OPS = {"copy": 0, "add": 1, "xor": 2, "rotr": 3}


def _operand(e, index):
    if isinstance(e, int):
        return b"\x01" + _struct.pack("<I", e)
    return b"\x00" + _struct.pack("<I", index[e])


def emit_w32(defn) -> bytes:
    word.validate_wmachine(defn)
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

    The game's Mallory found the producer minting t0, t1, ... and
    colliding with a spec whose own input was named t1 (an invalid
    machine, caught by SSA, but a producer bug all the same). The
    prefix is chosen so that no name in the spec starts with it.
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


def compile_wspec(spec_defn):
    word.validate_wspec(spec_defn)
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
    return assoc("wmachine", ("isa", Sym("W32")),
                 ("inputs", word.inputs_of(spec_defn)),
                 ("steps", steps), ("outputs", word.outputs_of(spec_defn)))


def build(spec_defn, store_dir):
    os.makedirs(store_dir, exist_ok=True)
    machine_defn = compile_wspec(spec_defn)
    binary = emit_w32(machine_defn)
    spec_hash = put_definition(store_dir, spec_defn)
    machine_hash = put_definition(store_dir, machine_defn)
    with open(os.path.join(store_dir, "binary.bin"), "wb") as f:
        f.write(binary)
    cert = assoc("certificate", ("cert", Sym("correctness")),
                 ("property", PROPERTY),
                 ("spec", spec_hash),
                 ("binary-hash", Bytes(blake3(binary))),
                 ("binary", Bytes(binary)),
                 ("inputs", len(word.inputs_of(spec_defn))))
    cert_hash = put_definition(store_dir, cert)
    with open(os.path.join(store_dir, "certificate.sexp"), "wb") as f:
        f.write(canonical_bytes(cert))
    return {"spec": spec_hash.hex(), "machine": machine_hash.hex(),
            "certificate": cert_hash.hex(), "binary_hash": blake3(binary).hex(),
            "binary_len": len(binary)}
