"""The word producer (untrusted): wspec -> W32 machine + certificate."""
import os

from . import word
from .blake3 import blake3
from .canon import Bytes, Sym, assoc, canonical_bytes, hash_of
from .producer import put_definition

PROPERTY = Sym("equals-wspec-v1")


def _flatten(e, steps, counter):
    """Append single-operation steps for e; return its operand atom."""
    if isinstance(e, (int, Sym)):
        return e
    op = e[0]
    if op == "rotr":
        a = _flatten(e[1], steps, counter)
        name = Sym(f"t{counter[0]}")
        counter[0] += 1
        steps.append([name, [Sym("rotr"), a, e[2]]])
        return name
    a = _flatten(e[1], steps, counter)
    b = _flatten(e[2], steps, counter)
    name = Sym(f"t{counter[0]}")
    counter[0] += 1
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


def _inline(spec_defn, args, steps, counter, defs):
    """Append the callee's steps, renamed; return its output atoms."""
    env = {}
    for name, a in zip(word.inputs_of(spec_defn), args):
        env[name] = a
    inner_defs = word._defs_of(spec_defn)
    for name, e in word.steps_of(spec_defn):
        if isinstance(name, list):
            outs = _inline(inner_defs[e[1]],
                           [_flatten(_rename(a, env), steps, counter)
                            for a in e[2:]], steps, counter, inner_defs)
            for n, o in zip(name, outs):
                env[n] = o
        else:
            fresh = Sym(f"t{counter[0]}")
            counter[0] += 1
            steps.append([fresh, _flatten(_rename(e, env), steps, counter)])
            env[name] = fresh
    return [env[o] for o in word.outputs_of(spec_defn)]


def compile_wspec(spec_defn):
    word.validate_wspec(spec_defn)
    steps, counter = [], [0]
    defs = word._defs_of(spec_defn)
    env = {n: n for n in word.inputs_of(spec_defn)}
    for name, e in word.steps_of(spec_defn):
        if isinstance(name, list):
            outs = _inline(defs[e[1]],
                           [_flatten(_rename(a, env), steps, counter)
                            for a in e[2:]], steps, counter, defs)
            for n, o in zip(name, outs):
                steps.append([n, o])
                env[n] = n
        else:
            steps.append([name, _flatten(_rename(e, env), steps, counter)])
            env[name] = name
    return assoc("wmachine", ("isa", Sym("W32")),
                 ("inputs", word.inputs_of(spec_defn)),
                 ("steps", steps), ("outputs", word.outputs_of(spec_defn)))


def build(spec_defn, store_dir):
    os.makedirs(store_dir, exist_ok=True)
    machine_defn = compile_wspec(spec_defn)
    binary = word.emit_w32(machine_defn)
    spec_hash = put_definition(store_dir, spec_defn)
    machine_hash = put_definition(store_dir, machine_defn)
    with open(os.path.join(store_dir, "binary.bin"), "wb") as f:
        f.write(binary)
    cert = assoc("certificate", ("cert", Sym("correctness")),
                 ("property", PROPERTY),
                 ("spec", spec_hash), ("machine", machine_hash),
                 ("binary-hash", Bytes(blake3(binary))),
                 ("binary", Bytes(binary)),
                 ("inputs", len(word.inputs_of(spec_defn))))
    cert_hash = put_definition(store_dir, cert)
    with open(os.path.join(store_dir, "certificate.sexp"), "wb") as f:
        f.write(canonical_bytes(cert))
    return {"spec": spec_hash.hex(), "machine": machine_hash.hex(),
            "certificate": cert_hash.hex(), "binary_hash": blake3(binary).hex(),
            "binary_len": len(binary)}
