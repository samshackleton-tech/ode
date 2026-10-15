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


def compile_wspec(spec_defn):
    word.validate_wspec(spec_defn)
    steps, counter = [], [0]
    for name, e in word.steps_of(spec_defn):
        operand = _flatten(e, steps, counter)
        steps.append([name, operand])
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
