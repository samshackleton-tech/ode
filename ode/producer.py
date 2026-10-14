"""Producers (SPEC s4.3): untrusted, interchangeable, believed per-output.

This module holds the compiler from the specification layer to the ODE8
machine layer, and the build that assembles a store: definitions named
by hash, the emitted binary, and a certificate claiming the binary's
program meets the specification. Nothing here is trusted; the checker
(ode/checker.py) re-derives every claim from the hashes alone.
"""
import itertools
import os

from . import machine, spec as spec_mod
from .canon import canonical_bytes, hash_of
from .blake3 import blake3_hex

PROPERTY = "equals-spec-v1"


def compile_expr(e, code):
    op = e[0]
    if op == "const":
        code.append(["const", e[1]])
    elif op == "var":
        code.append(["load", e[1]])
    elif op in ("add", "xor"):
        compile_expr(e[1], code)
        compile_expr(e[2], code)
        code.append([op])
    elif op == "rotl":
        compile_expr(e[1], code)
        code.append(["rotl", e[2]])
    else:
        raise AssertionError(op)
    return code


def compile_spec(spec_defn):
    spec_mod.validate_spec(spec_defn)
    code = compile_expr(spec_defn["body"], [])
    return {"kind": "machine", "isa": "ODE8",
            "inputs": spec_defn["inputs"], "code": code}


def put_definition(store_dir, defn):
    h = hash_of(defn)
    path = os.path.join(store_dir, h + ".json")
    with open(path, "wb") as f:
        f.write(canonical_bytes(defn))
    return h


def build(spec_defn, store_dir):
    """Produce: store/{spec,machine by hash}, binary.bin, certificate.json."""
    os.makedirs(store_dir, exist_ok=True)
    machine_defn = compile_spec(spec_defn)
    binary = machine.emit(machine_defn)
    spec_hash = put_definition(store_dir, spec_defn)
    machine_hash = put_definition(store_dir, machine_defn)
    with open(os.path.join(store_dir, "binary.bin"), "wb") as f:
        f.write(binary)
    cert = {"kind": "certificate", "cert": "correctness",
            "property": PROPERTY,
            "spec": spec_hash, "machine": machine_hash,
            "binary_hash": blake3_hex(binary), "binary_hex": binary.hex(),
            "inputs": spec_defn["inputs"]}
    cert_hash = put_definition(store_dir, cert)
    with open(os.path.join(store_dir, "certificate.json"), "wb") as f:
        f.write(canonical_bytes(cert))
    return {"spec": spec_hash, "machine": machine_hash,
            "certificate": cert_hash, "binary_hash": cert["binary_hash"],
            "binary_len": len(binary)}


def self_test_vectors(spec_defn):
    """Fixed inputs exercising the example, answers from the spec itself."""
    n = spec_defn["inputs"]
    points = [(0,) * n, (255,) * n, tuple(range(1, n + 1)),
              (0xA5,) * n, (1, 254)[:n] if n == 2 else (128,) * n]
    return [(list(p), spec_mod.eval_spec(spec_defn, list(p))) for p in points]


def all_inputs(n):
    return itertools.product(range(256), repeat=n)
