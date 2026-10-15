"""The checker (SPEC s4.3, reliance R1): small, deterministic, offline.

It reads only canonical s-expression definitions from a store, named by
hash, and a certificate. For the toy property "equals-spec-v1" it proves
the claim itself, by exhaustion over the whole declared domain: it
evaluates the specification and the program decoded from the emitted
bytes on every input, and accepts exactly when they agree everywhere
and the bytes are the emitter's output for the named machine definition.
It imports no producer code: the compiler could be replaced by any
other, honest or hostile, and this file's verdicts would not change.

Verdicts: accepts, or rejects with a reason. No third outcome.
"""
import itertools
import os

from . import machine, spec as spec_mod
from .canon import Bytes, Sym, assoc, field, hash_of, read_canonical
from .blake3 import blake3

CHECKER_ID = Sym("ode-checker-0.1")
PROPERTY = "equals-spec-v1"


class Reject(Exception):
    pass


def _load(store_dir, h):
    if not isinstance(h, Bytes) or len(h) != 32:
        raise Reject(f"bad hash {h!r}")
    path = os.path.join(store_dir, h.hex() + ".sexp")
    if not os.path.isfile(path):
        raise Reject(f"definition {h} not in store")
    with open(path, "rb") as f:
        data = f.read()
    try:
        defn = read_canonical(data)
    except ValueError as e:
        raise Reject(str(e)) from e
    if hash_of(defn) != h:
        raise Reject(f"definition named {h.hex()} hashes to "
                     f"{hash_of(defn).hex()}")
    return defn


def _load_binary(store_dir, cert):
    """The bytes that run: the store's binary.bin, bound to the certificate.

    A certificate carries the binary's hex and hash; this is where they
    are tied to the file a user actually executes. A store whose
    binary.bin differs from its certificate -- by one byte, or by
    belonging to a different build -- is rejected here.
    """
    import os as _os
    path = _os.path.join(store_dir, "binary.bin")
    if not _os.path.isfile(path):
        raise Reject("store has no binary.bin")
    with open(path, "rb") as f:
        data = f.read()
    if not isinstance(field(cert, "binary"), Bytes):
        raise Reject("certificate carries no binary")
    if data != bytes(field(cert, "binary")):
        raise Reject("binary.bin is not the binary the certificate names")
    if Bytes(blake3(data)) != field(cert, "binary-hash"):
        raise Reject("binary.bin does not hash to the certificate's "
                     "binary-hash")
    return data


def check_certificate(store_dir, cert):
    """Returns a checker record (an s-expression) or raises Reject."""
    if not isinstance(cert, list) or not cert or cert[0] != "certificate":
        raise Reject("not a certificate")
    if field(cert, "cert") != "correctness":
        raise Reject(f"unsupported certificate kind {field(cert, 'cert')!r}")
    if field(cert, "property") != PROPERTY:
        raise Reject(f"unsupported property {field(cert, 'property')!r}")
    spec_defn = _load(store_dir, field(cert, "spec"))
    machine_defn = _load(store_dir, field(cert, "machine"))
    try:
        spec_mod.validate_spec(spec_defn)
        machine.validate_machine(machine_defn)
    except ValueError as e:
        raise Reject(str(e)) from e
    if machine.machine_inputs(machine_defn) != spec_mod.spec_inputs(spec_defn):
        raise Reject("spec and machine disagree on input count")
    n = spec_mod.spec_inputs(spec_defn)
    if field(cert, "inputs") != n:
        raise Reject("certificate names the wrong input count")
    binary = _load_binary(store_dir, cert)
    if machine.emit(machine_defn) != binary:
        raise Reject("binary is not the emitter's output for the machine "
                     "definition")
    try:
        code = machine.decode(binary, n)
    except ValueError as e:
        raise Reject(str(e)) from e
    # The proof, by exhaustion over the whole domain (SPEC s5: the
    # property's test definitions are the subject's own specification).
    # ODE8 has no branch instructions, so the accepted program's trace
    # depends only on its input count: the toy constant-time claim.
    cases = 0
    for inputs in itertools.product(range(256), repeat=n):
        want = spec_mod.eval_spec(spec_defn, list(inputs))
        got = machine.run(code, list(inputs))
        cases += 1
        if got != want:
            raise Reject(f"disagreement at inputs {list(inputs)}: "
                         f"spec gives {want}, machine gives {got}")
    return assoc("record", ("checker", CHECKER_ID), ("verdict", Sym("accept")),
                 ("property", Sym(PROPERTY)),
                 ("spec", field(cert, "spec")),
                 ("machine", field(cert, "machine")),
                 ("binary-hash", field(cert, "binary-hash")),
                 ("certificate", hash_of(cert)),
                 ("cases-checked", cases))


def check_store(store_dir):
    """Check the store's certificate.sexp; return its record."""
    path = os.path.join(store_dir, "certificate.sexp")
    with open(path, "rb") as f:
        cert = read_canonical(f.read())
    return check_certificate(store_dir, cert)


def assurance_markdown(record):
    """The assurance map (SPEC s7), generated from this record alone.

    Every sentence below is computed from the record's fields; a claim
    with no record behind it cannot be written here.
    """
    cases = field(record, "cases-checked")
    scope = (f"({cases} cases, the whole domain)" if cases is not None
             else f"(symbolic proof over {field(record, 'domain')}, "
                  f"{field(record, 'dag-nodes')} shared expression nodes)")
    lines = ["# Assurance map (generated by ode/checker.py; do not edit)",
             "",
             f"Checker: {field(record, 'checker')} -- verdict: "
             f"**{field(record, 'verdict')}**",
             "",
             "## Claims, each resting on the record above",
             "",
             "- the emitted bytes compute the specification on every "
             f"input {scope}",
             "- the program is straight-line: its ISA has no branch "
             "instructions, so its instruction trace depends only on "
             "its input count",
             "",
             "## What each claim rests on (hashes)",
             "",
             f"- specification: `{field(record, 'spec').hex()}`",
             f"- machine definition: `{field(record, 'machine').hex()}`",
             f"- emitted binary: `{field(record, 'binary-hash').hex()}`",
             f"- certificate: `{field(record, 'certificate').hex()}`",
             f"- property: `{field(record, 'property')}` (SPEC s5)",
             "",
             "## Reliance, stated on the face of the map (SPEC s1)",
             "",
             "- the checker program (R1): `ode/checker.py`, the program",
             "  that issued this record's verdict, small enough to read",
             "  in one sitting -- this map is its output, not the checker",
             "- the canonical-form reader (R2): `ode/canon.py`",
             "- the specification and property definitions say what their",
             "  owners mean (R3): read them; their hashes are above",
             "- ODE8's semantics as implemented in `ode/machine.py` are the",
             "  toy ISA model (R4 at toy scale: a VM, no silicon)",
             "- BLAKE3 collision resistance (R6)",
             "",
             "## Gaps, first-class (SPEC s7)",
             "",
             "- toy scale: byte functions of 1-2 inputs, proved by",
             "  exhaustion; no silicon, no timing promise, no power or",
             "  clock claim (R5 is empty here and says so)",
             "- everything not listed under Claims is unproved",
             ""]
    return "\n".join(lines)
