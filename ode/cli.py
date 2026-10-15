"""Ode command line.

    pypy3 -m ode build      SPEC.sexp STORE/ [len=N]  # produce W32 bytes + certificate
    pypy3 -m ode build-a64  SPEC.sexp STORE/ [len=N]  # produce AArch64 bytes + certificate
    pypy3 -m ode check      STORE/                    # prove the bytes compute the spec
    pypy3 -m ode run        STORE/ WORD...            # check, then run the proved program
    pypy3 -m ode hash       STORE/ MESSAGE            # BLAKE3 stores: hash a UTF-8 message
    pypy3 -m ode assure     STORE/                    # print the assurance map

`build` relies on nothing and proves nothing. `check` is what a relying
party runs: it re-derives the claim from the store's hashes and bytes.
`run` checks first and runs exactly the program it proved -- W32 by
interpretation, AArch64 natively on this CPU. A specification's
interface -- its input names, in order, and its outputs -- is stated in
the file itself: read its (inputs ...) and (outputs ...). Words are
decimal or 0x... integers. A spec with natural inputs, like
examples/blake3.sexp, is built at an instantiation (len=65); a list
input's word count follows from the spec's own requirement, which for
BLAKE3 is the message padded to whole 64-byte blocks. Callees named in
(uses ...) are found by hash among the spec file's neighbours.
"""
import os
import sys

from . import check, produce
from .canon import canonical_bytes, field, parse, read_canonical
from .store import Reject


def _check(store):
    with open(os.path.join(store, "certificate.sexp"), "rb") as f:
        cert = read_canonical(f.read())
    return check.check_certificate(store, cert)


def check_store(store):
    """The checker record for a store; raises Reject."""
    return _check(store)[0]


def _build(argv, isa):
    spec_path, store, *assign = argv
    with open(spec_path, "rb") as f:
        spec_defn = parse(f.read())
    at = {k: int(v) for k, v in (a.split("=") for a in assign)}
    if "len" in at and "m" not in at:  # BLAKE3's message words
        at["m"] = 16 * max(1, -(-at["len"] // 64))
    library = produce.library_of(os.path.dirname(os.path.abspath(spec_path)))
    result = produce.build(spec_defn, store, isa, at, library)
    print(f"spec        {result['spec']}")
    print(f"binary      {result['binary_hash']}  ({result['binary_len']} "
          f"bytes, {isa})")
    print(f"certificate {result['certificate']}")
    print(f"produced, not yet checked: run `pypy3 -m ode check {store}`")
    return 0


def cmd_check(argv):
    (store,) = argv
    try:
        record = check_store(store)
    except Reject as e:
        print(f"REJECT: {e}")
        return 1
    with open(os.path.join(store, "checker-record.sexp"), "wb") as f:
        f.write(canonical_bytes(record))
    print(f"ACCEPT ({field(record, 'checker')}, {field(record, 'property')}, "
          f"{field(record, 'dag-nodes')} DAG nodes)")
    print("  - the bytes compute the specification on every input")
    print("  - straight-line code: no branches, constant addresses")
    return 0


def cmd_run(argv):
    store, values = argv[0], [int(x, 0) for x in argv[1:]]
    try:
        _, program = _check(store)
        out = check.run(program, values)
    except (Reject, ValueError) as e:
        print(f"REJECT: {e}")
        return 1
    print(" ".join(str(x) for x in out))
    return 0


def cmd_hash(argv):
    """Hash a message with a proved BLAKE3 store built at its length."""
    import struct
    store, message = argv[0], " ".join(argv[1:]).encode("utf-8")
    try:
        record, program = _check(store)
        at = {str(k): v for k, v in field(record, "at")}
        if at.get("len") != len(message):
            raise Reject(f"this store is proved at len={at.get('len')}, "
                         f"the message has {len(message)} bytes")
        n = at["m"]
        words = list(struct.unpack(f"<{n}I", message + b"\0" * (4 * n - len(message))))
        out = check.run(program, words)
    except (Reject, ValueError) as e:
        print(f"REJECT: {e}")
        return 1
    print(struct.pack("<8I", *out).hex())
    return 0


def cmd_assure(argv):
    """The assurance map, generated from the checker record alone."""
    (store,) = argv
    path = os.path.join(store, "checker-record.sexp")
    if not os.path.isfile(path):
        print("no checker record: run `check` first")
        return 1
    with open(path, "rb") as f:
        r = read_canonical(f.read())
    isa = "AArch64" if "a64" in str(field(r, "property")) else "W32"
    text = "\n".join([
        "# Assurance map (generated from checker-record.sexp; do not edit)",
        "",
        f"Checker {field(r, 'checker')}: **{field(r, 'verdict')}**",
        "",
        "## Claims",
        "",
        f"- the {isa} bytes compute the specification on every input "
        f"(symbolic proof, {field(r, 'dag-nodes')} shared expression nodes)",
        "- straight-line code with constant addresses: the instruction and",
        "  address trace depends on nothing but the code",
        "",
        "## What the claims rest on",
        "",
        f"- specification `{field(r, 'spec').hex()}`",
        f"- binary `{field(r, 'binary-hash').hex()}`",
        f"- certificate `{field(r, 'certificate').hex()}`, property "
        f"`{field(r, 'property')}`",
        "- the checker, `ode/check.py` with `ode/word.py`"
        + (" and `ode/a64.py`" if isa == "AArch64" else "")
        + "; the reader, `ode/canon.py`; BLAKE3 (SPEC s1, R1, R2, R6)",
        "- that the specification says what its owners mean (R3): read it",
        ("- that this CPU executes the eight modelled AArch64 forms as "
         "modelled (R4): checked on random states by tests/test_a64.py, "
         "not proved" if isa == "AArch64" else
         "- W32's meaning is `ode/word.py`; no silicon is involved"),
        "",
        "## Gaps",
        "",
        "- no timing claim beyond the trace (R5: instruction timing and",
        "  power are outside it); everything not listed above is unproved",
        ""])
    with open(os.path.join(store, "assurance.md"), "w") as f:
        f.write(text)
    print(text)
    return 0


COMMANDS = {"build": lambda a: _build(a, "w32"),
            "build-a64": lambda a: _build(a, "a64"),
            "check": cmd_check, "run": cmd_run, "hash": cmd_hash,
            "assure": cmd_assure}


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    if not argv or argv[0] not in COMMANDS:
        print(__doc__)
        return 2
    return COMMANDS[argv[0]](argv[1:])


if __name__ == "__main__":
    raise SystemExit(main())
