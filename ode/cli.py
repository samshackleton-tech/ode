"""Ode command line.

    pypy3 -m ode --version                           # release version
    pypy3 -m ode build      SPEC.sexp STORE/ [len=N]  # produce W32 bytes + certificate
    pypy3 -m ode build-a64  SPEC.sexp STORE/ [len=N]  # produce AArch64 bytes + certificate
    pypy3 -m ode bind       SPEC.sexp STORE/ [w32]    # the spec itself, callees proved (AArch64)
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
(uses ...) are found by hash among the spec file's neighbours. `bind`
makes a store whose one certificate covers every instantiation: the
spec itself runs, with each callee bound to its proved code, so `hash`
on such a store takes a message of any length.
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


def cmd_bind(argv):
    spec_path, store, *isa = argv
    with open(spec_path, "rb") as f:
        spec_defn = parse(f.read())
    library = produce.library_of(os.path.dirname(os.path.abspath(spec_path)))
    result = produce.bind(spec_defn, store, (isa or ["a64"])[0], library)
    print(f"spec        {result['spec']}")
    print(f"certificate {result['certificate']}  (every instantiation)")
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
    if field(record, "property") == "spec-with-callees-v1":
        print("  - running the specification with its bound callees computes it,")
        print("    at every instantiation; each callee proved for every input")
    else:
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
        n = 16 * max(1, -(-len(message) // 64))
        words = list(struct.unpack(f"<{n}I", message + b"\0" * (4 * n - len(message))))
        if program[0] == "spec":
            out = check.run(program, words, {"len": len(message)})
        else:
            at = {str(k): v for k, v in field(record, "at")}
            if at.get("len") != len(message):
                raise Reject(f"this store is proved at len={at.get('len')}, "
                             f"the message has {len(message)} bytes")
            out = check.run(program, words)
    except (Reject, ValueError) as e:
        print(f"REJECT: {e}")
        return 1
    print(struct.pack("<8I", *out).hex())
    return 0


def cmd_assure(argv):
    """Recheck the store and report exactly the resulting model-level claim."""
    (store,) = argv
    try:
        r = check_store(store)
    except Reject as e:
        print(f"REJECT: {e}")
        return 1
    prop = str(field(r, "property"))
    binding = prop == "spec-with-callees-v1"
    claims = ([
        "- the specification runs through its evaluator at every valid instantiation",
        "- each bound callee is checked against its named specification",
        "- the interpreter's control flow and runtime are outside a native trace claim",
    ] if binding else [
        "- the decoded bytes compute the specification for every input at the stated instantiation",
        "- decoded instructions are straight-line with constant addresses in the declared model",
        f"- binary `{field(r, 'binary-hash').hex()}`",
        f"- instantiation `{canonical_bytes(field(r, 'at')).decode()}`",
    ])
    text = "\n".join([
        "# Assurance map (store rechecked for this report)", "",
        f"Checker {field(r, 'checker')}: **{field(r, 'verdict')}**", "",
        "## Checked claim", "", *claims, "",
        f"- specification `{field(r, 'spec').hex()}`",
        f"- certificate `{field(r, 'certificate').hex()}`, property `{prop}`", "",
        "## Reliance and boundaries", "",
        "- the owner's specification, the checker, reader, evaluator, and symbolic normalizer",
        "- domain-separated BLAKE3 identities and the store's exact checked bytes",
        "- AArch64 callees additionally rely on Ode's instruction model and native runner",
        "- PyPy, its standard library, the operating system, and hardware",
        "- CPU cross-checks exercise the AArch64 model; Arm ISA refinement remains open",
        "- native memory behavior, calling conventions, and physical constant-time guarantees",
        "  remain outside the proof-object kernel's current guarantees", "",
        "This report describes the checked store; owner approval of its specification is separate.", "",
    ])
    with open(os.path.join(store, "assurance.md"), "w") as f:
        f.write(text)
    print(text)
    return 0


COMMANDS = {"build": lambda a: _build(a, "w32"),
            "build-a64": lambda a: _build(a, "a64"),
            "bind": cmd_bind, "check": cmd_check, "run": cmd_run, "hash": cmd_hash,
            "assure": cmd_assure}


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    if argv == ["--version"]:
        from pathlib import Path
        print("Ode " + (Path(__file__).resolve().parent.parent / "VERSION").read_text().strip())
        return 0
    if not argv or argv[0] not in COMMANDS:
        print(__doc__)
        return 2
    return COMMANDS[argv[0]](argv[1:])


if __name__ == "__main__":
    raise SystemExit(main())
