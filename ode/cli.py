"""Ode command line: build (produce), check (rely), run, assure.

    pypy3 -m ode build  examples/mix.sexp BUILD/
    pypy3 -m ode check  BUILD/
    pypy3 -m ode run    BUILD/ 60 165
    pypy3 -m ode assure BUILD/

Word programs (u32, symbolic proofs; SPEC s3 at word scale):

    pypy3 -m ode buildw examples/blake3-g.sexp BUILD/
    pypy3 -m ode checkw BUILD/
    pypy3 -m ode runw   BUILD/ 1 2 3 4 5 6

A word program's interface -- its input names, in order, and its outputs
-- is stated in its specification file itself: read the (inputs ...) and
(outputs ...) of e.g. examples/blake3-g.sexp. `runw` takes the inputs as
decimal (or 0x...) integers and prints the output words.

`build` relies on nothing and proves nothing; it produces definitions, a
binary, and a certificate. `check` is the only command whose output a
relying party needs: it re-derives every claim from the hashes alone.
`assure` prints the assurance map generated from the checker record.
All definitions and records are canonical s-expressions (ode/canon.py).
"""
import os
import sys

from . import checker, machine, producer, wcheck, word, wproducer
from .canon import canonical_bytes, field, parse, read_canonical


def _read_text_file(path):
    with open(path, "rb") as f:
        return parse(f.read())


def cmd_build(argv):
    spec_path, store = argv
    spec_defn = _read_text_file(spec_path)
    result = producer.build(spec_defn, store)
    with open(os.path.join(store, "self-test.sexp"), "wb") as f:
        f.write(canonical_bytes(producer.self_test_vectors(spec_defn)))
    print(f"spec        {result['spec']}")
    print(f"machine     {result['machine']}")
    print(f"binary      {result['binary_hash']}  ({result['binary_len']} bytes)")
    print(f"certificate {result['certificate']}")
    print(f"produced, not yet checked: run `pypy3 -m ode check {store}`")
    return 0


def cmd_check(argv):
    (store,) = argv
    try:
        record = checker.check_store(store)
    except checker.Reject as e:
        print(f"REJECT: {e}")
        return 1
    with open(os.path.join(store, "checker-record.sexp"), "wb") as f:
        f.write(canonical_bytes(record))
    print(f"ACCEPT ({field(record, 'checker')}, "
          f"{field(record, 'cases-checked')} cases)")
    print("  - the emitted bytes compute the specification on every input")
    print("  - the program is straight-line ODE8: its instruction trace "
          "depends only on its input count")
    return 0


def cmd_run(argv):
    store, inputs = argv[0], [int(x) for x in argv[1:]]
    with open(os.path.join(store, "binary.bin"), "rb") as f:
        binary = f.read()
    print(machine.run_binary(binary, inputs))
    return 0


def cmd_assure(argv):
    (store,) = argv
    path = os.path.join(store, "checker-record.sexp")
    if not os.path.isfile(path):
        print("no checker record: run `check` first")
        return 1
    with open(path, "rb") as f:
        record = read_canonical(f.read())
    text = checker.assurance_markdown(record)
    with open(os.path.join(store, "assurance.md"), "w") as f:
        f.write(text)
    print(text)
    return 0


def check_word_store(store):
    """Check a word store's certificate.sexp; return the checker record."""
    with open(os.path.join(store, "certificate.sexp"), "rb") as f:
        cert = read_canonical(f.read())
    record, _ = wcheck.check_certificate(store, cert)
    return record


def cmd_buildw(argv):
    spec_path, store = argv
    spec_defn = _read_text_file(spec_path)
    result = wproducer.build(spec_defn, store)
    print(f"spec        {result['spec']}")
    print(f"machine     {result['machine']}")
    print(f"binary      {result['binary_hash']}  ({result['binary_len']} bytes)")
    print(f"certificate {result['certificate']}")
    print(f"produced, not yet checked: run `pypy3 -m ode checkw {store}`")
    return 0


def cmd_checkw(argv):
    (store,) = argv
    try:
        record = check_word_store(store)
    except checker.Reject as e:
        print(f"REJECT: {e}")
        return 1
    with open(os.path.join(store, "checker-record.sexp"), "wb") as f:
        f.write(canonical_bytes(record))
    print(f"ACCEPT ({field(record, 'checker')}, symbolic over "
          f"{field(record, 'domain')}, {field(record, 'dag-nodes')} DAG nodes)")
    print(f"  - the {'AArch64' if 'a64' in str(field(record, 'property')) else 'W32'} "
          "bytes compute the specification on every input")
    print("  - the program is straight-line: no branches, constant addresses")
    return 0


def cmd_runw(argv):
    store, values = argv[0], [int(x, 0) for x in argv[1:]]
    cert = read_canonical(open(os.path.join(store, "certificate.sexp"),
                               "rb").read())
    spec_defn = checker._load(store, field(cert, "spec"))
    with open(os.path.join(store, "binary.bin"), "rb") as f:
        binary = f.read()
    decoded = word.decode_w32(binary, word.inputs_of(spec_defn))
    print(" ".join(str(x) for x in word.run_program(decoded, values)))
    return 0


def cmd_builda(argv):
    spec_path, store = argv
    result = wproducer.build_a64(_read_text_file(spec_path), store)
    print(f"spec        {result['spec']}")
    print(f"binary      {result['binary_hash']}  ({result['binary_len']} bytes of AArch64)")
    print(f"certificate {result['certificate']}")
    print(f"produced, not yet checked: run `pypy3 -m ode checkw {store}`")
    return 0


def cmd_runa(argv):
    """Check, then run the proved AArch64 bytes natively on this CPU."""
    from . import native
    store, values = argv[0], [int(x, 0) for x in argv[1:]]
    with open(os.path.join(store, "certificate.sexp"), "rb") as f:
        cert = read_canonical(f.read())
    try:
        _, program = wcheck.check_certificate(store, cert)
    except checker.Reject as e:
        print(f"REJECT: {e}")
        return 1
    kind, code, sizes = program
    fn = native.Function(code, sizes["in"], sizes["out"], sizes["scratch"])
    print(" ".join(str(x) for x in fn(values)))
    return 0


COMMANDS = {"build": cmd_build, "check": cmd_check,
            "run": cmd_run, "assure": cmd_assure,
            "buildw": cmd_buildw, "checkw": cmd_checkw, "runw": cmd_runw,
            "builda": cmd_builda, "runa": cmd_runa}


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    if not argv or argv[0] not in COMMANDS:
        print(__doc__)
        return 2
    return COMMANDS[argv[0]](argv[1:])


if __name__ == "__main__":
    raise SystemExit(main())
