"""Ode command line: build (produce), check (rely), run, assure.

    pypy3 -m ode build  examples/mix.json BUILD/
    pypy3 -m ode check  BUILD/
    pypy3 -m ode run    BUILD/ 60 165
    pypy3 -m ode assure BUILD/

`build` trusts nothing and proves nothing; it produces definitions, a
binary, and a certificate. `check` is the only command whose output a
relying party needs: it re-derives every claim from the hashes alone.
`assure` prints the assurance map generated from the checker record.
"""
import json
import os
import sys

from . import checker, machine, producer
from .canon import read_canonical


def _read_json_file(path):
    with open(path, "rb") as f:
        return read_canonical(f.read())


def cmd_build(argv):
    spec_path, store = argv
    spec_defn = _read_json_file(spec_path)
    result = producer.build(spec_defn, store)
    vectors = producer.self_test_vectors(spec_defn)
    with open(os.path.join(store, "self_test.json"), "w") as f:
        json.dump(vectors, f)
    print(f"spec        {result['spec']}")
    print(f"machine     {result['machine']}")
    print(f"binary      {result['binary_hash']}  ({result['binary_len']} bytes)")
    print(f"certificate {result['certificate']}")
    print("produced, not yet checked: run `pypy3 -m ode check "
          f"{store}`")
    return 0


def cmd_check(argv):
    (store,) = argv
    try:
        record = checker.check_store(store)
    except checker.Reject as e:
        print(f"REJECT: {e}")
        return 1
    with open(os.path.join(store, "checker-record.json"), "w") as f:
        json.dump(record, f, indent=2, sort_keys=True)
    print(f"ACCEPT ({record['checker']}, {record['cases_checked']} cases)")
    for c in record["claims"]:
        print(f"  - {c}")
    return 0


def cmd_run(argv):
    store, inputs = argv[0], [int(x) for x in argv[1:]]
    with open(os.path.join(store, "binary.bin"), "rb") as f:
        binary = f.read()
    print(machine.run_binary(binary, inputs))
    return 0


def cmd_assure(argv):
    (store,) = argv
    path = os.path.join(store, "checker-record.json")
    if not os.path.isfile(path):
        print("no checker record: run `check` first")
        return 1
    with open(path) as f:
        record = json.load(f)
    text = checker.assurance_markdown(record)
    with open(os.path.join(store, "assurance.md"), "w") as f:
        f.write(text)
    print(text)
    return 0


COMMANDS = {"build": cmd_build, "check": cmd_check,
            "run": cmd_run, "assure": cmd_assure}


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    if not argv or argv[0] not in COMMANDS:
        print(__doc__)
        return 2
    return COMMANDS[argv[0]](argv[1:])


if __name__ == "__main__":
    raise SystemExit(main())
