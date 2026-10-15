#!/usr/bin/env pypy3
"""Bob: the relying party's whole procedure, followed literally.

    pypy3 bootstrap/bob.py MALLORY_DIR TARGET word...

Bob holds this directory (from Sam) and relies on nothing else. He:
  1. loads the checker and reader from THIS directory, by absolute path,
     before anything else, so nothing in Mallory's directory can shadow
     them;
  2. reads RELIANCE, finds TARGET (g or hash65), parses its spec, and
     confirms the hash;
  3. reads Mallory's certificate.sexp and requires that the certificate's
     (spec ...) IS that hash -- a certificate about any other
     specification proves nothing about G;
  4. runs the checker over Mallory's store;
  5. on ACCEPT, decodes Mallory's binary.bin and runs it on the inputs.
Prints exactly one verdict line first: ACCEPT or REJECT <reason>.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path[:0] = [HERE]  # the bootstrap's ode package, and only it

from ode import wcheck, word  # noqa: E402
from ode.canon import field, hash_of, parse, read_canonical  # noqa: E402
from ode.store import Reject  # noqa: E402

assert wcheck.__file__.startswith(HERE), "checker loaded from outside bootstrap"


def main(argv):
    if len(argv) < 3:
        print("usage: bob.py MALLORY_DIR TARGET word...")
        return 2
    store, target = os.path.abspath(argv[0]), argv[1]
    values = [int(x, 0) for x in argv[2:]]
    with open(os.path.join(HERE, "RELIANCE"), "rb") as f:
        reliance = parse(f.read())
    entries = [e for e in field(reliance, "targets") if e and e[0] == target]
    if len(entries) != 1:
        print(f"REJECT unknown target {target}")
        return 1
    entry = entries[0]  # (name (spec ...) (spec-hash ...))
    with open(os.path.join(HERE, str(field(entry, "spec"))), "rb") as f:
        spec_defn = parse(f.read())
    n_in = len(word.inputs_of(spec_defn))
    if len(values) != n_in or any(not (0 <= v < 2 ** 32) for v in values):
        print(f"REJECT inputs must be {n_in} u32 words")  # the spec's domain
        return 1
    spec_hash = hash_of(spec_defn)
    if spec_hash != field(entry, "spec-hash"):
        print("REJECT bootstrap spec does not match RELIANCE")
        return 1
    try:
        with open(os.path.join(store, "certificate.sexp"), "rb") as f:
            cert = read_canonical(f.read())
    except (OSError, ValueError) as e:
        print(f"REJECT cannot read certificate: {e}")
        return 1
    if field(cert, "spec") != spec_hash:
        print("REJECT certificate is not about the relied-upon specification")
        return 1
    try:
        record = wcheck.check_certificate(store, cert)
    except Reject as e:
        print(f"REJECT {e}")
        return 1
    except Exception as e:  # any crash in the checker is a rejection
        print(f"REJECT checker failed: {type(e).__name__}: {e}")
        return 1
    print("ACCEPT")
    with open(os.path.join(store, "binary.bin"), "rb") as f:
        binary = f.read()
    inputs = word.inputs_of(spec_defn)
    decoded = word.decode_w32(binary, inputs)
    out = word.run_program(decoded, values)
    print(" ".join(str(v) for v in out))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
