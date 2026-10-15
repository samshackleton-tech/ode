#!/usr/bin/env pypy3
"""Bob: the relying party's whole procedure, followed literally.

    pypy3 bootstrap/bob.py MALLORY_DIR a b c d x y

Bob holds this directory (from Sam) and nothing else he trusts. He:
  1. loads the checker and reader from THIS directory, by absolute path,
     before anything else, so nothing in Mallory's directory can shadow
     them;
  2. reads TRUST, parses blake3-g.sexp, and confirms its hash;
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
from ode.checker import Reject  # noqa: E402

assert wcheck.__file__.startswith(HERE), "checker loaded from outside bootstrap"


def main(argv):
    if len(argv) < 2:
        print("usage: bob.py MALLORY_DIR a b c d x y")
        return 2
    store, values = os.path.abspath(argv[0]), [int(x, 0) for x in argv[1:]]
    if len(values) != 6 or any(not (0 <= v < 2 ** 32) for v in values):
        print("REJECT inputs must be six u32 words")  # the spec's domain
        return 1
    with open(os.path.join(HERE, "TRUST"), "rb") as f:
        trust = parse(f.read())
    with open(os.path.join(HERE, str(field(trust, "spec"))), "rb") as f:
        spec_defn = parse(f.read())
    spec_hash = hash_of(spec_defn)
    if spec_hash != field(trust, "spec-hash"):
        print("REJECT bootstrap spec does not match TRUST")
        return 1
    try:
        with open(os.path.join(store, "certificate.sexp"), "rb") as f:
            cert = read_canonical(f.read())
    except (OSError, ValueError) as e:
        print(f"REJECT cannot read certificate: {e}")
        return 1
    if field(cert, "spec") != spec_hash:
        print("REJECT certificate is not about the trusted specification")
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
