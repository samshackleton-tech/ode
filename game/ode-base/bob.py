"""Bob: the relying party's procedure, run by the root (root/launch.py).

The root has already confirmed this ode-base is the one the package
pins, and runs this file from the bytes it hashed. With the package's
RELIANCE bytes and Mallory's store, Bob:
  1. finds TARGET's pinned spec hash;
  2. reads Mallory's certificate and requires its (spec ...) to be that
     hash -- a certificate about any other specification proves nothing;
  3. runs the checker, which loads the spec by that hash and proves the
     binary it reads, once;
  4. prints ACCEPT and runs exactly the program it proved -- W32 by
     interpretation, AArch64 natively -- after checking the inputs are
     in the spec's domain.
Prints exactly one verdict line first: ACCEPT or REJECT <reason>.
"""
import os

from ode import check
from ode.canon import field, parse, read_canonical
from ode.store import Reject


def main(reliance_bytes, argv):
    store, target = os.path.abspath(argv[0]), argv[1]
    try:
        values = [int(x, 0) for x in argv[2:]]
    except ValueError:
        print("REJECT inputs must be integers")
        return 1
    pins = [p[1] for p in field(parse(reliance_bytes), "targets") or []
            if isinstance(p, list) and len(p) == 2 and p[0] == target]
    if len(pins) != 1:
        print(f"REJECT unknown target {target}")
        return 1
    try:
        with open(os.path.join(store, "certificate.sexp"), "rb") as f:
            cert = read_canonical(f.read())
    except (OSError, ValueError) as e:
        print(f"REJECT cannot read certificate: {e}")
        return 1
    if field(cert, "spec") != pins[0]:
        print("REJECT certificate is not about the relied-upon specification")
        return 1
    try:
        _, program = check.check_certificate(store, cert)
    except Reject as e:
        print(f"REJECT {e}")
        return 1
    except Exception as e:  # any crash in the checker is a rejection
        print(f"REJECT checker failed: {type(e).__name__}: {e}")
        return 1
    n_in = program[2]["in"]
    if len(values) != n_in or any(not (0 <= v < 2 ** 32) for v in values):
        print(f"REJECT inputs must be {n_in} u32 words")
        return 1
    print("ACCEPT")
    print(" ".join(str(v) for v in check.run(program, values)))
    return 0
