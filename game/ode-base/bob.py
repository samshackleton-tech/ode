"""Bob: the relying party's procedure, run by the root (root/launch.py).

The root has already confirmed this ode-base is the one the package
pins, and runs this file from the hashed bytes. Bob, with the
package's RELIANCE bytes and Mallory's store:
  1. finds TARGET's pinned spec hash;
  2. reads Mallory's certificate and requires its (spec ...) to be that
     hash -- a certificate about any other specification proves nothing;
  3. loads the spec from Mallory's store BY that hash (the bytes may come
     from anywhere; the hash makes them the pinned spec or a reject), and
     requires the inputs to be in the spec's domain;
  4. runs the checker over Mallory's store;
  5. on ACCEPT, decodes Mallory's binary.bin and runs it.
Prints exactly one verdict line first: ACCEPT or REJECT <reason>.
"""
import os

from ode import wcheck, word
from ode.canon import field, parse, read_canonical
from ode.store import Reject, load_definition


def main(reliance_bytes, argv):
    store, target = os.path.abspath(argv[0]), argv[1]
    try:
        values = [int(x, 0) for x in argv[2:]]
    except ValueError:
        print("REJECT inputs must be integers")
        return 1
    reliance = parse(reliance_bytes)
    entries = [e for e in field(reliance, "targets") or [] if e and e[0] == target]
    if len(entries) != 1:
        print(f"REJECT unknown target {target}")
        return 1
    spec_hash = field(entries[0], "spec-hash")
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
        spec_defn = load_definition(store, spec_hash)
        word.validate_wspec(spec_defn)
    except (Reject, ValueError) as e:
        print(f"REJECT {e}")
        return 1
    n_in = len(word.inputs_of(spec_defn))
    if len(values) != n_in or any(not (0 <= v < 2 ** 32) for v in values):
        print(f"REJECT inputs must be {n_in} u32 words")
        return 1
    try:
        wcheck.check_certificate(store, cert)
    except Reject as e:
        print(f"REJECT {e}")
        return 1
    except Exception as e:  # any crash in the checker is a rejection
        print(f"REJECT checker failed: {type(e).__name__}: {e}")
        return 1
    print("ACCEPT")
    with open(os.path.join(store, "binary.bin"), "rb") as f:
        binary = f.read()
    decoded = word.decode_w32(binary, word.inputs_of(spec_defn))
    print(" ".join(str(v) for v in word.run_program(decoded, values)))
    return 0
