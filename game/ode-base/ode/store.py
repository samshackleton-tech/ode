"""Reading a store: definitions by hash, and the binary that runs.

The checker's, and the only store code in a relying party's
bootstrap: a store is a directory of canonical s-expressions named by
their BLAKE3 hash (<hash>.sexp) and binaries named likewise (<hash>.bin);
certificate.sexp names the one to check. Loading is strict --
bytes must be canonical, and must hash to the name they were fetched
under. Anything else is a Reject, for the checkers to report.
"""
import os

from .blake3 import blake3
from .canon import Bytes, field, hash_of, read_canonical


class Reject(Exception):
    """The checker rejects; this exception carries the reason."""


def load_definition(store_dir, h):
    if not isinstance(h, Bytes) or len(h) != 32:
        raise Reject(f"bad hash {h!r}")
    path = os.path.join(store_dir, h.hex() + ".sexp")
    if not os.path.isfile(path):
        raise Reject(f"definition {h.hex()} not in store")
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


def load_binary(store_dir, cert):
    """The bytes that run: <binary-hash>.bin, read once, bound by hash.

    The caller must check and run these returned bytes, never re-read the
    file: a store's owner may change it between two reads.
    """
    h = field(cert, "binary-hash")
    if not isinstance(h, Bytes) or len(h) != 32:
        raise Reject("certificate names no binary-hash")
    path = os.path.join(store_dir, h.hex() + ".bin")
    if not os.path.isfile(path):
        raise Reject(f"binary {h.hex()} not in store")
    with open(path, "rb") as f:
        data = f.read()
    if Bytes(blake3(data)) != h:
        raise Reject("the binary file is not the binary the certificate names")
    return data
