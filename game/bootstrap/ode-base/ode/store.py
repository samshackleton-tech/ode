"""Reading a store: definitions by hash, and the binary that runs.

Shared by both checkers, and the only store code in a relying party's
bootstrap: a store is a directory of canonical s-expressions named by
their BLAKE3 hash (<hash>.sexp) plus binary.bin. Loading is strict --
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
    """The bytes that run: the store's binary.bin, bound to the certificate.

    A certificate carries the binary itself and its hash; this is where
    they are tied to the file a user actually executes. A store whose
    binary.bin differs from its certificate -- by one byte, or by
    belonging to a different build -- is rejected here.
    """
    path = os.path.join(store_dir, "binary.bin")
    if not os.path.isfile(path):
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
