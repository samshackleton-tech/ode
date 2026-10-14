"""Canonical form and content addressing (SPEC s2).

A definition is a JSON value built only from: objects with string keys,
arrays, strings, and integers in [0, 2**64). Its canonical form is UTF-8
JSON with keys sorted, no whitespace, integers in decimal. Its identity
is the BLAKE3 hash of that form, hex-encoded.
"""
import json

from .blake3 import blake3_hex

MAX_INT = 2 ** 64


def _validate(v, path="$"):
    if isinstance(v, bool):
        raise ValueError(f"{path}: booleans are not canonical values")
    if isinstance(v, int):
        if not (0 <= v < MAX_INT):
            raise ValueError(f"{path}: integer out of range")
        return
    if isinstance(v, str):
        return
    if isinstance(v, list):
        for i, x in enumerate(v):
            _validate(x, f"{path}[{i}]")
        return
    if isinstance(v, dict):
        for k, x in v.items():
            if not isinstance(k, str):
                raise ValueError(f"{path}: non-string key")
            _validate(x, f"{path}.{k}")
        return
    raise ValueError(f"{path}: {type(v).__name__} is not a canonical value")


def canonical_bytes(defn) -> bytes:
    """The one byte encoding of a definition. Rejects anything ambiguous."""
    _validate(defn)
    return json.dumps(defn, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=False).encode("utf-8")


def read_canonical(data: bytes):
    """The canonical-form reader (reliance R2): bytes -> definition.

    Accepts a byte string only when it is exactly the canonical form of
    the definition it decodes to; every other string is rejected.
    """
    assert isinstance(data, bytes)
    try:
        defn = json.loads(data.decode("utf-8"))
    except Exception as e:
        raise ValueError(f"not canonical form: {e}") from e
    if canonical_bytes(defn) != data:
        raise ValueError("not canonical form: re-encoding differs")
    return defn


def hash_of(defn) -> str:
    return blake3_hex(canonical_bytes(defn))
