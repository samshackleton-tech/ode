"""Canonical form and content addressing (SPEC s2).

Ode's one syntax is the s-expression. A canonical value is an integer in
[0, 2**64), a symbol, a byte string, or a list of canonical values. A
symbol matches [A-Za-z_][A-Za-z0-9._/*+<>=?!-]* -- no strings, no
quoting, nothing to escape; it never begins with a digit, so no token is
both an integer and a symbol. A byte string is written #hex -- '#'
followed by an even number of lowercase hex digits (#  alone is the empty
string) -- the one form for binaries, hashes, and other opaque bytes. The
canonical form of a value is its s-expression written with exactly one
space between elements and no other whitespace:

    (spec (name mix) (inputs 2) (body (rotl (add (xor (var 0) (var 1)) (const 60)) 3)))

A definition's identity is the BLAKE3 hash of its canonical form.
Definitions are written as association lists -- (kind (field value) ...)
-- and read with `field`. Text files may be formatted freely and use
';' comments; canonical form is what hashes and the checker read.
"""
import re

from .blake3 import blake3

MAX_INT = 2 ** 64
_SYMBOL = re.compile(r"[A-Za-z_][A-Za-z0-9._/*+<>=?!-]*\Z")
_BYTES = re.compile(r"#([0-9a-f][0-9a-f])*\Z")


class Sym(str):
    """A symbol: a name."""
    __slots__ = ()


class Bytes(bytes):
    """A byte string: opaque bytes, written #hex."""
    __slots__ = ()


def is_symbol(x):
    return isinstance(x, Sym)


def _validate(v, path="$"):
    if isinstance(v, bool):
        raise ValueError(f"{path}: booleans are not canonical values")
    if isinstance(v, int):
        if not (0 <= v < MAX_INT):
            raise ValueError(f"{path}: integer out of range")
        return
    if isinstance(v, Sym):
        if not _SYMBOL.match(v):
            raise ValueError(f"{path}: bad symbol {v!r}")
        return
    if isinstance(v, Bytes):
        return
    if isinstance(v, list):
        for i, x in enumerate(v):
            _validate(x, f"{path}[{i}]")
        return
    raise ValueError(f"{path}: {type(v).__name__} is not a canonical value")


def canonical_bytes(value) -> bytes:
    """The one byte encoding of a canonical value."""
    _validate(value)
    return _dump(value).encode("utf-8")


def _dump(v):
    if isinstance(v, int):
        return str(v)
    if isinstance(v, Sym):
        return str(v)
    if isinstance(v, Bytes):
        return "#" + v.hex()
    return "(" + " ".join(_dump(x) for x in v) + ")"


def _tokens(text):
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c in " \t\r\n":
            i += 1
        elif c == ";":
            while i < n and text[i] != "\n":
                i += 1
        elif c in "()":
            yield c
            i += 1
        else:
            j = i
            while j < n and text[j] not in " \t\r\n();":
                j += 1
            yield text[i:j]
            i = j


def parse(text):
    """Text (any formatting, ';' comments) -> canonical value."""
    if isinstance(text, bytes):
        text = text.decode("utf-8")
    toks = list(_tokens(text))
    pos = 0

    def one():
        nonlocal pos
        if pos >= len(toks):
            raise ValueError("unexpected end of input")
        t = toks[pos]
        pos += 1
        if t == "(":
            out = []
            while True:
                if pos >= len(toks):
                    raise ValueError("unclosed '('")
                if toks[pos] == ")":
                    pos += 1
                    return out
                out.append(one())
        if t == ")":
            raise ValueError("unexpected ')'")
        if t.isdigit():
            if len(t) > 1 and t[0] == "0":
                raise ValueError(f"non-canonical integer {t!r}")
            return int(t)
        if t[0] == "#":
            if not _BYTES.match(t):
                raise ValueError(f"bad byte string {t!r}")
            return Bytes(bytes.fromhex(t[1:]))
        if not _SYMBOL.match(t):
            raise ValueError(f"bad symbol {t!r}")
        return Sym(t)

    value = one()
    if pos != len(toks):
        raise ValueError("junk after the first form")
    _validate(value)
    return value


def read_canonical(data: bytes):
    """The canonical-form reader (reliance R2): bytes -> value.

    Accepts a byte string only when it is exactly the canonical form of
    the value it parses to; every other string is rejected.
    """
    assert isinstance(data, bytes)
    try:
        value = parse(data)
    except (ValueError, UnicodeDecodeError) as e:
        raise ValueError(f"not canonical form: {e}") from e
    if canonical_bytes(value) != data:
        raise ValueError("not canonical form: re-encoding differs")
    return value


def hash_of(value) -> "Bytes":
    """A definition's identity: the BLAKE3 hash of its canonical form."""
    return Bytes(blake3(canonical_bytes(value)))


def field(defn, name):
    """(kind (name value) ...) -> the value of a field, or None."""
    for item in defn[1:]:
        if isinstance(item, list) and len(item) == 2 and item[0] == name:
            return item[1]
    return None


def assoc(kind, *pairs):
    """Build a definition: (kind (name value) ...)."""
    return [Sym(kind)] + [[Sym(k), v] for k, v in pairs]
