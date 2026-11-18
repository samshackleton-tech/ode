#!/usr/bin/env python3
"""decode: the instruction at a place in a file's code, by the table.

`decode` gives the decoded row of the instruction at `at` (its length, its text as the table's ROW writes
it), or None where the bytes there are no instance of a row as the table writes one.

How: `candidates` proposes what the bytes might be (a way of a row, what each placeholder would be, how many
bytes). Nothing in `candidates` is relied on. A proposal is taken only if `encode.encode` writes, for that
way and those placeholders, the very bytes that are there; and the text is then written from the same way and
placeholders, and must be an instance of that same row first of all the table's. So the bytes read as an
instruction are always bytes the table writes for it, in the one form the table writes."""
import os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import table, encode

M64 = table.M64
ROWS = table.read(os.environ.get("ODE_TABLE") or os.path.join(HERE, "x86.tab"))       # (ODE_TABLE: another table, for the tests' controls)
HEADS = table.by_head(ROWS)
WAYS = encode.ways(ROWS)
ORDER = {id(w): i for i, w in enumerate(WAYS)}

# where to look: the ways by what a first glance at the bytes shows (the kind of prefix, the prefix an instruction needs, the map, the opcode)
INDEX, LITERAL = {}, {}
for _w in WAYS:
    if _w.literal is not None: LITERAL.setdefault(_w.literal[0], []).append(_w)
    else:
        for _r in range(8 if _w.plus else 1): INDEX.setdefault((_w.kind, _w.pp, _w.map, _w.opcode | _r), []).append(_w)


def sx(n, bits): return n - (1 << bits) if n >> (bits - 1) else n


def candidates(code, at, addr):
    """NOT RELIED ON. What the bytes at `at` might be: (a way, what its placeholders would be, how many bytes)."""
    found = [(w, {}, len(w.literal)) for w in LITERAL.get(code[at], ()) if code[at:at + len(w.literal)] == w.literal]
    try:
        p, b = at, code[at]
        pp = W = R = X = B = R2 = v = k = m = 0
        if b == 0x62:
            kind, (p0, p1, p2), p = "E", code[p + 1:p + 4], p + 4
            R, X, B, R2, m = (~p0 >> 7) & 1, (~p0 >> 6) & 1, (~p0 >> 5) & 1, (~p0 >> 4) & 1, p0 & 7
            W, v, pp, k = p1 >> 7, (~p1 >> 3) & 15 | ((~p2 >> 3) & 1) << 4, p1 & 3, p2 & 7
        elif b == 0xC5: kind, p1, p, m = "V", code[p + 1], p + 2, 1; R, v, pp = (~p1 >> 7) & 1, (~p1 >> 3) & 15, p1 & 3
        elif b == 0xC4:
            kind, (p1, p2), p = "V", code[p + 1:p + 3], p + 3
            R, X, B, m, W, v, pp = (~p1 >> 7) & 1, (~p1 >> 6) & 1, (~p1 >> 5) & 1, p1 & 31, p2 >> 7, (~p2 >> 3) & 15, p2 & 3
        else:
            kind = "L"
            if b in (0x66, 0xF3): pp, p = b, p + 1; b = code[p]
            if 0x40 <= b <= 0x4F: W, R, X, B, p = (b >> 3) & 1, (b >> 2) & 1, (b >> 1) & 1, b & 1, p + 1; b = code[p]
            if b == 0x0F:
                m, p = 1, p + 1
                if code[p] in (0x38, 0x3A): m, p = (2 if code[p] == 0x38 else 3), p + 1
        opcode, p = code[p], p + 1
    except (IndexError, ValueError): return found
    for way in INDEX.get((kind, pp, m, opcode), ()):
        try:
            q, f = p, {"vvvv": v, "k": k, "r": opcode & 7 | B << 3}
            if way.modrm:
                x, q = code[q], q + 1
                mod, low = x >> 6, x & 7
                f["reg"] = (x >> 3) & 7 | R << 3 | R2 << 4
                if mod == 3: f["rm"] = low | B << 3 | (X << 4 if kind == "E" else 0)
                elif mod == 0 and low == 5: f["field"], q = bytes(code[q:q + 4]), q + 4
                else:
                    if low == 4:
                        s, q = code[q], q + 1
                        low = s & 7
                        if (s >> 3) & 7 | X << 3 != 4: f["index"] = (s >> 3) & 7 | X << 3
                    f["base"] = low | B << 3
                    size = (0, 1, 4)[mod]
                    f["disp"] = (sx(int.from_bytes(code[q:q + size], "little"), 8 * size) * (way.scale8 if mod == 1 else 1) if size else 0) & M64
                    q += size
            if way.imm:
                size = 4 if way.imm in ("id", "sd", "rel32") else 1
                n, q = int.from_bytes(code[q:q + size], "little"), q + size
                if way.imm in ("sb", "sd", "rel8", "rel32"): n = sx(n, 8 * size)
                if way.late: f["field"] = bytes(code[q - 4:q])
                elif way.imm in ("rel8", "rel32"): f["rel"] = addr + (q - at) + n
                else: f["imm"] = n & M64
            if q > len(code) or way.rip and "field" not in f: continue
            bind = dict(way.fixed)
            for name, places in way.fields.items():
                for h in places:
                    if isinstance(h, str) and bind.setdefault(h, f[name]) != f[name]: raise KeyError(h)     # one placeholder, two things: not this way
            if "field" in f: bind["field"] = f["field"]
            found.append((way, bind, q - at))
        except (KeyError, IndexError): continue
    return sorted(found, key=lambda c: ORDER[id(c[0])])


def decode(code, at, addr, late):
    """(the length, the decoded row) of the instruction at `at` of `code`, which is at address `addr`; None if it
    is no instance of a row as the table writes one. `late(kind, field, end)`: what the file says of four
    bytes that stand for a place in its data or a function (the texts of the placeholders there)."""
    for way, bind, n in candidates(code, at, addr):
        if n > 15: continue                 # (a processor refuses an instruction of more than fifteen bytes; nothing the table writes is so long)
        try:
            if encode.encode(way, bind, addr) != bytes(code[at:at + n]): continue
        except encode.Refuse: continue
        if way.late: bind.update(zip(way.late[1], late(way.late[0], at + n - 4, at + n)))
        text = way.fill(bind)
        if table.find(HEADS, table.parse_row(text))[0] is not way.row: continue
        return n, text
    return None
