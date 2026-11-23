#!/usr/bin/env python3
"""word: how an instance of a row of arm64.tab is written as an instruction word, and how a word is read.

    python3 word.py                 lists the ways, a row at a time
    python3 word.py WORD ...        reads each word (hexadecimal) as an instance: its row, its placeholders

Under a row of arm64.tab are the ways its instances are written, one a line: `= BITS ; NOTES` (the notation
is at the head of arm64.tab). `encode` gives the word of an instance in one of the row's ways, or none
(`Refuse`) where that way cannot write it. `decode` reads a word as an instance of the first row, in the
table's order, one of whose ways writes that very word for it. So what is read is what is written here
and nothing else, and what must be right is this file and the table's lines, each of which is run on
processors (cross.py) as it is written here."""
import os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "core"))
import table

TABLE = os.path.join(HERE, "arm64.tab")
GENERAL = [f"x{i}" for i in range(31)]                     # a general register's number (a field that holds 31 is no instance: see arm64.tab)
REGISTER, VECTOR = "DSPB", "XYZ"                           # what kind of register a field's letter is


class Refuse(Exception):
    """This way does not write this instance."""


class Way:
    """One `=` line under a row: the word's fixed bits, and where each of the row's placeholders is in it."""
    def __init__(self, row, text):
        self.row, self.text = row, text
        bits, _, notes = text.partition(";")
        pattern = "".join(bits.split())
        if len(pattern) != 32: raise ValueError(f"{row.name}: {len(pattern)} bits in `{text}`")
        self.mask = self.value = 0
        self.fields = {}                                        # a field's letter -> (its lowest bit, how many bits)
        for k, ch in enumerate(pattern):
            bit = 31 - k
            if ch in "01":
                self.mask |= 1 << bit; self.value |= int(ch) << bit
            elif ch.isalpha():
                low, width = self.fields.get(ch, (bit + 1, 0))
                if low != bit + 1: raise ValueError(f"{row.name}: the places of `{ch}` do not lie together in `{text}`")
                self.fields[ch] = (bit, width + 1)
            else: raise ValueError(f"{row.name}: `{ch}` in `{text}`")
        # a placeholder that is not a field itself: (the field it is worked out from, how)
        self.rules, self.late = {}, None
        for note in notes.split():
            m = re.fullmatch(r"([A-Z])=([a-z])\*(\d+)", note)
            if m: self.rules[m.group(1)] = (m.group(2), "times", int(m.group(3))); continue
            m = re.fullmatch(r"([A-Z])=(\d+)-([a-z])", note)
            if m: self.rules[m.group(1)] = (m.group(3), "from", int(m.group(2))); continue
            m = re.fullmatch(r"(call|pc)=([A-Z])", note)
            if m:
                self.late = (m.group(1), m.group(2))
                if m.group(1) == "pc":
                    self.rules[m.group(2)] = (m.group(2).lower(), "pc", 4)
                continue
            raise ValueError(f"{row.name}: the note `{note}` in `{text}`")
        for field, _, _ in self.rules.values():
            if field not in self.fields: raise ValueError(f"{row.name}: no field `{field}` in `{text}`")
        if any(ch.islower() and ch not in {f for f, _, _ in self.rules.values()} for ch in self.fields):
            raise ValueError(f"{row.name}: a field that no placeholder is worked out from, in `{text}`")


def field_of(way, name, bind):
    """The number that the field `name` of a way holds for an instance."""
    if name in bind:
        v = bind[name]
        if name in REGISTER:
            if v not in GENERAL: raise Refuse(f"{v} is no register x0 to x30")
            v = GENERAL.index(v)
        return v
    for placeholder, (field, how, k) in way.rules.items():
        if field == name:
            v = bind[placeholder]
            if how == "times":
                if v % k: raise Refuse(f"{v} is not a multiple of {k}")
                return v // k
            if how == "pc":
                if not isinstance(v, int) or v % k: raise Refuse(f"{v} is not a multiple of {k}")
                _, width = way.fields[field]
                q = v // k
                if not -(1 << (width - 1)) <= q < (1 << (width - 1)):
                    raise Refuse(f"{v} does not fit the signed {width}-bit word offset of {placeholder}")
                return q & ((1 << width) - 1)
            return k - v
    raise Refuse(f"nothing says what the field {name} holds")


def encode(way, bind):
    """The instruction word of the instance of way.row that `bind` says (placeholder -> a general register's
    name, a vector register's number, or a number), as four bytes, the lowest first."""
    word = way.value
    for name, (low, width) in way.fields.items():
        v = field_of(way, name, bind)
        if not isinstance(v, int) or not 0 <= v < (1 << width): raise Refuse(f"{v} does not fit the {width} bits of {name}")
        word |= v << low
    return word.to_bytes(4, "little")


def ways(rows):
    return [Way(row, text) for row in rows for text in row.bytes]


def decode(all_ways, word):
    """(the row, what its placeholders are) of the instance that the four bytes `word` are, or None: the first
    way, in the table's order, that writes those very bytes for an instance."""
    w = int.from_bytes(word, "little")
    for way in all_ways:
        if w & way.mask != way.value: continue
        bind = {}
        try:
            for name, (low, width) in way.fields.items():
                v = (w >> low) & ((1 << width) - 1)
                if name in REGISTER:
                    if v == 31: raise Refuse("31")
                    bind[name] = GENERAL[v]
                elif name.isupper(): bind[name] = v
                else:
                    placeholder, (_, how, k) = next((p, rule) for p, rule in way.rules.items() if rule[0] == name)
                    if how == "pc":
                        signed = v - (1 << width) if v >= (1 << (width - 1)) else v
                        bind[placeholder] = signed * k
                    else:
                        bind[placeholder] = v * k if how == "times" else k - v
            if encode(way, bind) != word: continue
        except Refuse: continue
        return way.row, bind
    return None


def written(row, bind):
    """The decoded instruction as the table's ROW column writes it: a register by its name, a number in
    hexadecimal, the function a call names by its name."""
    def one(t):
        if t.startswith(".") and t[1:] in bind: return "." + bind[t[1:]]
        if t in bind: return bind[t] if isinstance(bind[t], str) else str(bind[t]) if t in VECTOR else hex(bind[t])
        return t
    def text(p): return "(" + " ".join(text(x) for x in p) + ")" if isinstance(p, list) else one(p)
    return " ".join(text(p) for p in row.pattern)


if __name__ == "__main__":
    rows = table.read(TABLE)
    if len(sys.argv) > 1:
        all_ways = ways(rows)
        for arg in sys.argv[1:]:
            got = decode(all_ways, int(arg, 16).to_bytes(4, "little"))
            print(arg, "is no instance of a row" if got is None else f"{got[0].name}: {written(*got)}")
    else:
        for row in rows:
            for text in row.bytes:
                way = Way(row, text)
                print(f"{row.name:12} {way.value:08x} under {way.mask:08x}  " + " ".join(f"{n}:{low + width - 1}..{low}" for n, (low, width) in way.fields.items())
                      + ("  " + " ".join(f"{p}={'%s*%d' % (f, k) if how == 'times' else '%d-%s' % (k, f)}" for p, (f, how, k) in way.rules.items()) if way.rules else ""))
