#!/usr/bin/env python3
"""obj: a function of an AArch64 object file, read as instances of the rows of arm64.tab.

    python3 obj.py OBJECT SYMBOL        lists the function's instructions

`read` gives the instructions of the function SYMBOL, one for every four bytes from the symbol's address
to its end (its size in the file's table of names): where each stands, counted from the function's start,
and the decoded instruction as the table's ROW column writes it (word.py). A call is written with the
name of the function called, which the file's relocation at that word gives. Anything this does not know
is refused with the reason (`Stop`): a file that is no AArch64 object file, a word that is no instance of
a row, a relocation that is no call, a call with no relocation."""
import os, struct, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path[:0] = [HERE, os.path.join(HERE, "..", "core")]
import table, word

EM_AARCH64, ET_REL = 183, 1
SHT_PROGBITS, SHT_SYMTAB, SHT_RELA, SHF_EXECINSTR = 1, 2, 4, 4
R_AARCH64_CALL26 = 283
MACHINES = {62: "x86-64", EM_AARCH64: "arm64"}


class Stop(Exception):
    """The file or the function is not one this reads."""


def machine(path):
    """What machine an ELF file is for: "x86-64", "arm64", or None."""
    with open(path, "rb") as f: head = f.read(20)
    if len(head) < 20 or head[:4] != b"\x7fELF": return None
    return MACHINES.get(struct.unpack_from("<H", head, 18)[0])


class Elf:
    def __init__(self, path):
        with open(path, "rb") as f: self.b = b = f.read()
        if b[:4] != b"\x7fELF" or b[4] != 2 or b[5] != 1: raise Stop("not a 64-bit ELF file with the lowest byte first")
        kind, mach = struct.unpack_from("<HH", b, 16)
        if mach != EM_AARCH64: raise Stop("not a file for AArch64")
        if kind != ET_REL: raise Stop("not an object file (one that is still to be linked)")
        shoff, = struct.unpack_from("<Q", b, 40)
        size, count, names = struct.unpack_from("<HHH", b, 58)
        if size != 64: raise Stop("section headers of a size this does not read")
        self.sections = [struct.unpack_from("<IIQQQQIIQQ", b, shoff + i * size) for i in range(count)]
        self.names = self.sections[names]

    def text(self, table_section, at):
        start = table_section[4] + at
        end = self.b.index(b"\0", start)
        return self.b[start:end].decode("ascii", "replace")

    def symbols(self):
        """[(name, bind, kind, section, value, size)] of the file's table of names, and the table's number among the sections."""
        for n, s in enumerate(self.sections):
            if s[1] == SHT_SYMTAB:
                strings = self.sections[s[6]]
                out = []
                for k in range(s[5] // 24):
                    name, info, _, shndx, value, size = struct.unpack_from("<IBBHQQ", self.b, s[4] + 24 * k)
                    out.append((self.text(strings, name), info >> 4, info & 15, shndx, value, size))
                return out, n
        raise Stop("no table of names")

    def relocations(self, section, symtab):
        """{where in the section: (kind, the symbol's number, the number added)} of the relocations of that section."""
        out = {}
        for s in self.sections:
            if s[1] == SHT_RELA and s[7] == section:
                if s[6] != symtab: raise Stop("relocations by another table of names")
                for k in range(s[5] // 24):
                    at, info, add = struct.unpack_from("<QQq", self.b, s[4] + 24 * k)
                    if at in out: raise Stop(f"two relocations at {at:#x}")
                    out[at] = (info & 0xFFFFFFFF, info >> 32, add)
        return out


def place(e, symbol):
    """Where the function `symbol` lies: (its section's number, its address in the section, its size, where
    its first byte is in the file)."""
    symbols, _ = e.symbols()
    found = [s for s in symbols if s[0] == symbol and s[3] not in (0, 0xFFF1, 0xFFF2)]
    if len(found) != 1: raise Stop(f"{symbol}: {len(found)} definitions in the file")
    _, _, _, shndx, value, size = found[0]
    if shndx >= len(e.sections): raise Stop(f"{symbol}: in no section of the file")
    sec = e.sections[shndx]
    if sec[1] != SHT_PROGBITS or not sec[2] & SHF_EXECINSTR: raise Stop(f"{symbol}: not in a section of code")
    if size == 0 or size % 4 or value % 4 or value + size > sec[5]: raise Stop(f"{symbol}: its size in the file ({size}) is not that of whole instructions within its section")
    return shndx, value, size, sec[4] + value


def words(obj, symbol):
    """The function's instruction words, each four bytes, and where the first is in the file."""
    e = Elf(obj)
    _, _, size, at = place(e, symbol)
    return [e.b[at + k:at + k + 4] for k in range(0, size, 4)], at


def read(obj, symbol, tab=None):
    """[(where, where + 4, the decoded instruction's text)] of the function `symbol` of the object file."""
    e = Elf(obj)
    symbols, symtab = e.symbols()
    shndx, value, size, at = place(e, symbol)
    code = e.b[at:at + size]
    relocs = e.relocations(shndx, symtab)
    ways = word.ways(table.read(tab or word.TABLE))
    rows = []
    for at in range(0, size, 4):
        w = code[at:at + 4]
        got = word.decode(ways, w)
        if got is None: raise Stop(f"{symbol}+{at:#x}: {int.from_bytes(w, 'little'):08x} is no instance of a row of the table")
        row, bind = got
        way = next(x for x in ways if x.row is row and word.encode(x, bind) == w)
        rel = relocs.pop(value + at, None)
        if way.late is not None:
            # a call: the word names no place (its field is zero), and the relocation names the function called
            _, placeholder = way.late
            if rel is None: raise Stop(f"{symbol}+{at:#x}: a call that no relocation gives a function for")
            kind, number, add = rel
            if kind != R_AARCH64_CALL26 or add != 0 or bind[placeholder] != 0: raise Stop(f"{symbol}+{at:#x}: a relocation that is no plain call of a function")
            name, sbind, skind, _, _, _ = symbols[number]
            if not name or sbind not in (1, 2) or skind not in (0, 2): raise Stop(f"{symbol}+{at:#x}: a call of what is no named function")
            bind = dict(bind); bind[placeholder] = name
        elif rel is not None: raise Stop(f"{symbol}+{at:#x}: a relocation at an instruction that is no call")
        rows.append((at, at + 4, word.written(row, bind)))
    if any(value <= at < value + size for at in relocs): raise Stop(f"{symbol}: a relocation that is not at an instruction's first byte")
    return rows


def called(obj, symbol, tab=None):
    """The functions `symbol` calls, by name, in the order of their first call."""
    out = []
    for _, _, text in read(obj, symbol, tab):
        parts = text.split()
        if parts[0] == ".bl" and parts[1] not in out: out.append(parts[1])
    return out


if __name__ == "__main__":
    if len(sys.argv) != 3: raise SystemExit(__doc__)
    try:
        for a, b, text in read(sys.argv[1], sys.argv[2]): print(f"{a:6} {b:6} {text}")
    except Stop as why: raise SystemExit(f"obj: {why}")
