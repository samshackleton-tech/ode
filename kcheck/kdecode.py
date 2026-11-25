#!/usr/bin/env python3
"""kdecode: a function's instructions read from a file's bytes, with no disassembler.

    python3 kdecode.py OBJECT SYMBOL BASE RODATA OUT        writes OUT.rows and OUT.data, as lift_one.py does
    python3 kdecode.py --compare OBJECT SYMBOL BASE RODATA LIFTED.rows LIFTED.data

This reads the ELF file itself: the section headers, the names, the relocations, the bytes. What instruction
the bytes at a place are is not decided here: the table of instructions says how each instance of each of
its rows is written in bytes, and bytes are read as an instance only if the table writes those very bytes
for it (../core/decode.py, ../core/encode.py, ../core/x86.tab); bytes it does not write stop the reading.
`--compare` says whether the rows read are a disassembler's (lift_one.py), instruction for instruction: two
readings of the same bytes, made apart.

Decoding starts at SYMBOL and goes on, instruction after instruction, to the first `ret` (so a second entry
that falls into the same body, as P32 into K32, is read with it). The object's read-only data is placed at
RODATA, as the lifter places it. `lea reg, [rip + data]` is the row `.lea_data reg WHERE` (the lifter writes
it as a move of the number RODATA + WHERE: `--compare` reads the one as the other; the verifiers must not,
for a true move of that number is no address).

Two kinds of file. An object whose code has relocations (an assembler's output): an operand's or a call's
target is what its relocation names. A file whose addresses are settled (`settled` below: an object with no
relocation left for its code, a shared object, an executable): the target is where the instruction's own
bytes say; the bytes read are those a loader maps without leave to write, whole pages of the file, and they
are the read-only data too."""
import os, struct, sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "core"))
import decode as table_decode

G = "rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15".split()


class Stop(Exception):
    pass


def bv(n): return f"0x{n & ((1 << 64) - 1):X}"
def sx(n, bits): return n - (1 << bits) if n >> (bits - 1) else n


class Elf:
    def __init__(self, path):
        if isinstance(path, (bytes, bytearray)): self.b = bytes(path)
        else:
            with open(path, "rb") as f: self.b = f.read()
        b = self.b
        if b[:4] != b"\x7fELF" or b[4] != 2 or b[5] != 1 or struct.unpack_from("<H", b, 18)[0] != 62: raise Stop("not a little-endian x86-64 ELF object")
        self.type, = struct.unpack_from("<H", b, 16)            # 1: an object to be linked; 2: an executable; 3: a shared object
        shoff, = struct.unpack_from("<Q", b, 40); shentsize, shnum, shstrndx = struct.unpack_from("<HHH", b, 58)
        # the file is its maker's: every table it points at must lie within it, or the reading stops. (Until
        # November 17, 2026 a section that named bytes past the file's end, or a name that ran past its table,
        # was read as whatever the slices happened to give: a maker could choose what the reader saw.)
        if shnum and (shentsize < 64 or shoff + shentsize * shnum > len(b)): raise Stop("a table of sections outside the file")
        if not 0 <= shstrndx < shnum: raise Stop("no table of the sections' names")
        self.sections = []
        for i in range(shnum):
            name, typ, flags, addr, off, size, link, info, align, entsize = struct.unpack_from("IIQQQQIIQQ", b, shoff + i * shentsize)
            if off + size > len(b) or (typ in (2, 11, 4) and entsize not in (0, 24)): raise Stop(f"its section {i} lies outside the file, or holds other than whole entries")
            self.sections.append(dict(name=name, type=typ, off=off, size=size, link=link, info=info, align=align, flags=flags))
        names = self.sections[shstrndx]
        def cstr(sec, at):
            end = b.find(b"\0", sec["off"] + at, sec["off"] + sec["size"])
            if at < 0 or at >= sec["size"] or end < 0: raise Stop("a name outside the table of names")
            return b[sec["off"] + at:end].decode()
        for s in self.sections: s["name"] = cstr(names, s["name"])
        self.symbols = []
        for symtab in [s for s in self.sections if s["type"] in ((2,) if self.type == 1 else (2, 11))]:    # .symtab; in a linked file .dynsym too
            if not 0 <= symtab["link"] < len(self.sections): raise Stop("a table of names that is not one")
            strtab = self.sections[symtab["link"]]
            for i in range(symtab["size"] // 24):
                name, info, other, shndx, value, size = struct.unpack_from("<IBBHQQ", b, symtab["off"] + 24 * i)
                self.symbols.append(dict(name=cstr(strtab, name), type=info & 15, bind=info >> 4, shndx=shndx, value=value, other=other & 3, size=size))
        self.index = {s["name"]: i for i, s in enumerate(self.sections)}
        phoff, = struct.unpack_from("<Q", b, 32); phentsize, phnum = struct.unpack_from("<HH", b, 54)
        self.segments = []
        if phnum and (phentsize < 56 or phoff + phentsize * phnum > len(b)): raise Stop("a table of segments outside the file")
        for i in range(phnum if self.type != 1 else 0):
            typ, flags, off, vaddr, paddr, filesz, memsz, align = struct.unpack_from("IIQQQQQQ", b, phoff + i * phentsize)
            if off + filesz > len(b): raise Stop("a segment outside the file")
            self.segments.append(dict(type=typ, flags=flags, off=off, vaddr=vaddr, filesz=filesz, memsz=memsz, align=align))
    def bytes_of(self, name):
        if name not in self.index: return b""                 # an object with no read-only data
        s = self.sections[self.index[name]]
        return self.b[s["off"]:s["off"] + s["size"]]

    def relocations(self, name):
        """offset in the section -> (section the target is in, offset there before the instruction's own length is counted)"""
        out = {}
        for s in self.sections:
            if s["type"] == 4 and s["info"] == self.index[name]:
                for i in range(s["size"] // 24):
                    off, info, addend = struct.unpack_from("<QQq", self.b, s["off"] + 24 * i)
                    sym = self.symbols[info >> 32]
                    kind = info & 0xFFFFFFFF
                    if kind == 4 or kind == 2 and sym["shndx"] == 0:        # R_X86_64_PLT32, or PC32 to a name from elsewhere: a call
                        out[off] = ("call", sym["name"])
                    elif kind == 2: out[off] = (self.sections[sym["shndx"]]["name"], sym["value"] + addend)      # R_X86_64_PC32
                    else: raise Stop(f"a relocation of type {kind}")
        return out


PAGE = 4096
GIVEN = {}          # names a proof gives to addresses of a file whose own names are gone (check_binary.py): {name: address}


class Named:
    """An object whose code has relocations: an operand's or a call's target is what its relocation names.
    `align`: the boundary the read-only data starts on, wherever a linker puts it."""
    def __init__(self, e):
        self.table = e.relocations(".text")
        self.align = e.sections[e.index[".rodata"]]["align"] if ".rodata" in e.index else 1

    def data(self, code, field, end):
        if field not in self.table: raise Stop("a RIP-relative operand with no relocation")
        sec, off = self.table[field]
        if sec != ".rodata": raise Stop(f"an operand in {sec}")
        return off + (end - field)

    def callee(self, code, field, end):
        if self.table.get(field, ("", ""))[0] != "call": raise Stop("a call with no function named")
        return self.table[field][1]


class Settled:
    """A file whose addresses are settled. `image`: the bytes a loader maps without leave to write, from the
    lowest such address `lo` (for an object: its .text); `parts`: (from, to, executable) within the image;
    `names`: the functions' names by where they start; `align`: the boundary the image starts on."""
    def __init__(self, e):
        if e.type == 1:
            if ".text" not in e.index: raise Stop("an object with no .text")
            text = e.bytes_of(".text")
            self.image, self.lo, self.parts, self.align = text, 0, [(0, len(text), True)], e.sections[e.index[".text"]]["align"]
            inside = lambda s: s["shndx"] == e.index[".text"]
        else:
            spans = []
            for s in e.segments:
                if s["type"] == 2:                               # PT_DYNAMIC: does the file ask the loader to change its code?
                    for i in range(s["filesz"] // 16):
                        tag, val = struct.unpack_from("<QQ", e.b, s["off"] + 16 * i)
                        if tag == 0: break
                        if tag == 22 or tag == 30 and val & 4: raise Stop("the file asks the loader to write into its code (TEXTREL)")
                if s["type"] != 1: continue                      # PT_LOAD: what is mapped, in whole pages
                if (s["vaddr"] - s["off"]) % PAGE: raise Stop("a part of the file is not where its page in memory is")
                spans.append((s["vaddr"] // PAGE * PAGE, -(-(s["vaddr"] + s["memsz"]) // PAGE) * PAGE, s))
            for i, (a, z, s) in enumerate(spans):
                if any(a < z2 and a2 < z for a2, z2, _ in spans[i + 1:]): raise Stop("two parts of the file are loaded on one page")
            keep = sorted(((a, z, s) for a, z, s in spans if not s["flags"] & 2), key=lambda x: x[0])      # without leave to write
            if not keep: raise Stop("nothing in the file is loaded read-only")
            if any(z != a2 for (_, z, _), (a2, _, _) in zip(keep, keep[1:])): raise Stop("the parts loaded read-only do not lie side by side")
            self.lo, image, self.parts, self.align = keep[0][0], bytearray(), [], PAGE
            for a, z, s in keep:
                if s["memsz"] != s["filesz"]: raise Stop("a read-only part that is longer in memory than in the file")
                first = s["off"] - (s["vaddr"] - a)
                piece = e.b[first:first + z - a]                 # whole pages of the file, as a loader maps them; past the file's end, zeros
                image += piece + bytes(z - a - len(piece))
                self.parts.append((a - self.lo, z - self.lo, bool(s["flags"] & 1)))
            self.image = bytes(image)
            inside = lambda s: 0 < s["shndx"] < 0xFF00 and self.lo <= s["value"] < self.lo + len(self.image)      # in a section: a loader moves it with the file
        # Names: of functions, and of labels an assembler gave no type. A name the file gives to two places
        # (as an object's own names may be, once several objects are linked) is no name here.
        places = {}
        for s in e.symbols:
            if s["name"] and s["type"] in (0, 2) and inside(s): places.setdefault(s["name"], set()).add(s["value"] - self.lo)
        for name, value in GIVEN.items(): places.setdefault(name, set()).add(value - self.lo)        # names a proof gives: as the file's own
        self.at = {name: min(where) for name, where in places.items() if len(where) == 1}
        self.sizes = {s["name"]: s["size"] for s in e.symbols if s["name"] and s["type"] == 2 and inside(s) and s["size"]}
        self.names = {}
        for name, v in self.at.items(): self.names.setdefault(v, []).append(name)

    def runs(self, a, z):
        return any(x and lo <= a and z <= hi for lo, hi, x in self.parts)

    def target(self, code, field, end):
        return end + sx(int.from_bytes(code[field:field + 4], "little"), 32)

    def data(self, code, field, end):
        t = self.target(code, field, end)
        if not any(lo <= t and t + 64 <= hi for lo, hi, _ in self.parts): raise Stop("an operand that is not in what is loaded read-only")
        return t

    def callee(self, code, field, end):
        t = self.target(code, field, end)
        if t not in self.names: raise Stop("a call to what is no function's start")
        return sorted(self.names[t], key=lambda n: (n.startswith("_"), n))[0]


def settled(e):
    """The file's addresses are settled: no relocation is left for its code."""
    return e.type != 1 or not any(s["type"] in (4, 9) and s["info"] == e.index.get(".text") for s in e.sections)


KNOWN = {".text": (1, 0x6), ".note.GNU-stack": (1, 0), ".symtab": (2, 0), ".strtab": (3, 0), ".shstrtab": (3, 0), ".ode.proof": (1, 0)}      # a section's name: (its type, its leave)


def linkable(e):
    """For an object that is to be linked (a file of type 1): (why it is not read, {}), or (None, {name: its
    place in .text}) with every name the file gives a linker.

    A linker takes more from an object than the bytes of `.text` read here: other sections it loads to be
    run, whatever they are called; names it resolves by rules of its own (a LOCAL name goes to no caller, a
    WEAK one may give way to another file's, an IFUNC is resolved when the program starts); a stack it is
    asked to make executable. Until November 16, 2026 a copy of the shipped odeframe.o whose `ode_unframe` was
    made LOCAL, with another function under the GLOBAL name in a second executable section, was verified as
    the shipped file is, and a program linked with it ran the other function. So an object is read only in
    the one shape the makers here write (klink.py, programs/kpack.py), with its names or stripped of them:
    the sections of KNOWN and no others, each once, of that type and with that leave (and the one that says the stack is not to be run, there); and no name but GLOBAL
    names of functions in `.text`, each once. A driver then asks that each such name be verified."""
    seen = set()
    for i, s in enumerate(e.sections):
        if i == 0 and s["type"] == 0 and s["size"] == 0: continue
        name = s["name"]
        if name not in KNOWN or name in seen:
            return f"it has a section this reader does not read ({name!r}{', a second time' if name in seen else ''}), and a linker would take that too", {}
        seen.add(name)
        if (s["type"], s["flags"]) != KNOWN[name]:
            return f"its section {name} is not of the kind, or has not the leave, this reader takes it to have (type {s['type']}, flags {s['flags']:#x})", {}
    if ".note.GNU-stack" not in seen: return "it has no section .note.GNU-stack, and a linker takes that as asking for a stack that can be run", {}
    names, text = {}, e.index.get(".text")
    for k, sym in enumerate(e.symbols):
        if k == 0 and not sym["name"] and sym["shndx"] == 0: continue
        if not (sym["type"] in (0, 2) and sym["bind"] == 1 and sym["other"] == 0 and sym["shndx"] == text and sym["name"]) or sym["name"] in names:
            return (f"it has a name of a kind this reader does not read ({sym['name']!r}: type {sym['type']}, binding {sym['bind']}, visibility {sym['other']}, "
                    f"section {sym['shndx']}{', given twice' if sym['name'] in names else ''}), and a linker reads names by rules of its own"), {}
        names[sym["name"]] = sym["value"]
    return None, names


def decode(code, at, relocs, rodata, rodata_at, base, start, sym_size=0):
    """One instruction at `at`: (its length, its text as the table's ROW writes it), by the table of instructions
    (../core/decode.py: bytes are read as an instance of a row only if the table writes those very bytes for it).
    What the table leaves to the file is answered here: four bytes that stand for a place in the file's
    read-only data, or for a function called."""
    def late(kind, field, end):
        if kind == "call": return (relocs.callee(code, field, end),)
        off = relocs.data(code, field, end)
        size = {"data": 0, "data4": 16, "data1": 4, "data16": 64}[kind]
        if not 0 <= off <= len(rodata) - size: raise Stop("an operand that is not within the file's read-only data")
        # MOVAPS faults where the sixteen bytes do not start on a 16-byte boundary
        if kind == "data4" and (off % 16 or relocs.align % 16): raise Stop("sixteen bytes read as aligned from where they need not be on a 16-byte boundary")
        if kind == "data": return (bv(off),)
        if kind == "data4": return tuple(f"0x{int.from_bytes(rodata[off + 4 * i:off + 4 * i + 4], 'little'):X}" for i in range(4))
        return ("0x" + "".join(f"{x:02X}" for x in reversed(rodata[off:off + size])) + ("#512" if kind == "data16" else ""),)
    got = table_decode.decode(code, at, base + at - start, late)
    if got is None: raise Stop(f"an instruction this verifier does not know: {bytes(code[at:at + 6]).hex()}")
    n, text = got
    if n == 5 and code[at] == 0xE9 and text.startswith(".jmp "):
        if isinstance(relocs, Named) and (at + 1) in relocs.table:
            kind, target_name = relocs.table[at + 1]
            if kind != "call": raise Stop("a jump with a relocation that names no function")
            if code[at + 1:at + 5] != b"\x00\x00\x00\x00": raise Stop("a tail jump with a nonzero displacement beside its relocation")
            return 5, f".jmp {target_name}"
        if isinstance(relocs, Settled):
            tgt = relocs.target(code, at + 1, at + 5)
            if sym_size and not (start <= tgt < start + sym_size) and tgt in relocs.names:
                return 5, f".jmp {relocs.callee(code, at + 1, at + 5)}"
    return got


def place(e, symbol):
    """(the bytes the code is in, where `symbol` starts in them, the relocations or the settled file, the read-only data)"""
    if settled(e):
        s = Settled(e)
        if symbol not in s.at or not s.runs(s.at[symbol], s.at[symbol] + 1): raise Stop(f"no {symbol} in the file's code")
        return s.image, s.at[symbol], s, s.image
    sym = next((s for s in e.symbols if s["name"] == symbol and e.sections[s["shndx"]]["name"] == ".text"), None)
    if sym is None: raise Stop(f"no {symbol} in the object's .text")
    return e.bytes_of(".text"), sym["value"], Named(e), e.bytes_of(".rodata")


def address(obj, symbol):
    return place(Elf(obj), symbol)[1]


def boundary(obj, symbol):
    """The boundary the file's read-only data (as `read` gives it) starts on, wherever a linker and a loader put it."""
    return place(Elf(obj), symbol)[2].align


def read(obj, symbol, base, rodata_at):
    text, start, relocs, rodata = place(Elf(obj), symbol)
    sym_size = relocs.sizes.get(symbol, 0) if isinstance(relocs, Settled) else 0
    at = start
    rows = []
    farthest = base
    while True:
        n, ins = decode(text, at, relocs, rodata, rodata_at, base, start, sym_size=sym_size)
        if isinstance(relocs, Settled) and not relocs.runs(at, at + n): raise Stop("the code runs out of what is loaded to be run")
        pc = base + at - start
        nxt = pc + n
        rows.append((pc, nxt, ins))
        parts = ins.split()
        if len(parts) == 2 and parts[0] in (".jmp", ".je", ".jne", ".jae", ".jb", ".ja", ".jbe") and parts[1].startswith("0x"):
            tgt = int(parts[1], 16)
            if tgt > farthest: farthest = tgt
        at += n
        is_tail = len(parts) == 2 and parts[0] == ".jmp" and not parts[1].startswith("0x")
        if (ins == ".ret" or is_tail) and nxt > farthest: break
        if at >= len(text): raise Stop("the code runs off the section")
    return rows, rodata


def features(obj, symbol):
    """What kinds of instruction the function at `symbol` holds, by how each is encoded: "avx512" (an EVEX
    prefix), "avx" (a VEX prefix), "sse41" (the 0F 38 and 0F 3A maps of the older encoding: SSSE3 and
    SSE4.1). The rest are the instructions every x86-64 processor has."""
    text, start, _, _ = place(Elf(obj), symbol)
    rows, _ = read(obj, symbol, 0, 0)
    out = set()
    for at, _, _ in rows:
        p = start + at
        while text[p] in (0x66, 0xF2, 0xF3): p += 1
        if text[p] == 0x62: out.add("avx512")
        elif text[p] in (0xC4, 0xC5): out.add("avx")
        else:
            if 0x40 <= text[p] <= 0x4F: p += 1
            if text[p] == 0x0F and text[p + 1] in (0x38, 0x3A): out.add("sse41")
    return out


def main():
    a = sys.argv[1:]
    compare = a and a[0] == "--compare"
    if compare: a = a[1:]
    obj, symbol, base, rodata_at = a[0], a[1], int(a[2], 16), int(a[3], 16)
    rows, rodata = read(obj, symbol, base, rodata_at)
    if compare:
        with open(a[4]) as f: theirs = [tuple(l.rstrip("\n").split("\t")) for l in f]
        lifters = lambda i: f".mov 64 (.reg {i.split()[1]}) (.imm {bv(rodata_at + int(i.split()[2], 16))})" if i.startswith(".lea_data ") else i
        ours = [(f"{x:X}", f"{y:X}", lifters(i)) for x, y, i in rows]
        with open(a[5]) as f: data = f.read().split()
        same_data = data == [f"{rodata_at:X}", rodata.hex().upper()]
        diff = [(o, t) for o, t in zip(ours, theirs) if o != t]
        print(f"{symbol}: {len(ours)} instructions decoded from the bytes, the lifter read {len(theirs)}: " + ("the same, every one" if not diff and len(ours) == len(theirs) else f"{len(diff)} DIFFER")
              + "; the read-only data " + ("the same" if same_data else "DIFFERS"))
        for o, t in diff[:8]: print("  ours  ", o, "\n  theirs", t)
        return 0 if not diff and len(ours) == len(theirs) and same_data else 1
    with open(a[4] + ".rows", "w") as f: f.write("".join(f"{x:X}\t{y:X}\t{i}\n" for x, y, i in rows))
    with open(a[4] + ".data", "w") as f: f.write(f"{rodata_at:X}\t{rodata.hex().upper()}\n")
    print(len(rows), "instructions")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Stop as e:
        print(f"kdecode: stopped: {e}"); sys.exit(1)
