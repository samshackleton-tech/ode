#!/usr/bin/env python3
"""encode: how an instance of a row is written in bytes, by the table.

    python3 encode.py           lists the ways, a row at a time

Under a row of x86.tab are the ways its instances are written, one a line: `= ENCODING ; OPERANDS` (the
notation is at the head of x86.tab). `encode` gives the bytes of an instance in one of the row's ways: for
each way and each instance one byte string, or none (`Refuse`) where that way cannot write it.

The reader of a file's code (decode.py) takes bytes for an instance of a row only if `encode` writes those
very bytes for it. So what it accepts is what is written here and nothing else: no prefix, no bit and no
form is read that this does not write, and what must be right is this file and the table's lines, each of
which is run on processors with numbers (cross.py) as it is written here."""
import os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import table

G = "rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15".split()
M64, M32 = table.M64, table.M32
GENERAL, VECTOR, MASK = "DSBPbs", "XYZ", "M"                      # what kind of register a placeholder is
NUMBER = {"ib": (1, False), "cb": (1, False), "sb": (1, True), "id": (4, False), "sd": (4, True)}     # bytes; taken sign-extended to 64 bits?
LATE = ("data", "data4", "data1", "data16", "call")              # four bytes that the file's relocations (or its settled addresses) speak for


class Refuse(Exception):
    """This way does not write this instance."""


def signed(n, bits=64): return n - (1 << bits) if n >> (bits - 1) else n
def hexbyte(t): return re.fullmatch(r"[0-9A-F]{2}", t) is not None


class Way:
    """One `=` line under a row: an encoding and where the row's placeholders are in it."""
    def __init__(self, row, text):
        self.row, self.text = row, text
        enc, _, ops = text.partition(";")
        t = enc.split()
        self.literal = bytes(int(x, 16) for x in t) if all(hexbyte(x) for x in t) and not ops.strip() else None
        self.kind, self.pp, self.W, self.map, self.L = "L", 0, 0, 0, 0
        self.opcode, self.plus, self.modrm, self.digit, self.imm, self.scale8 = None, False, False, None, None, 1
        self.fields, self.fixed, self.late, self.below, self.byte8, self.rip = {}, {}, None, None, None, False
        if self.literal is not None: return
        i = 0
        if t[0].startswith(("VEX.", "EVEX.")):
            self.kind = t[0][0]
            for part in t[0].split(".")[1:]:
                if part in ("128", "512"): self.L = 0 if part == "128" else 2
                elif part in ("66", "F3"): self.pp = 1 if part == "66" else 2
                elif part in ("0F", "0F38", "0F3A"): self.map = ("0F", "0F38", "0F3A").index(part) + 1
                elif part in ("W0", "W1"): self.W = int(part[1])
                else: raise ValueError(f"cannot read {part} in {text}")
            i = 1
        else:
            if t[i] in ("66", "F3"): self.pp = int(t[i], 16); i += 1
            if t[i] == "REX.W": self.W = 1; i += 1
            if t[i] == "0F":
                self.map, i = 1, i + 1
                if t[i] in ("38", "3A") and i + 1 < len(t) and hexbyte(t[i + 1][:2]): self.map, i = (2 if t[i] == "38" else 3), i + 1
        self.opcode, self.plus = int(t[i][:2], 16), t[i].endswith("+r"); i += 1
        if i < len(t) and t[i].startswith("/"):
            self.modrm, self.digit = True, None if t[i] == "/r" else int(t[i][1:]); i += 1
        if i < len(t) and t[i] in (*NUMBER, "rel8", "rel32"): self.imm = t[i]; i += 1
        if i < len(t) and t[i].startswith("d8*"): self.scale8 = int(t[i][3:]); i += 1
        if i != len(t): raise ValueError(f"cannot read {t[i]} in {text}")
        value = lambda x: G.index(x) if x in G else int(x) if x.isdigit() else x       # a placeholder, or the register or the number it always is
        for tok in ops.split():
            lhs, _, rhs = tok.partition("=")
            if lhs == "mem":
                parts = rhs.split("+")
                self.fields["base"], self.fields["disp"] = (parts[0],), (parts[-1],)
                if len(parts) == 3: self.fields["index"] = (parts[1],)
            elif lhs in LATE: self.late = (lhs, tuple(rhs.split(",")))
            elif lhs in ("reg", "reg8", "rm", "rm8", "r", "vvvv", "k", "imm", "rel"):
                if lhs == "rm8": self.byte8, lhs = "rm", "rm"
                elif lhs == "reg8": self.byte8, lhs = "reg", "reg"
                if "<" in rhs: rhs, _, n = rhs.partition("<"); self.below = int(n)
                self.fields[lhs] = tuple(value(x) for x in rhs.split(","))
            elif len(lhs) == 1: self.fixed[lhs] = value(rhs)
            else: raise ValueError(f"cannot read {tok} in {text}")
        self.rip = self.late is not None and self.late[0] != "call"
        # how the decoded row writes a number: a count, a choice or a fixed number in decimal; where a jump goes in plain hex; the rest as 64 bits in hex
        self.decimal = {h for h in self.fields.get("imm", ()) if self.imm == "cb"} | {h for h, v in self.fixed.items() if h in table.NUMBERS}
        self.targets = set(self.fields.get("rel", ()))
        given = {h for hs in self.fields.values() for h in hs if isinstance(h, str)} | set(self.fixed) | set(self.late[1] if self.late else ())
        wanted = {x.lstrip(".") for x in re.findall(r"[^\s()]+", row.row)} & set(table.REGISTERS + table.VECTORS + table.NUMBERS + table.MASKS)
        if wanted - given: raise ValueError(f"{row.name}: `{text}` does not say where {sorted(wanted - given)} are")
        # every placeholder the way names must be in the bytes it writes: a field that `encode` would not write is refused here
        f, call = set(self.fields), self.late is not None and not self.rip
        ok = (self.modrm == bool({"reg", "rm", "base"} & f or self.digit is not None or self.rip)
              and not ("reg" in f and self.digit is not None) and not ("rm" in f and ("base" in f or self.rip)) and not ("base" in f and self.rip)
              and ("imm" in f) == (self.imm in NUMBER) and ("rel" in f or call) == (self.imm in ("rel8", "rel32")) and not ("rel" in f and call)
              and (not call or self.imm == "rel32" and not self.modrm) and ("r" in f) == self.plus and (self.below is None or "imm" in f)
              and ("vvvv" not in f or self.kind in "VE") and ("k" not in f or self.kind == "E") and (self.scale8 == 1 or self.kind == "E" and "base" in f))
        if not ok: raise ValueError(f"{row.name}: `{text}`: the operands are not all in the bytes this writes")

    def fill(self, bind):
        """The decoded row of this instance, as the table's ROW writes it."""
        def one(m):
            t = m.group(0)
            if t[:1] == "." and t[1:] in table.REGISTERS: return "." + G[bind[t[1:]]]
            if t in table.VECTORS or t in table.MASKS: return str(bind[t])
            if t not in table.NUMBERS: return t
            v = bind[t]
            return v if isinstance(v, str) else str(v) if t in self.decimal else f"0x{v:X}" if t in self.targets else f"0x{v & M64:X}"
        return re.sub(r"[^\s()]+", one, self.row.row)


def encode(way, bind, at=0):
    """The bytes of the instance of the way's row that `bind` says (registers and numbers, by placeholder), in
    this way; `at`: where the instruction is (a jump's bytes say how far it goes from its end)."""
    if way.literal is not None: return way.literal
    if any(bind.get(h) != v for h, v in way.fixed.items()): raise Refuse("a placeholder that this way writes only as one thing")
    def value(f):
        got = {bind[h] if isinstance(h, str) else h for h in way.fields[f]}
        if len(got) != 1: raise Refuse(f"{f}: one field, two things")
        return got.pop()
    def register(f):
        if f not in way.fields: return 0
        n, h = value(f), str(way.fields[f][0])
        top = 8 if h in MASK else (32 if way.kind == "E" else 16) if h in VECTOR else 16
        if not 0 <= n < top: raise Refuse(f"{f}: no such register in this encoding")
        return n
    reg = way.digit if way.digit is not None else register("reg")
    v, r, k = register("vvvv"), register("r"), register("k")
    if "k" in way.fields and k == 0: raise Refuse("no mask register")              # (k0 written there says: no mask)
    R, R2, X, B, tail, low_byte = (reg >> 3) & 1, reg >> 4, 0, r >> 3, b"", (way.byte8 == "reg" and 4 <= reg <= 7)
    if "base" in way.fields:                    # memory at base + displacement (+ index)
        base, disp, index = register("base"), signed(value("disp")), register("index") if "index" in way.fields else None
        if not -1 << 31 <= disp < 1 << 31: raise Refuse("a displacement of more than 32 bits")
        if index == 4: raise Refuse("the stack pointer as an index")
        if index is not None or base & 7 == 4: low, sib = 4, bytes([(4 if index is None else index & 7) << 3 | base & 7])
        else: low, sib = base & 7, b""
        if disp == 0 and base & 7 != 5: mod, d = 0, b""
        elif disp % way.scale8 == 0 and -128 <= disp // way.scale8 <= 127: mod, d = 1, bytes([disp // way.scale8 & 0xFF])
        else: mod, d = 2, (disp & M32).to_bytes(4, "little")
        X, B, tail = (index or 0) >> 3, base >> 3, bytes([mod << 6 | (reg & 7) << 3 | low]) + sib + d
    elif way.rip: tail = bytes([(reg & 7) << 3 | 5]) + bytes(bind["field"])        # in the file's data: four bytes the file speaks for
    elif way.modrm:
        rm = register("rm")
        if way.byte8 == "rm" and 4 <= rm <= 7: low_byte = True  # the low byte of rsp, rbp, rsi, rdi: named so only after a REX prefix (without one: ah, ch, dh, bh)
        X, B, tail = rm >> 4, (rm >> 3) & 1, bytes([0xC0 | (reg & 7) << 3 | rm & 7])
    opcode = bytes([way.opcode | (r & 7 if way.plus else 0)])
    if way.kind == "L":
        rex = way.W << 3 | R << 2 | X << 1 | B
        head = (bytes([way.pp]) if way.pp else b"") + (bytes([0x40 | rex]) if rex or low_byte else b"") + (b"", b"\x0f", b"\x0f\x38", b"\x0f\x3a")[way.map]
    elif way.kind == "V":
        last = (~v & 15) << 3 | way.L << 2 | way.pp
        if X == 0 and B == 0 and way.W == 0 and way.map == 1: head = bytes([0xC5, (R ^ 1) << 7 | last])
        else: head = bytes([0xC4, (R ^ 1) << 7 | (X ^ 1) << 6 | (B ^ 1) << 5 | way.map, way.W << 7 | last])
    else:
        head = bytes([0x62, (R ^ 1) << 7 | (X ^ 1) << 6 | (B ^ 1) << 5 | (R2 ^ 1) << 4 | way.map,
                      way.W << 7 | (~v & 15) << 3 | 4 | way.pp, way.L << 5 | ((v >> 4) ^ 1) << 3 | k])
    out = head + opcode + tail
    if way.imm in NUMBER:
        size, sign = NUMBER[way.imm]
        n = value("imm")
        if not 0 <= n <= M64 or way.below is not None and n >= way.below: raise Refuse("a number too large for this instruction")
        low, high = (-1 << 8 * size - 1, 1 << 8 * size - 1) if sign else (0, 1 << 8 * size)
        if not low <= (signed(n) if sign else n) < high: raise Refuse("a number these bytes do not hold")
        return out + (n & ((1 << 8 * size) - 1)).to_bytes(size, "little")
    if way.late and way.late[0] == "call": return out + bytes(bind["field"])
    if way.imm in ("rel8", "rel32"):
        size = 1 if way.imm == "rel8" else 4
        d = value("rel") - (at + len(out) + size)
        if not -1 << 8 * size - 1 <= d < 1 << 8 * size - 1: raise Refuse("a jump too far for this way")
        return out + (d & ((1 << 8 * size) - 1)).to_bytes(size, "little")
    return out


def ways(rows):
    """Every way of every row, in the table's order."""
    return [Way(row, text) for row in rows for text in row.bytes]


if __name__ == "__main__":
    for row in table.read():
        print(row.name)
        for text in row.bytes: Way(row, text); print("    " + text)
