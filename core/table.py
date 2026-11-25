#!/usr/bin/env python3
"""table: the table of instructions (x86.tab) read.

    python3 table.py            lists the rows

A row is NAME | ASM | ROW | EFFECT, and under it the ways its instances are written in bytes (see the head
of x86.tab). `read` gives the rows; `find` the row a decoded instruction is an instance of, with what its
placeholders are. An EFFECT is statements, run left to right, over primitives:

    PLACE = EXPRESSION          a register, a flag (zf, cf) or bytes of memory (mem8/mem32/mem64/mem128/mem512(base, displacement[, index]))
    jump TARGET [if [not] FLAG] the next instruction is at TARGET (if the flag says so)
    call TARGET                 a call of the function there; the address to come back to is put below the stack pointer
    call TARGET link REGISTER   a call of the function there; the address to come back to is put in the register
    return                      the function returns to the address at the stack pointer
    return REGISTER             the function returns to the address the register holds
    nothing

What a primitive means on numbers is in conc.py (compared with a processor by cross.py); what the
verifier answers it with on symbols is in step.py (compared with conc.py by meaning.py). The primitives
that only move lanes about are the same on both, and are here (MOVES)."""
import os, re

HERE = os.path.dirname(os.path.abspath(__file__))
M64, M32 = (1 << 64) - 1, (1 << 32) - 1
UNKNOWN = "unknown"
REGISTERS, VECTORS, NUMBERS = ("D", "S", "B", "P"), ("X", "Y", "Z"), ("I", "J", "K", "L", "N")
WIDE, MASKS = {"X512": "X", "Y512": "Y", "Z512": "Z"}, ("M",)      # a vector register's whole 512 bits as sixteen lanes; a mask register's sixteen bits


# The primitives that only move lanes about: the same whatever a lane is (a number, or a term of the verifier's).
MOVES = {
    "pick4": lambda a, b, i: (a[i & 3], a[(i >> 2) & 3], b[(i >> 4) & 3], b[(i >> 6) & 3]),
    "blend4": lambda a, b, i: tuple(b[k] if (i >> k) & 1 else a[k] for k in range(4)),
    # within each quarter of the register (four lanes): lanes picked from the first's quarter (0 to 3) and the second's (4 to 7)
    "in_quarters": lambda a, b, *pick: sum((tuple((a[q:q + 4] + b[q:q + 4])[p] for p in pick) for q in (0, 4, 8, 12)), ()),
    # quarters picked: two of the first register, then two of the second
    "quarters": lambda a, b, i: a[4 * (i % 4):][:4] + a[4 * (i // 4 % 4):][:4] + b[4 * (i // 16 % 4):][:4] + b[4 * (i // 64 % 4):][:4],
}
# bytes of memory at base + displacement (+ index). mem512a: sixty-four bytes on a 64-byte boundary (the instruction faults elsewhere)
SIZES = {"mem8": 1, "mem32": 4, "mem64": 8, "mem128": 16, "mem512": 64, "mem512a": 64}


def parse_row(text):
    """A decoded instruction as nested lists: `.mov 64 (.reg .rax) (.imm 0x4)` -> [".mov", "64", [".reg", ".rax"], [".imm", "0x4"]]."""
    stack = [[]]
    for t in re.findall(r"[()]|[^\s()]+", text):
        if t == "(": stack.append([])
        elif t == ")": done = stack.pop(); stack[-1].append(done)
        else: stack[-1].append(t)
    if len(stack) != 1: raise ValueError(f"brackets do not close in {text}")
    return stack[0]


def unify(pattern, ins, bind):
    """Whether the decoded instruction INS is an instance of the row's PATTERN; BIND gets what each placeholder is:
    a register's name, a vector register's number, or a number's text as the decoder wrote it."""
    if isinstance(pattern, list): return isinstance(ins, list) and len(pattern) == len(ins) and all(unify(p, x, bind) for p, x in zip(pattern, ins))
    if not isinstance(ins, str): return False
    if pattern[:1] == "." and pattern[1:] in REGISTERS:
        if not ins.startswith(".") or pattern == ".P" and ins == ".rsp" or ins == ".sp": return False     # (AArch64's sp is named in rows of its own)
        new = ins[1:]
    elif pattern in VECTORS or pattern in MASKS:
        if not ins.isdigit(): return False
        new = int(ins)
    elif pattern in NUMBERS: new = ins
    else: return pattern == ins
    key = pattern.lstrip(".")
    if bind.setdefault(key, new) != new: return False          # a placeholder written twice: the same thing both times
    return True


class Row:
    def __init__(self, name, asm, row, effect):
        self.name, self.asm, self.row, self.text = name, asm, row, effect
        self.bytes = []                 # the ways its instances are written in bytes: the `=` lines under it (encode.py reads them)
        self.pattern = parse_row(row)
        self.effect = [statement(s) for s in effect.split(";")]

    def match(self, ins):
        bind = {}
        return bind if unify(self.pattern, ins, bind) else None


def tokens(text):
    return re.findall(r"[A-Za-z_][A-Za-z_0-9]*|\d+|[().,=]", text)


def statement(text):
    t = tokens(text)
    if "=" in t:
        at = t.index("=")
        return ("set", expression(t[:at]), expression(t[at + 1:]))
    if t[0] == "jump":
        if "if" not in t: return ("jump", expression(t[1:]), None)
        at = t.index("if"); want = t[at + 1] != "not"
        flag = t[at + 1] if want else t[at + 2]
        if flag not in ("zf", "cf", "hi") or len(t) != at + (2 if want else 3): raise ValueError(f"cannot read {text}")
        return ("jump", expression(t[1:at]), (flag, want))
    if t[0] == "call":
        if "link" not in t: return ("call", expression(t[1:]))
        at = t.index("link")
        if len(t) != at + 2: raise ValueError(f"cannot read {text}")
        return ("call", expression(t[1:at]), t[at + 1])
    if t in (["return"], ["nothing"]): return (t[0],)
    if t[0] == "return" and len(t) == 2: return ("return", t[1])
    raise ValueError(f"cannot read {text}")


def expression(t):
    def one(i):
        if t[i].isdigit(): return ("number", int(t[i])), i + 1
        name = t[i]; i += 1
        if i < len(t) and t[i] == "(":
            args, i = [], i + 1
            while t[i] != ")":
                a, i = one(i); args.append(a)
                if t[i] == ",": i += 1
            return ("call", name, args), i + 1
        if i < len(t) and t[i] == ".": return ("lane", name, int(t[i + 1])), i + 2
        return ("name", name), i
    e, i = one(0)
    if i != len(t): raise ValueError(f"cannot read {' '.join(t)}")
    return e


_READ_CACHE = {}


def read(path=os.path.join(HERE, "x86.tab")):
    ap = os.path.abspath(path)
    st = os.stat(ap)
    key = (ap, st.st_mtime_ns, st.st_size)
    cached = _READ_CACHE.get(key)
    if cached is not None:
        return list(cached)
    rows = []
    with open(ap) as f:
        for line in f:
            line = line.split("#")[0].strip()
            if not line: continue
            if line.startswith("="): rows[-1].bytes.append(line[1:].strip()); continue
            parts = [p.strip() for p in line.split("|")]
            if len(parts) != 4: raise ValueError(f"a row that is not NAME | ASM | ROW | EFFECT: {line}")
            rows.append(Row(*parts))
    _READ_CACHE[key] = tuple(rows)
    return rows


def by_head(rows):
    """The rows under the first word of their ROW, in the table's order: the first that matches an instruction is its row."""
    heads = {}
    for row in rows: heads.setdefault(row.pattern[0], []).append(row)
    return heads


def find(heads, ins):
    """(the row this decoded instruction is an instance of, what its placeholders are), or (None, None)."""
    for row in heads.get(ins[0], ()):
        bind = row.match(ins)
        if bind is not None: return row, bind
    return None, None


if __name__ == "__main__":
    for r in read(): print(f"{r.name:13} {r.asm:36} {r.text}")
