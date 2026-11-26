#!/usr/bin/env python3
"""asm: Ode instructions to an x86-64 ELF object, by the table.

Called by `lang/odec.py`. Instruction forms use the encodings in `x86.tab` through `encode.py`.
Jumps start short; each pass widens jumps that no longer fit. `.p2align` uses table NOPs of up to ten
bytes. These objects are inputs to Ode's fixed-image linker. They carry no unwind information; the
historical `.cfi` directives are preserved only in the assembly listing.

An instruction is written as the row of the table that it is an instance of, or it is refused: after a row
is chosen, each operand as it is written must be of the class the row's ASM column has in its place (a
register of 64 bits, of 32, an xmm or a zmm register, memory, a number), and a size word before memory
(`byte ptr`, `qword ptr`, ...) must be the size that the row moves there (same()). So what is written
`mov byte ptr [rdi + 0], rax` or `movzx rax, al` or `vprord ymm1, ymm2, 7` is not laid down as another
instruction that the table happens to have. Which row a name and its operands choose is said by the branches
of write(). `lang/test_asm.py` compares all of it with clang: every instruction of the sources, changed in
many ways, is refused here or is the instruction that clang writes for the same text."""
import os, re, struct, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import encode, table

G64 = "rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15".split()
G32 = "eax ecx edx ebx esp ebp esi edi r8d r9d r10d r11d r12d r13d r14d r15d".split()
G8  = "al cl dl bl spl bpl sil dil r8b r9b r10b r11b r12b r13b r14b r15b".split()
G16 = "ax cx dx bx sp bp si di r8w r9w r10w r11w r12w r13w r14w r15w ah ch dh bh".split()         # (no row has one: they are named to be refused)

ROWS = {r.name: (r, [encode.Way(r, t) for t in r.bytes]) for r in table.read()}
NOPS = {len(w.literal): w.literal for w in ROWS["nop"][1] if w.literal is not None and w.literal != b"\xf3\x0f\x1e\xfa"}
JUMPS = {"jmp": "jmp", "je": "je", "jz": "je", "jne": "jne", "jnz": "jne", "jae": "jae", "jb": "jb", "ja": "ja", "jnbe": "ja", "jbe": "jbe", "jna": "jbe"}
CMOVS = {"cmove": "cmove64_rr", "cmovz": "cmove64_rr", "cmovne": "cmovne64_rr", "cmovnz": "cmovne64_rr",
         "cmovb": "cmovb64_rr", "cmovc": "cmovb64_rr", "cmovae": "cmovae64_rr", "cmovnc": "cmovae64_rr",
         "cmova": "cmova64_rr", "cmovnbe": "cmova64_rr", "cmovbe": "cmovbe64_rr", "cmovna": "cmovbe64_rr"}
BIN64 = {"add": "add64", "sub": "sub64", "and": "and64", "or": "or64", "cmp": "cmp64"}
VEC128 = {
    "paddd": ("paddd128", "L"), "vpaddd": ("paddd128", "V"),
    "pxor": ("pxor128", "L"), "vpxor": ("pxor128", "V"), "vpxord": ("pxor128", "E"),
    "pand": ("pand128", "L"), "vpand": ("pand128", "V"),
    "por": ("por128", "L"), "vpor": ("por128", "V"),
    "punpckldq": ("unpckldq", "L"), "vpunpckldq": ("unpckldq", "V"),
    "punpckhdq": ("unpckhdq", "L"), "vpunpckhdq": ("unpckhdq", "V"),
    "punpcklqdq": ("unpcklqdq", "L"), "vpunpcklqdq": ("unpcklqdq", "V"),
}
VEC512 = {
    "vpaddd": "paddd512", "vpxord": "pxord512",
    "vpunpckldq": "unpckldq512", "vpunpckhdq": "unpckhdq512",
    "vpunpcklqdq": "unpcklqdq512", "vpunpckhqdq": "unpckhqdq512",
}


# What an operand is, in words; the size word of the memory that a row moves to or from a register of a class;
# and the old two-operand forms of the rows that the table writes with three (the first operand is both).
CLASS = {"r64": "a register of 64 bits", "r32": "a register of 32 bits", "r8": "a register of 8 bits", "al": "al", "xmm0": "xmm0", "xmm": "an xmm register",
         "zmm": "a zmm register", "zmm{k}": "a zmm register under a mask", "k": "a mask register", "number": "a number", "memory": "memory"}
MOVED = {"r64": "qword", "r32": "dword", "r8": "byte", "xmm": "xmmword", "zmm": "zmmword", "zmm{k}": "zmmword"}
TWO = {m for m, (_, k) in VEC128.items() if k == "L"} | {"shufps", "pslld", "psrld"}
WORD = r"(?:(byte|word|dword|qword|xmmword|ymmword|zmmword)\s+ptr\s*)?"
PICKED = [None]                    # the row that pick() last took


def up(n, align): return (n + align - 1) & ~(align - 1)


def num(tok):
    try: return int(tok.replace("_", ""), 0)
    except ValueError: raise ValueError(f"not a number: {tok}") from None


def operand(text):
    """An operand as it is written: (its class, the size word before memory or None)."""
    t = text.strip()
    m = re.fullmatch(WORD + r"\[.*\]", t, flags=re.I)
    if m: return "memory", (m.group(1).lower() if m.group(1) else None)
    for names, cls in ((G64, "r64"), (G32, "r32"), (G8, "r8"), (G16, "r16")):
        if t in names: return cls, None
    m = re.fullmatch(r"([xyz]mm)\d+", t)
    if m: return m.group(1), None
    if re.fullmatch(r"zmm\d+\s*\{k\d\}", t): return "zmm{k}", None
    if re.fullmatch(r"k\d", t): return "k", None
    if re.fullmatch(r"-?(?:0[xX][0-9a-fA-F_]+|\d[\d_]*)", t): return "number", None
    return "other", None


def template(row, mn):
    """The operands of a row as the table writes an instance of it (its ASM column): [(class, size word)].
    Memory written there without a size word has the size of the row's register (`mov [B64 + N], S64`: a
    qword); `lea` moves nothing, so any word may stand before its memory."""
    out = []
    for t in [x.strip() for x in row.asm.partition(" ")[2].split(",") if x.strip()]:
        m = re.fullmatch(WORD + r"\[.*\]", t)
        if m: out.append(("memory", m.group(1))); continue
        cls = ("al" if t == "al" else "xmm0" if t == "xmm0" else "r64" if re.fullmatch(r"[A-Z]64", t) else "r32" if re.fullmatch(r"[A-Z]32", t) else "r8" if re.fullmatch(r"[A-Z]8", t)
               else "xmm" if re.fullmatch(r"xmm[A-Z]", t) else "zmm" if re.fullmatch(r"zmm[A-Z]", t) else "zmm{k}" if re.fullmatch(r"zmm[A-Z]\{kM\}", t)
               else "k" if t == "kM" else "number" if t == "I" or t.isdigit() else None)
        if cls is None: raise ValueError(f"x86.tab: the operand `{t}` of `{row.asm}` is not read")
        out.append((cls, None))
    moved = next((MOVED[c] for c, _ in out if c in MOVED), None)
    return [(c, w or (moved if c == "memory" and mn != "lea" else None)) for c, w in out]


def same(mn, ops, row):
    """The instruction as it is written is an instance of the row as the table writes it: as many operands,
    each of the row's class, and memory of the row's size where a size word says one."""
    want = template(row, mn)
    if mn in TWO: del want[1]
    if len(want) != len(ops): raise ValueError(f"{len(ops)} operands where x86.tab's `{row.asm}` has {len(want)}")
    for text, (cls, word) in zip(ops, want):
        got, given = operand(text)
        if (text.strip() != cls) if cls in ("al", "xmm0") else (got != cls): raise ValueError(f"`{text.strip()}` where x86.tab's `{row.asm}` has {CLASS[cls]}")
        if given is not None and word is not None and given != word: raise ValueError(f"`{given} ptr` where x86.tab's `{row.asm}` moves a {word}")


def imm(tok, bits):
    n = num(tok)
    if not -(1 << (bits - 1)) <= n < (1 << bits): raise ValueError(f"immediate outside {bits} bits: {tok}")
    return n % (1 << bits)


def nop_pad(count):
    out = bytearray()
    while count > 0:
        step = min(count, 10)
        out += NOPS[step]
        count -= step
    return bytes(out)


def parse_mem(text):
    s = re.sub(r"^(?:byte|word|dword|qword|xmmword|ymmword|zmmword)\s+ptr\s*", "", text.strip(), flags=re.I)        # (same() reads the word)
    if not (s.startswith("[") and s.endswith("]")): raise ValueError(f"not a memory operand: {text}")
    base, index, disp, sym = None, None, 0, None
    for raw in re.findall(r"[+-]?\s*[^+-]+", s[1:-1].strip()):
        sign = -1 if raw.lstrip().startswith("-") else 1
        tok = raw.lstrip("+- \t").strip()
        if tok == "rip":
            if base is not None or sign != 1: raise ValueError(f"bad rip operand: {text}")
            base = "rip"
        elif tok in G64:
            if sign != 1: raise ValueError(f"subtracted register in {text}")
            if base is None: base = G64.index(tok)
            elif index is None: index = G64.index(tok)
            else: raise ValueError(f"more than two registers in {text}")
        elif re.fullmatch(r"\d+|0x[0-9a-fA-F_]+", tok): disp += sign * num(tok)
        elif sign == 1 and sym is None: sym = tok
        else: raise ValueError(f"cannot read {tok} in {text}")
    if base == "rip":
        if sym is None or index is not None: raise ValueError(f"bad rip operand: {text}")
        return ("rip", sym, disp)
    if base is None or sym is not None or not -(1 << 31) <= disp < (1 << 31): raise ValueError(f"bad memory operand: {text}")
    return ("mem", base, index, disp & table.M64)


def pick(row_name, bind, pred=None, at=0):
    best = None
    PICKED[0] = row_name
    for w in ROWS[row_name][1]:
        if pred is not None and not pred(w): continue
        try: b = encode.encode(w, bind, at)
        except encode.Refuse: continue
        if best is None or len(b) < len(best): best = b
    if best is None: raise ValueError(f"no way in x86.tab writes {row_name} {bind}")
    return best


def forms_for(mn):
    """Supported ASM templates from x86.tab for mnemonic `mn` (read directly from the table)."""
    forms = []
    for row, _ in ROWS.values():
        if row.asm != "-" and row.asm.split()[0] == mn and row.asm not in forms:
            forms.append(row.asm)
    return forms


def instruction(line):
    """('fixed', bytes) | ('reloc', bytes, field_off, r_type, sym, addend) | ('jump', row_name, label).
    What is written is an instance of the row it is laid down by (same()), or ValueError says why not."""
    mn, _, rest = line.partition(" ")
    ops = [p.strip() for p in rest.strip().split(",")] if rest.strip() else []
    PICKED[0] = None
    try: item = write(line, mn, ops)
    except (KeyError, IndexError, TypeError): raise ValueError("instruction not in x86.tab") from None
    except ValueError as e:
        if "not in list" in str(e) or "invalid literal" in str(e): raise ValueError("instruction not in x86.tab") from None      # (Python's words for an operand of no class the form has)
        raise
    row = ROWS[PICKED[0]][0] if PICKED[0] is not None else None
    if row is not None and row.asm != "-" and mn != "prefetcht0": same(mn, ops, row)             # (a prefetch is laid down by the row of `nop`)
    return item


def write(line, mn, ops):
    """The bytes of an instruction by the row that its name and its operands choose (instruction() then asks that it is that row's)."""
    if mn in ("nop", "endbr64", "ret", "vzeroupper") and ops: raise ValueError(f"{mn} takes no operands")
    if mn == "nop": return ("fixed", b"\x90")
    if mn == "endbr64": return ("fixed", b"\xf3\x0f\x1e\xfa")
    if mn in ("ret", "vzeroupper"): return ("fixed", pick(mn, {}))
    if mn == "prefetcht0":
        if len(ops) != 1 or operand(ops[0])[1] not in (None, "byte"): raise ValueError("a prefetch names one address, with `byte ptr` before it or no size word")
        _, base, idx, disp = parse_mem(ops[0])
        if idx is None: return ("fixed", pick("nop", {"b": base, "n": disp}, lambda w: w.fields.get("base") == ("b",) and "index" not in w.fields))
        return ("fixed", pick("nop", {"b": base, "s": idx, "n": disp}, lambda w: "index" in w.fields))
    if mn in JUMPS:
        if len(ops) != 1: raise ValueError("a jump names one label")
        if mn == "jmp":
            mc = re.fullmatch(r"CALL\((\w+)\)", ops[0])
            if mc:
                return ("reloc", b"\xe9\x00\x00\x00\x00", 1, 4, mc.group(1), -4)
        if operand(ops[0])[0] != "other": raise ValueError("a jump names one label")
        return ("jump", JUMPS[mn], ops[0])
    if mn == "call":
        m = re.fullmatch(r"CALL\((\w+)\)|(\w+)", ops[0]) if len(ops) == 1 else None
        if not m: raise ValueError(f"cannot read call target: {line}")
        sym = m.group(1) or m.group(2)
        if m.group(2) and operand(sym)[0] != "other": raise ValueError("x86.tab has no call of a register: a call names a function")
        b = pick("call", {"I": sym, "field": bytes(4)})
        return ("reloc", b, len(b) - 4, 4, sym, -4)
    if mn in ("push", "pop"):
        r = G64.index(ops[0])
        if r == 4: raise ValueError(f"{mn} rsp is not in x86.tab")
        return ("fixed", pick(mn, {"P": r}))
    if mn == "dec":
        if ops[0] == "al": return ("fixed", pick("dec8_al", {}))
        return ("fixed", pick("dec64", {"D": G64.index(ops[0])}) if ops[0] in G64 else pick("dec32", {"D": G32.index(ops[0])}))
    if mn in ("test", "xor"):
        if ops[0] != ops[1]: raise ValueError(f"{mn} requires equal operands in x86.tab: {line}")
        return ("fixed", pick(f"{mn}64_same", {"D": G64.index(ops[0])}) if ops[0] in G64 else pick(f"{mn}32_same", {"D": G32.index(ops[0])}))
    if mn in ("shl", "shr"):
        count = num(ops[1])
        return ("fixed", pick(f"{mn}64_ri", {"D": G64.index(ops[0]), "I": count}) if ops[0] in G64 else pick(f"{mn}32_ri", {"D": G32.index(ops[0]), "I": count}))
    if mn in BIN64:
        base_row = BIN64[mn]
        if ops[0] in G64:
            d = G64.index(ops[0])
            if ops[1] in G64: return ("fixed", pick(f"{base_row}_rr", {"D": d, "S": G64.index(ops[1])}))
            if "[" in ops[1]:
                _, b, idx, disp = parse_mem(ops[1])
                if idx is not None: raise ValueError(f"indexed {mn} not in x86.tab: {line}")
                return ("fixed", pick(f"{base_row}_rm", {"D": d, "B": b, "N": disp}))
            return ("fixed", pick(f"{base_row}_ri", {"D": d, "I": imm(ops[1], 64)}))
        d = G32.index(ops[0])
        if mn == "or" and ops[1] in G32: return ("fixed", pick("or32_rr", {"D": d, "S": G32.index(ops[1])}))
        if mn == "and":
            v = imm(ops[1], 32)
            return ("fixed", pick("and32_ri", {"D": d, "I": (v - (1 << 32)) & table.M64 if v >= 0xFFFFFF80 else v}))
    if mn == "lea":
        if len(ops) != 2: raise ValueError("lea takes a register and an address")
        d, m = G64.index(ops[0]), parse_mem(ops[1])
        if m[0] == "rip":
            b = pick("lea_data", {"D": d, "I": 0, "field": bytes(4)})
            return ("reloc", b, len(b) - 4, 2, m[1], m[2] - 4)
        if m[2] is not None:
            b, idx = m[1], m[2]
            if idx == 4:
                if b == 4: raise ValueError(f"x86-64 cannot use rsp as both base and index: {line}")
                b, idx = idx, b
            return ("fixed", pick("lea_idx", {"D": d, "B": b, "S": idx, "N": m[3]}))
        return ("fixed", pick("lea", {"D": d, "B": m[1], "N": m[3]}))
    if mn == "movzx":
        d = G32.index(ops[0]) if ops[0] in G32 else G64.index(ops[0])
        if ops[1] in G8: return ("fixed", pick("movzx8_rr", {"D": d, "S": G8.index(ops[1])}))
        if operand(ops[1]) == ("memory", None): raise ValueError("movzx from memory needs the size word of what it reads: `byte ptr [...]`")
        _, b, idx, disp = parse_mem(ops[1])
        if idx is not None: raise ValueError(f"indexed movzx not in x86.tab: {line}")
        return ("fixed", pick("movzx8_rm", {"D": d, "B": b, "N": disp}))
    if mn in CMOVS:
        if len(ops) != 2 or ops[0] not in G64 or ops[1] not in G64:
            raise ValueError(f"{mn} takes two 64-bit registers: {line}")
        return ("fixed", pick(CMOVS[mn], {"D": G64.index(ops[0]), "S": G64.index(ops[1])}))
    if mn == "mov":
        if ops[0] == "al":
            if operand(ops[1])[0] != "number": raise ValueError(f"x86.tab has `mov al, I` alone into al (a byte is loaded by `movzx`): not from {ops[1]}")
            return ("fixed", pick("mov8_al_i", {"I": imm(ops[1], 8)}))
        if ops[0] in G64:
            d = G64.index(ops[0])
            if ops[1] in G64: return ("fixed", pick("mov64_rr", {"D": d, "S": G64.index(ops[1])}))
            if "[" in ops[1]:
                _, b, idx, disp = parse_mem(ops[1])
                if idx is not None: raise ValueError(f"indexed mov not in x86.tab: {line}")
                return ("fixed", pick("mov64_rm", {"D": d, "B": b, "N": disp}))
            return ("fixed", pick("mov64_ri", {"D": d, "I": imm(ops[1], 64)}))
        if ops[0] in G32:
            d = G32.index(ops[0])
            if ops[1] in G32: return ("fixed", pick("mov32_rr", {"D": d, "S": G32.index(ops[1])}))
            if "[" in ops[1]:
                _, b, idx, disp = parse_mem(ops[1])
                if idx is not None: raise ValueError(f"indexed mov32 not in x86.tab: {line}")
                return ("fixed", pick("mov32_rm", {"D": d, "B": b, "N": disp}))
            return ("fixed", pick("mov32_ri", {"D": d, "I": imm(ops[1], 32)}))
        _, b, idx, disp = parse_mem(ops[0])
        if idx is not None: raise ValueError(f"indexed store not in x86.tab: {line}")
        if ops[1] in G8: return ("fixed", pick("mov8_mr", {"B": b, "N": disp, "S": G8.index(ops[1])}))
        if ops[1] in G64: return ("fixed", pick("mov64_mr", {"B": b, "N": disp, "S": G64.index(ops[1])}))
        if operand(ops[1])[0] != "number": raise ValueError(f"x86.tab has a store of an 8-bit register, of a 64-bit register, and of an 8-bit number: not of {ops[1]}")
        if operand(ops[0])[1] != "byte": raise ValueError("x86.tab has a store of a number for one byte only, written `mov byte ptr [...], N`")
        return ("fixed", pick("mov8_mi", {"B": b, "N": disp, "I": imm(ops[1], 8)}))
    if mn in ("movq", "vmovq"):
        k = "V" if mn.startswith("v") else "L"
        return ("fixed", pick("movq128", {"X": int(ops[0][3:]), "S": G64.index(ops[1])}, lambda w: w.kind == k))
    if mn in ("movups", "vmovups", "vmovdqu", "movaps", "vmovaps", "movdqa", "vmovdqa"):
        k = "V" if mn.startswith("v") else "L"
        pp = (2 if mn == "vmovdqu" else 1 if mn == "vmovdqa" else 0) if k == "V" else (0x66 if mn == "movdqa" else 0)
        # The table has the move between registers by the aligned names, and the move from or to memory by the
        # unaligned names (with the file's data, by movaps): each name is laid down as itself, or refused.
        if re.fullmatch(r"xmm\d+", ops[0]) and re.fullmatch(r"xmm\d+", ops[1]):
            if mn in ("movups", "vmovups", "vmovdqu"): raise ValueError("x86.tab has the move between xmm registers as movaps, movdqa, vmovaps and vmovdqa")
            return ("fixed", pick("mov128", {"X": int(ops[0][3:]), "Y": int(ops[1][3:])}, lambda w: w.kind == k and w.pp == pp))
        if re.fullmatch(r"xmm\d+", ops[0]):
            x, m = int(ops[0][3:]), parse_mem(ops[1])
            if m[0] == "rip":
                if mn not in ("movaps", "vmovaps"): raise ValueError(f"rip 128-bit load not movaps: {line}")
                b = pick("const128", {"X": x, "I": 0, "J": 0, "K": 0, "L": 0, "field": bytes(4)}, lambda w: w.kind == k)
                return ("reloc", b, len(b) - 4, 2, m[1], m[2] - 4)
            if mn not in ("movups", "vmovups", "vmovdqu"): raise ValueError("x86.tab has the move of an xmm register from memory as movups, vmovups and vmovdqu")
            if m[2] is not None: raise ValueError(f"indexed 128-bit load not in x86.tab: {line}")
            return ("fixed", pick("loadu128", {"X": x, "B": m[1], "N": m[3]}, lambda w: w.kind == k and w.pp == pp))
        if mn not in ("movups", "vmovups", "vmovdqu"): raise ValueError("x86.tab has the move of an xmm register to memory as movups, vmovups and vmovdqu")
        _, base, idx, disp = parse_mem(ops[0])
        if idx is not None: raise ValueError(f"indexed 128-bit store not in x86.tab: {line}")
        return ("fixed", pick("storeu128", {"X": int(ops[1][3:]), "B": base, "N": disp}, lambda w: w.kind == k and w.pp == pp))
    if mn in ("vmovdqa32", "vmovdqu32"):
        aligned, pp = mn == "vmovdqa32", (1 if mn == "vmovdqa32" else 2)
        if re.fullmatch(r"zmm\d+", ops[0]) and re.fullmatch(r"zmm\d+", ops[1]):
            return ("fixed", pick("mov512", {"X": int(ops[0][3:]), "Y": int(ops[1][3:])}, lambda w: w.pp == pp))
        if re.fullmatch(r"zmm\d+", ops[0]):
            x, (_, base, idx, disp) = int(ops[0][3:]), parse_mem(ops[1])
            if idx is not None:
                if aligned: raise ValueError(f"aligned indexed 512-bit load: {line}")
                return ("fixed", pick("load512i", {"X": x, "B": base, "S": idx, "N": disp}))
            return ("fixed", pick("load512a" if aligned else "load512", {"X": x, "B": base, "N": disp}))
        _, base, idx, disp = parse_mem(ops[0])
        if idx is not None: raise ValueError(f"indexed 512-bit store: {line}")
        return ("fixed", pick("store512a" if aligned else "store512", {"X": int(ops[1][3:]), "B": base, "N": disp}))
    if mn in ("pslld", "psrld"):
        x = int(ops[0][3:])
        return ("fixed", pick(f"{mn}128", {"X": x, "Y": x, "I": num(ops[1])}, lambda w: w.kind == "L"))
    if mn in ("vpslld", "vpsrld"):
        return ("fixed", pick(f"{mn[1:]}128", {"X": int(ops[0][3:]), "Y": int(ops[1][3:]), "I": num(ops[2])}, lambda w: w.kind == "V"))
    if mn == "pshufb": return ("fixed", pick("pshufb128", {"X": int(ops[0][3:]), "Z": int(ops[1][3:])}))
    if mn == "pblendw": return ("fixed", pick("pblendw128", {"X": int(ops[0][3:]), "Z": int(ops[1][3:]), "I": num(ops[2])}))
    if mn in ("pshufd", "vpshufd"):
        k = "V" if mn.startswith("v") else "L"
        return ("fixed", pick("pshufd128", {"X": int(ops[0][3:]), "Y": int(ops[1][3:]), "I": num(ops[2])}, lambda w: w.kind == k))
    if mn in ("shufps", "vshufps"):
        if not mn.startswith("v"):
            x = int(ops[0][3:])
            return ("fixed", pick("shufps128", {"X": x, "Y": x, "Z": int(ops[1][3:]), "I": num(ops[2])}, lambda w: w.kind == "L"))
        return ("fixed", pick("shufps128", {"X": int(ops[0][3:]), "Y": int(ops[1][3:]), "Z": int(ops[2][3:]), "I": num(ops[3])}, lambda w: w.kind == "V"))
    if mn == "vpblendd": return ("fixed", pick("pblendd128", {"X": int(ops[0][3:]), "Y": int(ops[1][3:]), "Z": int(ops[2][3:]), "I": num(ops[3])}))
    if mn == "vpalignr":
        iv = num(ops[3])
        if iv not in (4, 8, 12): raise ValueError(f"vpalignr immediate must be 4, 8, or 12: {line}")
        return ("fixed", pick(f"palignr{iv}", {"X": int(ops[0][3:]), "Y": int(ops[1][3:]), "Z": int(ops[2][3:])}))
    if mn == "sha256rnds2":
        if len(ops) != 3 or ops[2] != "xmm0": raise ValueError(f"sha256rnds2 takes `xmmX, xmmZ, xmm0`: {line}")
        return ("fixed", pick("sha256rnds2", {"X": int(ops[0][3:]), "Z": int(ops[1][3:])}))
    if mn in ("sha256msg1", "sha256msg2"):
        return ("fixed", pick(mn, {"X": int(ops[0][3:]), "Z": int(ops[1][3:])}))
    if mn == "vprord":
        return ("fixed", pick("prord128" if ops[0].startswith("xmm") else "prord512", {"X": int(ops[0][3:]), "Y": int(ops[1][3:]), "I": num(ops[2])}))
    if mn == "vpbroadcastd":
        x = int(ops[0][3:])
        if ops[1] in G32: return ("fixed", pick("broadcast_r", {"X": x, "S": G32.index(ops[1])}))
        m = parse_mem(ops[1])
        if m[0] == "rip":
            b = pick("broadcast_i", {"X": x, "I": 0, "field": bytes(4)})
            return ("reloc", b, len(b) - 4, 2, m[1], m[2] - 4)
        if m[2] is not None: raise ValueError(f"indexed broadcast: {line}")
        return ("fixed", pick("broadcast_m", {"X": x, "B": m[1], "N": m[3]}))
    if mn == "vpcmpud":
        if num(ops[3]) != 1: raise ValueError(f"vpcmpud immediate not 1: {line}")
        return ("fixed", pick("pcmpud512", {"M": int(ops[0][1:]), "X": int(ops[1][3:]), "Y": int(ops[2][3:])}))
    if mn == "vshufi32x4": return ("fixed", pick("shufi32x4", {"X": int(ops[0][3:]), "Y": int(ops[1][3:]), "Z": int(ops[2][3:]), "I": num(ops[3])}))
    if re.fullmatch(r"xmm\d+", ops[0]) and mn in VEC128:
        row_name, k = VEC128[mn]
        x = int(ops[0][3:])
        if k == "L": return ("fixed", pick(row_name, {"X": x, "Y": x, "Z": int(ops[1][3:])}, lambda w: w.kind == "L"))
        y, z = int(ops[1][3:]), int(ops[2][3:])
        if k == "V" and mn in ("vpaddd", "vpxor", "vpor", "vpand") and y < 8 <= z: y, z = z, y
        return ("fixed", pick(row_name, {"X": x, "Y": y, "Z": z}, lambda w: w.kind == k))
    if ops[0].startswith("zmm"):
        mk = re.fullmatch(r"zmm(\d+)\s*\{k(\d+)\}", ops[0])
        if mk:
            if mn != "vpaddd": raise ValueError(f"masked {mn} not in x86.tab: {line}")
            return ("fixed", pick("paddd512k", {"X": int(mk.group(1)), "M": int(mk.group(2)), "Y": int(ops[1][3:]), "Z": int(ops[2][3:])}))
        x, y = int(ops[0][3:]), int(ops[1][3:])
        if "[" in ops[2]:
            if mn != "vpaddd": raise ValueError(f"memory {mn} not in x86.tab: {line}")
            m = parse_mem(ops[2])
            if m[0] == "rip":
                b = pick("paddd512c", {"X": x, "Y": y, "K": 0, "field": bytes(4)})
                return ("reloc", b, len(b) - 4, 2, m[1], m[2] - 4)
            if m[2] is None: raise ValueError("x86.tab has `vpaddd zmmX, zmmY, [B64 + S64 + N]`: its memory has an index register")
            return ("fixed", pick("paddd512m", {"X": x, "Y": y, "B": m[1], "S": m[2], "N": m[3]}))
        z = int(ops[2][3:])
        if mn == "vpxord" and y == z: return ("fixed", pick("pxord512_same", {"X": x, "Y": y}))
        return ("fixed", pick(VEC512[mn], {"X": x, "Y": y, "Z": z}))
    raise ValueError(f"instruction not in x86.tab: {line}")


def build_elf(name, symbol, expanded, notes, data, where=None, locs=None):
    """Assemble expanded lines into a relocatable little-endian x86-64 ELF object (`bytes`).
    A note ("at", INDEX, LABEL) puts the label LABEL before the instruction of that index and nothing into
    the object. `where`, if a dict, gets every label's count of bytes from the function's first byte.
    `locs`, if a list, gets (byte_offset, byte_len, orig_expanded_index) for each emitted instruction."""
    tagged = [(k, s) for k, s in enumerate(expanded)]
    entries = []
    has_place = False
    for note in sorted(notes, key=lambda n: -n[1]):
        if note[0] == "place": tagged[note[1]:note[1]] = [(None, f".Lode_place_{name}:")]; has_place = True
        elif note[0] == "at": tagged[note[1]:note[1]] = [(None, f"{note[2]}:")]
        else: tagged[note[1]:note[1]] = [(None, f"{note[2]}:")]; entries.append(note[2])
    top_align = 1 << int(tagged.pop(0)[1].split()[1]) if tagged and tagged[0][1].startswith(".p2align ") else 16
    used = [(n, ws) for n, ws in data if any(f".Lode_data_{n}]" in x or f".Lode_data_{n} " in x for _, x in tagged)]

    items = [("label", symbol)]
    orig_of = [None]
    for orig_idx, s in tagged:
        if s.endswith(":"): items.append(("label", s[:-1])); orig_of.append(None)
        elif s.startswith(".p2align "): items.append(("align", 1 << int(s.split()[1]))); orig_of.append(None)
        elif s.split()[0] in {".cfi_startproc", ".cfi_endproc", ".cfi_offset", ".cfi_restore", ".cfi_def_cfa", ".cfi_def_cfa_offset", ".cfi_def_cfa_register"}: continue
        else: items.append(instruction(s)); orig_of.append(orig_idx)

    defined_labels = {it[1] for it in items if it[0] == "label"}
    items = [
        ("reloc", b"\xe9\x00\x00\x00\x00", 1, 4, it[2], -4)
        if it[0] == "jump" and it[1] == "jmp" and it[2] not in defined_labels and not it[2].startswith(".")
        else it
        for it in items
    ]
    long_jumps = set()
    while True:
        off, labels, starts = 0, {}, {}
        for idx, it in enumerate(items):
            starts[idx] = off
            if it[0] == "label": labels[it[1]] = off
            elif it[0] == "align": off += (-off) % it[1]
            elif it[0] in ("fixed", "reloc"): off += len(it[1])
            elif it[0] == "jump": off += (5 if it[1] == "jmp" else 6) if idx in long_jumps else 2
        widen = {idx for idx, it in enumerate(items) if it[0] == "jump" and idx not in long_jumps
                 and not (-128 <= labels[it[2]] - (starts[idx] + 2) < 128)}
        if widen: long_jumps |= widen; continue
        code, relocs = bytearray(), []
        for idx, it in enumerate(items):
            if it[0] == "label": continue
            before = len(code)
            if it[0] == "align": code += nop_pad((-starts[idx]) % it[1])
            elif it[0] == "fixed": code += it[1]
            elif it[0] == "reloc":
                relocs.append((starts[idx] + it[2], it[3], it[4], it[5])); code += it[1]
            elif it[0] == "jump":
                code += encode.encode(ROWS[it[1]][1][1 if idx in long_jumps else 0], {"I": labels[it[2]]}, starts[idx])
            if locs is not None and orig_of[idx] is not None:
                locs.append((before, len(code) - before, orig_of[idx]))
        break
    if where is not None: where.update(labels)

    rodata, data_at = bytearray(), {}
    for n, ws in used:
        rodata += bytes((-len(rodata)) % 64)
        data_at[f".Lode_data_{n}"] = len(rodata)
        for w in ws: rodata += struct.pack("<I", w & 0xFFFFFFFF)

    # Section indices: 0 null, 1 .text, [rodata], [.ode.place], .note.GNU-stack, [.rela.text], .symtab, .strtab, .shstrtab
    text_align = max([top_align] + [it[1] for it in items if it[0] == "align"])
    sec_list = [(".text", 1, 6, text_align, 0, bytes(code))]
    rodata_idx = None
    if used:
        rodata_idx = len(sec_list) + 1
        sec_list.append((".rodata", 1, 2, 64, 0, bytes(rodata)))
    if has_place:
        place_bytes = struct.pack("<I", labels[f".Lode_place_{name}"] - labels[symbol])
        sec_list.append((".ode.place", 1, 0, 1, 0, place_bytes))
    sec_list.append((".note.GNU-stack", 1, 0, 1, 0, b""))

    # Symbols: all STB_LOCAL first (`sh_info` = index of first STB_GLOBAL), then defined globals, then externs.
    strtab, syms = bytearray(b"\0"), bytearray(24)
    def add_str(s):
        if not s: return 0
        at = len(strtab); strtab.extend(s.encode() + b"\0"); return at
    rodata_sym = None
    if rodata_idx is not None:
        rodata_sym = len(syms) // 24
        syms += struct.pack("<IBBHQQ", 0, (0 << 4) | 3, 0, rodata_idx, 0, 0)    # STB_LOCAL | STT_SECTION
    first_global = len(syms) // 24
    sym_index = {}
    for gsym in [symbol] + [e for e in entries if e != symbol]:
        sym_index[gsym] = len(syms) // 24
        syms += struct.pack("<IBBHQQ", add_str(gsym), (1 << 4) | 2, 0, 1, labels[gsym], len(code) - labels[gsym])
    for _, kind, target, _ in relocs:
        if kind == 2 and target in data_at: continue
        if target not in sym_index:
            sym_index[target] = len(syms) // 24
            syms += struct.pack("<IBBHQQ", add_str(target), (1 << 4) | 0, 0, 0, 0, 0)

    rela = bytearray()
    for r_off, kind, target, addend in relocs:
        if kind == 2 and target in data_at:
            rela += struct.pack("<QQq", r_off, (rodata_sym << 32) | 2, data_at[target] + addend)
        else:
            rela += struct.pack("<QQq", r_off, (sym_index[target] << 32) | kind, addend)

    rela_idx = None
    if rela:
        rela_idx = len(sec_list) + 1
        sec_list.append((".rela.text", 4, 0x40, 8, 24, bytes(rela)))
    symtab_idx = len(sec_list) + 1
    strtab_idx = symtab_idx + 1
    shstrtab_idx = strtab_idx + 1
    sec_list.append((".symtab", 2, 0, 8, 24, bytes(syms)))
    sec_list.append((".strtab", 3, 0, 1, 0, bytes(strtab)))

    shstr = bytearray(b"\0")
    sh_names = {}
    for sname, *_ in sec_list + [(".shstrtab",)]:
        sh_names[sname] = len(shstr); shstr.extend(sname.encode() + b"\0")
    sec_list.append((".shstrtab", 3, 0, 1, 0, bytes(shstr)))

    blob = bytearray(64)
    headers = [bytes(64)]
    for idx, (sname, stype, sflags, salign, sentsize, sbytes) in enumerate(sec_list, 1):
        blob += bytes(up(len(blob), max(salign, 1)) - len(blob))
        soff = len(blob)
        blob += sbytes
        slink = symtab_idx if idx == rela_idx else (strtab_idx if idx == symtab_idx else 0)
        sinfo = 1 if idx == rela_idx else (first_global if idx == symtab_idx else 0)
        headers.append(struct.pack("<IIQQQQIIQQ", sh_names[sname], stype, sflags, 0, soff, len(sbytes), slink, sinfo, salign, sentsize))
    blob += bytes(up(len(blob), 8) - len(blob))
    shoff = len(blob)
    for h in headers: blob += h
    blob[:64] = b"\x7fELF\x02\x01\x01" + bytes(9) + struct.pack("<HHIQQQIHHHHHH", 1, 62, 1, 0, 0, shoff, 0, 64, 0, 0, 64, len(headers), shstrtab_idx)
    return bytes(blob)

