#!/usr/bin/env python3
"""asm: AArch64 instructions to an AArch64 ELF object, directly from arm64.tab.

Matches each instruction against the ASM templates in `arm64.tab` (plus `bl SYMBOL` and `ret`), encodes
each four-byte word with `word.encode`, and checks that `word.decode` reads the same row back. Produces a
64-bit little-endian AArch64 relocatable ELF object (`EM_AARCH64 = 183`) readable by `obj.py`.
Nothing here names Ode's verifier or contracts."""
import os, re, struct, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path[:0] = [HERE, os.path.join(HERE, "..", "core")]
import table, word

EM_AARCH64 = 183
R_AARCH64_CALL26 = 283
G64 = {f"x{i}": f"x{i}" for i in range(31)}
G32 = {f"w{i}": f"x{i}" for i in range(31)}


def up(n, align):
    return (n + align - 1) & ~(align - 1)


def _num(tok):
    t = tok.strip()
    if t.startswith("#"):
        t = t[1:].strip()
    if not re.fullmatch(r"-?(?:0[xX][0-9a-fA-F_]+|\d[\d_]*)", t):
        return None
    return int(t.replace("_", ""), 0)


def _compile_template(asm_text):
    """Compile an ASM template from arm64.tab into (regex, [(placeholder, kind)]).
    Accepts optional `#` before immediates and `[BASE]` as shorthand for `[BASE, 0]`."""
    groups = []
    # Split keeping delimiters, handling `[BASE, N]` shorthand cleanly.
    s = asm_text.strip()
    # Allow `[B64]` / `[sp]` when template ends with `, N]`
    optional_n = re.search(r",\s*N\]$", s) is not None
    if optional_n:
        s = re.sub(r",\s*N\]$", "", s)
    parts = re.split(r"(\s+|,|\[|\]|\{|\})", s)
    pat = []
    for p in parts:
        if not p:
            continue
        if p.isspace():
            pat.append(r"\s+")
        elif p in (",", "[", "]", "{", "}"):
            pat.append(r"\s*" + re.escape(p) + r"\s*")
        elif re.fullmatch(r"[DSPB]64", p):
            groups.append((p[0], "g64"))
            pat.append(r"([A-Za-z_]\w*)")
        elif re.fullmatch(r"[DSPB]32", p):
            groups.append((p[0], "g32"))
            pat.append(r"([A-Za-z_]\w*)")
        elif re.fullmatch(r"v([XYZ])\.(4s|16b|8h|2d)", p):
            m = re.fullmatch(r"v([XYZ])\.(4s|16b|8h|2d)", p)
            groups.append((m.group(1), "vec"))
            pat.append(r"v(\d+)\." + re.escape(m.group(2)))
        elif re.fullmatch(r"d([XYZ])", p):
            groups.append((p[1], "vec"))
            pat.append(r"d(\d+)")
        elif p in ("I", "N"):
            groups.append((p, "imm"))
            pat.append(r"(#?-?(?:0[xX][0-9a-fA-F_]+|\d[\d_]*))")
        elif re.fullmatch(r"\d+", p):
            pat.append(r"#?" + re.escape(p))
        else:
            pat.append(re.escape(p))
    if optional_n:
        groups.append(("N", "imm_opt"))
        pat.append(r"(?:\s*,\s*(#?-?(?:0[xX][0-9a-fA-F_]+|\d[\d_]*)))?\s*\]")
    return re.compile(r"^\s*" + "".join(pat) + r"\s*$"), groups


def _load():
    rows = table.read(word.TABLE)
    all_ways = word.ways(rows)
    by_name = {}
    matchers = []
    for w in all_ways:
        by_name.setdefault(w.row.name, []).append(w)
        if w.row.asm != "-":
            rx, groups = _compile_template(w.row.asm)
            matchers.append((w, rx, groups))
    return rows, all_ways, by_name, matchers


ROWS, ALL_WAYS, BY_NAME, MATCHERS = _load()
NOP_WORD = word.encode(BY_NAME["nop"][0], {})
BRANCH_ROWS = {"b": "b", "b.eq": "b_eq", "b.ne": "b_ne", "b.hs": "b_hs", "b.cs": "b_hs", "b.lo": "b_lo", "b.cc": "b_lo"}


def instruction(line):
    """Assemble one AArch64 instruction line into:
      ("fixed", 4-byte bytes, row, bind)
      ("reloc", 4-byte bytes, 0, R_AARCH64_CALL26, symbol, 0, row, bind)
      ("jump", way, label, row, bind)
    Raises ValueError if the instruction is not an instance of a row in arm64.tab."""
    s = line.split("//")[0].strip()
    if s == "ret":
        w = BY_NAME["ret"][0]
        return ("fixed", word.encode(w, {}), w.row, {})
    m = re.fullmatch(r"bl\s+([A-Za-z_.$][\w.$]*)", s)
    if m:
        w = BY_NAME["bl"][0]
        sym = m.group(1)
        return ("reloc", word.encode(w, {"I": 0}), 0, R_AARCH64_CALL26, sym, 0, w.row, {"I": sym})
    m = re.fullmatch(r"(b(?:\.(?:eq|ne|hs|cs|lo|cc))?)\s+([A-Za-z_.$][\w.$]*)", s)
    if m:
        w = BY_NAME[BRANCH_ROWS[m.group(1)]][0]
        lbl = m.group(2)
        return ("jump", w, lbl, w.row, {"I": lbl})

    last_err = None
    for w, rx, groups in MATCHERS:
        m = rx.match(s)
        if not m:
            continue
        bind = {}
        ok = True
        for val, (ph, kind) in zip(m.groups(), groups):
            if kind == "g64":
                if val not in G64:
                    ok = False
                    last_err = f"`{val}` is not a general 64-bit register x0..x30 (for `{w.row.asm}`)"
                    break
                bind[ph] = G64[val]
            elif kind == "g32":
                if val not in G32:
                    ok = False
                    last_err = f"`{val}` is not a general 32-bit register w0..w30 (for `{w.row.asm}`)"
                    break
                bind[ph] = G32[val]
            elif kind == "vec":
                n = int(val)
                if not 0 <= n < 32:
                    ok = False
                    last_err = f"vector register v{n} out of range 0..31"
                    break
                bind[ph] = n
            elif kind == "imm":
                n = _num(val)
                if n is None:
                    ok = False
                    break
                bind[ph] = n
            elif kind == "imm_opt":
                if val is None:
                    bind[ph] = 0
                else:
                    n = _num(val)
                    if n is None:
                        ok = False
                        break
                    bind[ph] = n
        if not ok:
            continue
        try:
            raw = word.encode(w, bind)
        except word.Refuse as e:
            last_err = str(e)
            continue
        got = word.decode(ALL_WAYS, raw)
        if got is None or got[0].name != w.row.name:
            raise ValueError(f"arm64.tab does not read back the word written for `{s}`")
        return ("fixed", raw, w.row, bind)
    raise ValueError(f"{last_err or 'no row in arm64.tab matches'}: {s}")


def written(line):
    """Whole registers changed by one AArch64 instruction, read from its row's EFFECT in arm64.tab.
    General registers are returned as `x0`..`x30` or `sp`; vector registers as `v0`..`v31`."""
    item = instruction(line)
    row, bind = item[-2], item[-1]
    regs = set()
    for st in row.effect:
        if st[0] in ("call", "call_link"):
            raise ValueError("a call inside an inline function: not supported yet")
        if st[0] != "set" or st[1][0] != "name":
            continue
        place = st[1][1]
        if place in table.REGISTERS:
            regs.add(bind[place])
        elif place in table.VECTORS:
            regs.add(f"v{bind[place]}")
        else:
            regs.add(place)
    return regs


def build_elf(name, symbol, ins, notes, data, where=None, locs=None):
    """Build a 64-bit little-endian AArch64 ELF object for one function.
    `where`: if given (dict), receives {symbol_or_label: byte_offset_in_text}.
    `locs`: if given (list), receives (byte_offset, byte_len, orig_ins_index) for each emitted instruction."""
    tagged = [(k, s) for k, s in enumerate(ins)]
    entries = []
    has_place = False
    for note in sorted(notes, key=lambda n: -n[1]):
        if note[0] == "place":
            tagged[note[1]:note[1]] = [(None, f".Lode_place_{name}:")]
            has_place = True
        elif note[0] == "at":
            tagged[note[1]:note[1]] = [(None, f"{note[2]}:")]
        else:
            tagged[note[1]:note[1]] = [(None, f"{note[2]}:")]
            entries.append(note[2])
    top_align = 16
    if tagged and tagged[0][1].startswith(".p2align "):
        top_align = max(4, 1 << int(tagged.pop(0)[1].split()[1]))

    items = [(None, "label", symbol)]
    for orig_idx, s in tagged:
        if s.endswith(":"):
            items.append((None, "label", s[:-1]))
        elif s.startswith(".p2align "):
            items.append((None, "align", max(4, 1 << int(s.split()[1]))))
        else:
            it = instruction(s)
            items.append((orig_idx, *it))

    # Pass 1: compute exact byte offsets of all labels (every AArch64 instruction is 4 bytes).
    labels = {}
    pos = 0
    for it in items:
        kind = it[1]
        if kind == "label":
            labels[it[2]] = pos
        elif kind == "align":
            al = it[2]
            pad = (-pos) % al
            if pad % 4:
                raise ValueError(f"AArch64 alignment pad {pad} not a multiple of 4")
            pos += pad
        elif kind in ("fixed", "reloc", "jump"):
            pos += 4

    # Pass 2: emit bytes and resolve internal PC-relative branches.
    code = bytearray()
    relocs = []
    for it in items:
        orig_idx, kind = it[0], it[1]
        if kind == "label":
            assert labels[it[2]] == len(code)
        elif kind == "align":
            al = it[2]
            pad = (-len(code)) % al
            code += NOP_WORD * (pad // 4)
        elif kind == "fixed":
            start = len(code)
            code += it[2]
            if locs is not None and orig_idx is not None:
                locs.append((start, 4, orig_idx))
        elif kind == "reloc":
            start = len(code)
            relocs.append((start + it[3], it[4], it[5], it[6]))
            code += it[2]
            if locs is not None and orig_idx is not None:
                locs.append((start, 4, orig_idx))
        elif kind == "jump":
            start = len(code)
            w_way, lbl = it[2], it[3]
            if lbl not in labels:
                raise ValueError(f"unknown label {lbl}")
            delta = labels[lbl] - start
            raw = word.encode(w_way, {"I": delta})
            got = word.decode(ALL_WAYS, raw)
            if got is None or got[0].name != w_way.row.name:
                raise ValueError(f"arm64.tab does not read back branch to {lbl}")
            code += raw
            if locs is not None and orig_idx is not None:
                locs.append((start, 4, orig_idx))
    if where is not None:
        where.update(labels)

    text_align = max([top_align] + [it[2] for it in items if it[1] == "align"])
    sec_list = [(".text", 1, 6, text_align, 0, bytes(code))]
    if has_place:
        place_bytes = struct.pack("<I", labels[f".Lode_place_{name}"] - labels[symbol])
        sec_list.append((".ode.place", 1, 0, 1, 0, place_bytes))
    sec_list.append((".note.GNU-stack", 1, 0, 1, 0, b""))

    strtab, syms = bytearray(b"\0"), bytearray(24)
    def add_str(s):
        if not s:
            return 0
        at = len(strtab)
        strtab.extend(s.encode() + b"\0")
        return at

    first_global = len(syms) // 24
    sym_index = {}
    for gsym in [symbol] + [e for e in entries if e != symbol]:
        sym_index[gsym] = len(syms) // 24
        syms += struct.pack("<IBBHQQ", add_str(gsym), (1 << 4) | 2, 0, 1, labels[gsym], len(code) - labels[gsym])
    for _, kind, target, _ in relocs:
        if target not in sym_index:
            sym_index[target] = len(syms) // 24
            syms += struct.pack("<IBBHQQ", add_str(target), (1 << 4) | 0, 0, 0, 0, 0)

    rela = bytearray()
    for r_off, kind, target, addend in relocs:
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
        sh_names[sname] = len(shstr)
        shstr.extend(sname.encode() + b"\0")
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
    for h in headers:
        blob += h
    blob[:64] = b"\x7fELF\x02\x01\x01" + bytes(9) + struct.pack("<HHIQQQIHHHHHH", 1, EM_AARCH64, 1, 0, 0, shoff, 0, 64, 0, 0, 64, len(headers), shstrtab_idx)
    return bytes(blob)
