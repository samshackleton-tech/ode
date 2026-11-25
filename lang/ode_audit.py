"""Binary-first auditor (`audit`), hash-bound packager (`pack`), and `.ocl` spec evaluator.

Implements the auditor workflow documented in `docs/ODE-FOR-AUDITORS.md`:
  - Contracts have NO name: their sole identifier is the 52-character lowercase
    RFC 4648 base-32 BLAKE3-256 hash (without padding) of their canonical `.ocl` form (`[a-z2-7]{52}`).
  - Exported FFI linker symbols are bound directly to that hash: `ode_<52-char-b32>`.
  - Canonical `.ocl` bytes are embedded in a non-allocated (`sh_flags = 0`) ELF section
    named `.ode.ocl` inside the binary; `.proof` files remain separate.
  - `audit_binary` checks 100% executable/symbol coverage, rejects startup hooks and extra
    executable sections, validates `.ode.ocl` canonicality and `--expect-contract`, runs
    the Lean 4 verifier `odeverify` directly on the binary's machine-code bytes, and
    reports BOTH 52-character base-32 digests: `BLAKE3(binary)` and `BLAKE3(contract)`.
"""

import hmac
import json
import os
import re
import struct
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for d in (HERE, os.path.join(ROOT, "proof-core"), os.path.join(ROOT, "kcheck"),
          os.path.join(ROOT, "arm64"), os.path.join(ROOT, "core")):
    if d not in sys.path:
        sys.path.insert(0, d)

import ode
import ode_canon
import odec
import prove
import statement
import kdecode
import obj as arm64_obj

EM_X86_64 = 62
EM_AARCH64 = 183

SHT_PROGBITS = 1
SHT_SYMTAB = 2
SHT_STRTAB = 3
SHT_RELA = 4
SHT_INIT_ARRAY = 14
SHT_FINI_ARRAY = 15
SHT_PREINIT_ARRAY = 16

SHF_WRITE = 0x1
SHF_ALLOC = 0x2
SHF_EXECINSTR = 0x4
SHF_INFO_LINK = 0x40

STB_LOCAL = 0
STB_GLOBAL = 1
STB_WEAK = 2

STT_OBJECT = 1
STT_FUNC = 2
STT_SECTION = 3

R_X86_64_PC32 = 2
R_X86_64_PLT32 = 4
R_AARCH64_JUMP26 = 282
R_AARCH64_CALL26 = 283

HELPERS_BEGIN = "=== ode-helpers ==="
PROOF_BEGIN = "=== ode-proof ==="

FORBIDDEN_HOOK_TYPES = frozenset({SHT_INIT_ARRAY, SHT_FINI_ARRAY, SHT_PREINIT_ARRAY})
FORBIDDEN_HOOK_NAMES = frozenset({
    ".init", ".fini", ".init_array", ".fini_array", ".preinit_array", ".ctors", ".dtors",
})
FORBIDDEN_HOOK_PREFIXES = (".init_array.", ".fini_array.", ".preinit_array.", ".ctors.", ".dtors.")

# Standard x86-64 alignment NOP encodings (1..9 bytes) and AArch64 4-byte NOP (`0xd503201f` LE).
_X86_NOPS = (
    b"\x90",
    b"\x66\x90",
    b"\x0f\x1f\x00",
    b"\x0f\x1f\x40\x00",
    b"\x0f\x1f\x44\x00\x00",
    b"\x66\x0f\x1f\x44\x00\x00",
    b"\x0f\x1f\x80\x00\x00\x00\x00",
    b"\x0f\x1f\x84\x00\x00\x00\x00\x00",
    b"\x66\x0f\x1f\x84\x00\x00\x00\x00\x00",
)
_ARM64_NOP = b"\x1f\x20\x03\xd5"


def _up(n, align):
    align = max(align, 1)
    return (n + align - 1) & ~(align - 1)


def _cstr(buf, off):
    if off < 0 or off >= len(buf):
        raise ValueError(f"ELF string offset {off} out of range (len {len(buf)})")
    end = buf.find(b"\x00", off)
    if end < 0:
        raise ValueError(f"unterminated ELF string at offset {off}")
    return buf[off:end].decode("utf-8", errors="replace")


# ---------------------------------------------------------------------------
# ELF64 relocatable parser & surgical builders (x86-64 + AArch64)
# ---------------------------------------------------------------------------

def parse_elf64(data):
    """Parse a little-endian ELF64 relocatable object file."""
    if len(data) < 64 or data[:4] != b"\x7fELF":
        raise ValueError("not an ELF binary (missing 0x7fELF header)")
    if data[4] != 2 or data[5] != 1:
        raise ValueError(f"only little-endian ELF64 is supported (class={data[4]}, data={data[5]})")
    (e_type, e_machine, e_version, _entry, _phoff, e_shoff, _flags, _ehsize,
     _phentsize, _phnum, e_shentsize, e_shnum, e_shstrndx) = struct.unpack_from("<HHIQQQIHHHHHH", data, 16)
    if e_type != 1:
        raise ValueError(f"expected ELF relocatable object (ET_REL=1), got e_type={e_type}")
    if e_machine == EM_X86_64:
        target = "x86-64"
    elif e_machine == EM_AARCH64:
        target = "arm64"
    else:
        raise ValueError(f"unsupported ELF machine {e_machine} (supported: x86-64=62, arm64=183)")
    if e_shentsize != 64 or e_shnum == 0 or e_shoff + e_shentsize * e_shnum > len(data):
        raise ValueError("malformed ELF section header table")
    if e_shstrndx >= e_shnum:
        raise ValueError("malformed ELF shstrtab index")

    raw_secs = []
    for i in range(e_shnum):
        off = e_shoff + i * 64
        fields = struct.unpack_from("<IIQQQQIIQQ", data, off)
        sh_name, sh_type, sh_flags, sh_addr, sh_offset, sh_size, sh_link, sh_info, sh_align, sh_entsize = fields
        body = b"" if sh_type == 8 else data[sh_offset : sh_offset + sh_size]
        if sh_type != 8 and sh_offset + sh_size > len(data):
            raise ValueError(f"ELF section {i} extends past end of file")
        raw_secs.append({
            "idx": i,
            "sh_name": sh_name,
            "type": sh_type,
            "flags": sh_flags,
            "addr": sh_addr,
            "offset": sh_offset,
            "size": sh_size,
            "link": sh_link,
            "info": sh_info,
            "align": sh_align,
            "entsize": sh_entsize,
            "body": body,
        })

    shstr_body = raw_secs[e_shstrndx]["body"]
    by_name = {}
    for s in raw_secs:
        s["name"] = _cstr(shstr_body, s["sh_name"]) if s["idx"] != 0 else ""
        if s["name"]:
            by_name.setdefault(s["name"], []).append(s)

    symbols = []
    symtabs = [s for s in raw_secs if s["type"] == SHT_SYMTAB]
    for st in symtabs:
        if st["link"] >= len(raw_secs):
            raise ValueError("ELF symtab sh_link out of range")
        strtab = raw_secs[st["link"]]["body"]
        if st["size"] % 24 != 0:
            raise ValueError("ELF symtab size is not a multiple of 24")
        for pos in range(0, st["size"], 24):
            st_name, st_info, st_other, st_shndx, st_value, st_size = struct.unpack_from("<IBBHQQ", st["body"], pos)
            symbols.append({
                "index": pos // 24,
                "name": _cstr(strtab, st_name) if st_name else "",
                "bind": st_info >> 4,
                "type": st_info & 0xF,
                "other": st_other,
                "shndx": st_shndx,
                "value": st_value,
                "size": st_size,
            })

    return {
        "machine": e_machine,
        "target": target,
        "shstrndx": e_shstrndx,
        "sections": raw_secs,
        "by_name": by_name,
        "symbols": symbols,
    }


def _rebuild_elf64(machine, shstrndx, sections):
    """Serialize a parsed ELF64 relocatable section list back to valid ELF64 bytes."""
    blob = bytearray(64)
    headers = [bytes(64)]
    for s in sections[1:]:
        align = max(int(s["align"]), 1)
        blob += bytes(_up(len(blob), align) - len(blob))
        soff = len(blob)
        if s["type"] != 8:
            blob += s["body"]
        headers.append(struct.pack(
            "<IIQQQQIIQQ",
            s["sh_name"], s["type"], s["flags"], s["addr"],
            soff, len(s["body"]) if s["type"] != 8 else s["size"],
            s["link"], s["info"], s["align"], s["entsize"],
        ))
    blob += bytes(_up(len(blob), 8) - len(blob))
    shoff = len(blob)
    for h in headers:
        blob += h
    blob[:64] = (
        b"\x7fELF\x02\x01\x01"
        + bytes(9)
        + struct.pack("<HHIQQQIHHHHHH", 1, machine, 1, 0, 0, shoff, 0, 64, 0, 0, 64, len(headers), shstrndx)
    )
    return bytes(blob)


def append_elf_section(elf_bytes, sec_name, sec_bytes, sh_type=SHT_PROGBITS, sh_flags=0, sh_align=1):
    """Append a new section to an ELF64 relocatable `.o` without disturbing any existing section index."""
    parsed = parse_elf64(elf_bytes)
    if sec_name in parsed["by_name"]:
        raise ValueError(f"ELF object already contains section `{sec_name}`")
    secs = [dict(s) for s in parsed["sections"]]
    shstr = secs[parsed["shstrndx"]]
    shstr_body = bytearray(shstr["body"])
    if not shstr_body.endswith(b"\x00"):
        shstr_body.append(0)
    name_off = len(shstr_body)
    shstr_body.extend(sec_name.encode("utf-8") + b"\x00")
    shstr["body"] = bytes(shstr_body)
    shstr["size"] = len(shstr_body)
    secs.append({
        "idx": len(secs),
        "name": sec_name,
        "sh_name": name_off,
        "type": sh_type,
        "flags": sh_flags,
        "addr": 0,
        "offset": 0,
        "size": len(sec_bytes),
        "link": 0,
        "info": 0,
        "align": sh_align,
        "entsize": 0,
        "body": bytes(sec_bytes),
    })
    return _rebuild_elf64(parsed["machine"], parsed["shstrndx"], secs)


def rename_elf_symbol(elf_bytes, old_name, new_name):
    """Rename an exact symbol in an ELF64 relocatable `.o` while leaving `.text` byte-identical."""
    parsed = parse_elf64(elf_bytes)
    secs = [dict(s) for s in parsed["sections"]]
    symtabs = [s for s in secs if s["type"] == SHT_SYMTAB]
    if len(symtabs) != 1:
        raise ValueError(f"expected 1 .symtab section, found {len(symtabs)}")
    st = symtabs[0]
    strtab_sec = secs[st["link"]]
    strtab = bytearray(strtab_sec["body"])
    sym_buf = bytearray(st["body"])
    renamed = 0
    for pos in range(0, len(sym_buf), 24):
        st_name, st_info, st_other, st_shndx, st_value, st_size = struct.unpack_from("<IBBHQQ", sym_buf, pos)
        cur = _cstr(strtab, st_name) if st_name else ""
        if cur == old_name:
            if not strtab.endswith(b"\x00"):
                strtab.append(0)
            new_off = len(strtab)
            strtab.extend(new_name.encode("utf-8") + b"\x00")
            struct.pack_into("<IBBHQQ", sym_buf, pos, new_off, st_info, st_other, st_shndx, st_value, st_size)
            renamed += 1
    if renamed == 0:
        raise ValueError(f"symbol `{old_name}` not found in ELF .symtab")
    st["body"] = bytes(sym_buf)
    st["size"] = len(sym_buf)
    strtab_sec["body"] = bytes(strtab)
    strtab_sec["size"] = len(strtab)
    return _rebuild_elf64(parsed["machine"], parsed["shstrndx"], secs)


def _is_pure_nop_pad(pad, target):
    """Return True iff `pad` is pure alignment NOP padding (and shorter than 16 bytes)."""
    if not pad:
        return True
    if len(pad) >= 16:
        return False
    if target == "arm64":
        return len(pad) % 4 == 0 and pad == _ARM64_NOP * (len(pad) // 4)
    # Greedy match standard Intel/AMD alignment NOPs (1..9 B).
    pos = 0
    while pos < len(pad):
        matched = False
        for nop in sorted(_X86_NOPS, key=len, reverse=True):
            if pad.startswith(nop, pos):
                pos += len(nop)
                matched = True
                break
        if not matched:
            return False
    return True


def _find_odeverify(verify_bin=None):
    cand = verify_bin or os.path.join(ROOT, "proof-core", ".lake", "build", "bin", "odeverify")
    if os.path.isfile(cand) and os.access(cand, os.X_OK):
        return cand
    raise FileNotFoundError(
        f"Lean verifier binary not found at `{cand}`; build it with `cd proof-core && lake build odeverify`"
    )


def format_proof_bundle(order, helper_spec_text, raw_proof_text):
    """Wrap helper contracts/calling lemmas and raw `odeverify` proof lines into one `.proof` file."""
    if len(order) <= 1 and not helper_spec_text.strip():
        return raw_proof_text
    lines = [HELPERS_BEGIN, "order: " + " ".join(order)]
    if helper_spec_text.strip():
        lines.append(helper_spec_text.rstrip("\n"))
    lines.append(PROOF_BEGIN)
    lines.append(raw_proof_text.rstrip("\n"))
    return "\n".join(lines) + "\n"


def split_proof_bundle(proof_text):
    """Split a `.proof` file into `(order_or_None, helper_spec_text, raw_proof_text)`."""
    if not proof_text.startswith(HELPERS_BEGIN + "\n"):
        return None, "", proof_text
    marker = "\n" + PROOF_BEGIN + "\n"
    idx = proof_text.find(marker)
    if idx < 0:
        raise ValueError(f"proof file begins with `{HELPERS_BEGIN}` but lacks `{PROOF_BEGIN}`")
    head = proof_text[len(HELPERS_BEGIN) + 1 : idx]
    raw_proof = proof_text[idx + len(marker) :]
    hlines = head.splitlines()
    if not hlines or not hlines[0].startswith("order:"):
        raise ValueError(f"`{HELPERS_BEGIN}` block must start with `order: sym1 sym2 ...`")
    order = hlines[0][len("order:"):].split()
    if not order:
        raise ValueError("`order:` line in proof file is empty")
    helper_spec = "\n".join(hlines[1:]).strip()
    return order, (helper_spec + "\n" if helper_spec else ""), raw_proof


def _called_symbols(elf_bytes):
    """Return ordered list of called function symbol names referenced by `.rela.text`."""
    elf = parse_elf64(elf_bytes)
    text_secs = elf["by_name"].get(".text", [])
    if not text_secs:
        return []
    text_idx = text_secs[0]["idx"]
    ro_secs = elf["by_name"].get(".rodata", [])
    ro_idx = ro_secs[0]["idx"] if ro_secs else -1
    syms = elf["symbols"]
    called = []
    seen = set()
    for s in elf["sections"]:
        if s["type"] == SHT_RELA and s["info"] == text_idx:
            for pos in range(0, len(s["body"]), 24):
                _off, r_info, _add = struct.unpack_from("<QQq", s["body"], pos)
                r_type = r_info & 0xFFFFFFFF
                rsym = syms[r_info >> 32]
                is_call = (
                    r_type in (R_X86_64_PLT32, R_AARCH64_CALL26, R_AARCH64_JUMP26)
                    or (r_type == R_X86_64_PC32 and rsym["shndx"] != ro_idx)
                )
                if is_call and rsym["name"] and rsym["name"] not in seen:
                    seen.add(rsym["name"])
                    called.append(rsym["name"])
    return called


def merge_elf_objects(units, target, rename_map, export_sym, embedded_ocl_bytes=None):
    """Merge relocatable ELF64 `.o` byte blobs into one clean relocatable ELF64 `.o` (pure Python).

    - `.text` packs all units with 16-byte pure-NOP alignment (pad strictly < 16 bytes).
    - `.rodata` (if any) is kept strictly non-executable (`SHF_ALLOC`, 64-byte aligned).
    - `.symtab` places all `STB_LOCAL` symbols first (section symbol + local `STT_FUNC` helpers),
      followed by the single `STB_GLOBAL` `STT_FUNC` exported symbol `export_sym`.
    - Zero `SHN_UNDEF` symbols remain; any call targeting a symbol outside `rename_map` is refused.
    - If `embedded_ocl_bytes` is provided, appends non-allocated `.ode.ocl` (`sh_flags = 0`).
    """
    if target == "x86-64":
        machine = EM_X86_64
        nop_unit = b"\x90"
    elif target == "arm64":
        machine = EM_AARCH64
        nop_unit = _ARM64_NOP
    else:
        raise ValueError(f"unsupported target `{target}` for ELF merge")

    merged_text = bytearray()
    merged_rodata = bytearray()
    defined_funcs = {}  # new_name -> (text_off, st_size, is_global)
    local_order = []
    reloc_recs = []     # ("rodata", off, rtype, addend) | ("call", off, rtype, new_tgt, addend)

    for u_bytes in units:
        elf = parse_elf64(u_bytes)
        if elf["target"] != target:
            raise ValueError(f"ELF target mismatch during merge: expected {target}, got {elf['target']}")
        text_secs = elf["by_name"].get(".text", [])
        if len(text_secs) != 1 or text_secs[0]["size"] == 0:
            raise ValueError("input ELF unit lacks a single non-empty `.text` section")
        tsec = text_secs[0]
        t_idx = tsec["idx"]

        # Align `.text` to 16 bytes with pure NOPs (pad is always 0..15 bytes).
        pad_len = (-len(merged_text)) % 16
        if pad_len:
            if pad_len % len(nop_unit) != 0:
                raise ValueError(f"alignment pad {pad_len} is not a multiple of instruction width")
            merged_text += nop_unit * (pad_len // len(nop_unit))
        text_base = len(merged_text)
        merged_text += tsec["body"]

        ro_secs = elf["by_name"].get(".rodata", [])
        ro_idx = -1
        ro_base = 0
        if ro_secs:
            if len(ro_secs) != 1:
                raise ValueError("input ELF unit has multiple `.rodata` sections")
            rsec = ro_secs[0]
            ro_idx = rsec["idx"]
            ro_pad = (-len(merged_rodata)) % 64
            if ro_pad:
                merged_rodata += bytes(ro_pad)
            ro_base = len(merged_rodata)
            merged_rodata += rsec["body"]

        syms = elf["symbols"]
        for sym in syms:
            if sym["shndx"] == t_idx and sym["name"] and sym["type"] in (0, STT_FUNC):
                orig = sym["name"]
                if orig not in rename_map:
                    raise ValueError(f"input ELF defines symbol `{orig}` absent from rename_map")
                new_nm = rename_map[orig]
                if new_nm in defined_funcs:
                    raise ValueError(f"duplicate merged function symbol `{new_nm}`")
                is_glob = (new_nm == export_sym)
                defined_funcs[new_nm] = (text_base + sym["value"], sym["size"], is_glob)
                if not is_glob:
                    local_order.append(new_nm)

        for s in elf["sections"]:
            if s["type"] == SHT_RELA and s["info"] == t_idx:
                for pos in range(0, len(s["body"]), 24):
                    r_off, r_info, r_addend = struct.unpack_from("<QQq", s["body"], pos)
                    r_type = r_info & 0xFFFFFFFF
                    rsym = syms[r_info >> 32]
                    if r_type == R_X86_64_PC32 and ro_idx >= 0 and rsym["shndx"] == ro_idx:
                        reloc_recs.append(("rodata", text_base + r_off, R_X86_64_PC32, ro_base + rsym["value"] + r_addend))
                    elif (
                        r_type in (R_X86_64_PLT32, R_AARCH64_CALL26, R_AARCH64_JUMP26)
                        or (r_type == R_X86_64_PC32 and rsym["shndx"] == 0)
                    ):
                        orig_tgt = rsym["name"]
                        if orig_tgt not in rename_map:
                            raise ValueError(
                                f"call to external symbol `{orig_tgt}` is missing from this bundle"
                            )
                        reloc_recs.append(("call", text_base + r_off, r_type, rename_map[orig_tgt], r_addend))
                    else:
                        raise ValueError(f"unsupported relocation type {r_type} to `{rsym['name']}`")

    if export_sym not in defined_funcs:
        raise ValueError(f"exported symbol `{export_sym}` was not defined by any input ELF unit")

    # Assemble clean sections: .text, [.rodata], .note.GNU-stack, [.rela.text], .symtab, .strtab, .shstrtab, [.ode.ocl]
    sec_list = [(".text", SHT_PROGBITS, SHF_ALLOC | SHF_EXECINSTR, 16, 0, bytes(merged_text))]
    rodata_sec_idx = None
    if merged_rodata:
        rodata_sec_idx = len(sec_list) + 1
        sec_list.append((".rodata", SHT_PROGBITS, SHF_ALLOC, 64, 0, bytes(merged_rodata)))
    sec_list.append((".note.GNU-stack", SHT_PROGBITS, 0, 1, 0, b""))

    strtab = bytearray(b"\x00")
    syms_buf = bytearray(24)  # index 0: STN_UNDEF
    def add_str(nm):
        if not nm:
            return 0
        off = len(strtab)
        strtab.extend(nm.encode("utf-8") + b"\x00")
        return off

    rodata_sym_idx = None
    if rodata_sec_idx is not None:
        rodata_sym_idx = len(syms_buf) // 24
        syms_buf += struct.pack("<IBBHQQ", 0, (STB_LOCAL << 4) | STT_SECTION, 0, rodata_sec_idx, 0, 0)

    sym_idx = {}
    for nm in local_order:
        val, sz, _ = defined_funcs[nm]
        sym_idx[nm] = len(syms_buf) // 24
        syms_buf += struct.pack("<IBBHQQ", add_str(nm), (STB_LOCAL << 4) | STT_FUNC, 0, 1, val, sz)

    first_global = len(syms_buf) // 24
    exp_val, exp_sz, _ = defined_funcs[export_sym]
    sym_idx[export_sym] = first_global
    syms_buf += struct.pack("<IBBHQQ", add_str(export_sym), (STB_GLOBAL << 4) | STT_FUNC, 0, 1, exp_val, exp_sz)

    rela_buf = bytearray()
    for rec in reloc_recs:
        if rec[0] == "rodata":
            _, r_off, r_type, r_add = rec
            rela_buf += struct.pack("<QQq", r_off, (rodata_sym_idx << 32) | r_type, r_add)
        else:
            _, r_off, r_type, tgt_nm, r_add = rec
            if tgt_nm not in sym_idx:
                raise ValueError(f"call target `{tgt_nm}` not defined in merged ELF")
            rela_buf += struct.pack("<QQq", r_off, (sym_idx[tgt_nm] << 32) | r_type, r_add)

    rela_sec_idx = None
    if rela_buf:
        rela_sec_idx = len(sec_list) + 1
        sec_list.append((".rela.text", SHT_RELA, SHF_INFO_LINK, 8, 24, bytes(rela_buf)))

    symtab_sec_idx = len(sec_list) + 1
    strtab_sec_idx = symtab_sec_idx + 1
    shstrtab_sec_idx = strtab_sec_idx + 1
    sec_list.append((".symtab", SHT_SYMTAB, 0, 8, 24, bytes(syms_buf)))
    sec_list.append((".strtab", SHT_STRTAB, 0, 1, 0, bytes(strtab)))

    extra_names = [".shstrtab"]
    if embedded_ocl_bytes is not None:
        extra_names.append(".ode.ocl")
    shstr = bytearray(b"\x00")
    sh_names = {}
    for sname in [x[0] for x in sec_list] + extra_names:
        sh_names[sname] = len(shstr)
        shstr.extend(sname.encode("utf-8") + b"\x00")
    sec_list.append((".shstrtab", SHT_STRTAB, 0, 1, 0, bytes(shstr)))
    if embedded_ocl_bytes is not None:
        sec_list.append((".ode.ocl", SHT_PROGBITS, 0, 1, 0, bytes(embedded_ocl_bytes)))

    blob = bytearray(64)
    headers = [bytes(64)]
    for idx, (sname, stype, sflags, salign, sentsize, sbytes) in enumerate(sec_list, 1):
        blob += bytes(_up(len(blob), max(salign, 1)) - len(blob))
        soff = len(blob)
        blob += sbytes
        slink = symtab_sec_idx if idx == rela_sec_idx else (strtab_sec_idx if idx == symtab_sec_idx else 0)
        sinfo = 1 if idx == rela_sec_idx else (first_global if idx == symtab_sec_idx else 0)
        headers.append(struct.pack(
            "<IIQQQQIIQQ",
            sh_names[sname], stype, sflags, 0, soff, len(sbytes), slink, sinfo, salign, sentsize,
        ))
    blob += bytes(_up(len(blob), 8) - len(blob))
    shoff = len(blob)
    for h in headers:
        blob += h
    blob[:64] = (
        b"\x7fELF\x02\x01\x01"
        + bytes(9)
        + struct.pack("<HHIQQQIHHHHHH", 1, machine, 1, 0, 0, shoff, 0, 64, 0, 0, 64, len(headers), shstrtab_sec_idx)
    )
    return bytes(blob)


# ---------------------------------------------------------------------------
# Binary-first auditor (`ode_tool.py audit`)
# ---------------------------------------------------------------------------

def audit_binary(
    bin_path,
    proof_path=None,
    expect_contract=None,
    contract_path=None,
    verify_bin=None,
):
    """Audit a compiled ELF64 binary directly against its canonical `.ocl` contract and separate `.proof`.

    Supports both single-function `.o` files and multi-function `.o` bundles containing `STB_LOCAL`
    callees whose contracts and custom `calling` conventions travel inside `.proof`. When
    `proof_path` is omitted on a single-function binary, tries auto-proving loop-free code and
    verifies the result with `odeverify`.
    """
    errors = []
    if not os.path.isfile(bin_path):
        return {"verdict": "refused", "errors": [f"binary not found: {bin_path}"]}
    with open(bin_path, "rb") as f:
        bin_bytes = f.read()
    binary_b32 = ode_canon.blake3_b32(bin_bytes)

    res = {
        "binary": bin_path,
        "binary_b32": binary_b32,
        "contract_b32": None,
        "symbol": None,
        "target": None,
        "contract_source": None,
        "canonical_ocl": None,
        "coverage": {},
        "verdict": "refused",
        "errors": errors,
    }

    # 1. Validate --expect-contract format upfront (refuse truncated prefixes loudly!).
    if expect_contract is not None:
        if not ode_canon.B32_RE.fullmatch(expect_contract):
            errors.append(
                f"--expect-contract must be a full 52-character lowercase base-32 BLAKE3 digest "
                f"([a-z2-7]{{52}}), got {expect_contract!r} (len {len(expect_contract)})"
            )
            return res

    # 2. Parse ELF64 structure.
    try:
        elf = parse_elf64(bin_bytes)
    except ValueError as exc:
        errors.append(f"ELF parse error: {exc}")
        return res
    target = elf["target"]
    res["target"] = target

    # 3. Reject startup/teardown hooks and extra executable sections.
    for s in elf["sections"][1:]:
        nm = s["name"]
        if (
            s["type"] in FORBIDDEN_HOOK_TYPES
            or nm in FORBIDDEN_HOOK_NAMES
            or any(nm.startswith(pfx) for pfx in FORBIDDEN_HOOK_PREFIXES)
        ):
            errors.append(f"forbidden startup/teardown hook section `{nm}` (type={s['type']}, size={s['size']})")
        if (s["flags"] & SHF_EXECINSTR) and nm != ".text":
            errors.append(f"unexpected executable section `{nm}` outside `.text` (size={s['size']})")

    text_secs = elf["by_name"].get(".text", [])
    if len(text_secs) != 1 or text_secs[0]["size"] == 0:
        errors.append(f"expected exactly 1 non-empty `.text` section, found {len(text_secs)}")
        return res
    text_sec = text_secs[0]
    text_idx = text_sec["idx"]
    text_bytes = text_sec["body"]

    # 4. Extract & validate `.ode.ocl` (and/or `--contract`).
    ocl_secs = elf["by_name"].get(".ode.ocl", [])
    if len(ocl_secs) > 1:
        errors.append(f"multiple `.ode.ocl` sections ({len(ocl_secs)}) are forbidden")
        return res
    embedded_ocl = None
    embedded_b32 = None
    if ocl_secs:
        os_sec = ocl_secs[0]
        if os_sec["flags"] != 0:
            errors.append(f"`.ode.ocl` section must be non-allocated/non-executable (sh_flags=0), got 0x{os_sec['flags']:x}")
        try:
            embedded_ocl = os_sec["body"].decode("utf-8")
        except UnicodeDecodeError as exc:
            errors.append(f"`.ode.ocl` is not valid UTF-8: {exc}")
            return res
        if not ode_canon.is_canonical(embedded_ocl):
            errors.append("`.ode.ocl` is not in canonical form (contains comments, author names, unused defs, or non-canonical formatting)")
            return res
        embedded_b32 = ode_canon.blake3_b32(embedded_ocl.encode("utf-8"))

    ext_ocl = None
    ext_b32 = None
    if contract_path is not None:
        if not os.path.isfile(contract_path):
            errors.append(f"contract file not found: {contract_path}")
            return res
        with open(contract_path, "r", encoding="utf-8") as f:
            raw_ext = f.read()
        try:
            ext_info = ode_canon.canonicalize(raw_ext)
            ode_canon.check_ocl_filename(contract_path, ext_info["contract_id"])
        except Exception as exc:
            errors.append(f"failed to canonicalize `--contract {contract_path}`: {exc}")
            return res
        ext_ocl = ext_info["canonical"]
        ext_b32 = ext_info["contract_id"]

    if embedded_ocl is not None and ext_ocl is not None:
        if not hmac.compare_digest(embedded_b32, ext_b32):
            errors.append(
                f"contract mismatch: embedded `.ode.ocl` is {embedded_b32} but `--contract` is {ext_b32}"
            )
            return res
        canonical_ocl = embedded_ocl
        contract_b32 = embedded_b32
        res["contract_source"] = "embedded .ode.ocl (matched --contract)"
    elif embedded_ocl is not None:
        canonical_ocl = embedded_ocl
        contract_b32 = embedded_b32
        res["contract_source"] = "embedded .ode.ocl"
    elif ext_ocl is not None:
        canonical_ocl = ext_ocl
        contract_b32 = ext_b32
        res["contract_source"] = f"external {contract_path}"
    else:
        errors.append("binary has no embedded `.ode.ocl` section and no `--contract` file was provided")
        return res

    res["contract_b32"] = contract_b32
    res["canonical_ocl"] = canonical_ocl

    # 5. Compare against --expect-contract if supplied.
    if expect_contract is not None and not hmac.compare_digest(expect_contract, contract_b32):
        errors.append(
            f"contract hash mismatch: expected {expect_contract}, binary carries {contract_b32}"
        )
        return res

    # 6. Check exported, local, and undefined symbols (100% symbol coverage + hash-bound symbol rule).
    defined_exports = [
        sym for sym in elf["symbols"]
        if sym["bind"] in (STB_GLOBAL, STB_WEAK) and sym["shndx"] != 0
    ]
    if len(defined_exports) != 1:
        names = [s["name"] for s in defined_exports]
        errors.append(f"expected exactly 1 exported symbol, found {len(defined_exports)}: {names}")
        return res
    exp = defined_exports[0]
    exp_sym = exp["name"]
    res["symbol"] = exp_sym
    if exp["shndx"] != text_idx or exp["type"] != STT_FUNC:
        errors.append(f"exported symbol `{exp_sym}` is not a `.text` function (shndx={exp['shndx']}, type={exp['type']})")
    expected_hash_sym = ode_canon.ode_symbol(contract_b32)
    if embedded_ocl is not None and exp_sym != expected_hash_sym:
        errors.append(
            f"exported symbol `{exp_sym}` does not match canonical contract hash symbol `{expected_hash_sym}`"
        )

    undef_syms = [
        sym["name"] for sym in elf["symbols"]
        if sym["index"] != 0 and sym["shndx"] == 0
    ]
    if undef_syms:
        errors.append(f"binary has external undefined symbol(s) outside verified `.text`: {undef_syms}")

    local_funcs = {}
    for sym in elf["symbols"]:
        if sym["bind"] == STB_LOCAL and sym["shndx"] == text_idx:
            if sym["type"] == STT_SECTION:
                continue
            if sym["type"] != STT_FUNC or not sym["name"]:
                errors.append(f"non-function local symbol `{sym['name']}` in `.text` (type={sym['type']})")
                continue
            if sym["name"] == exp_sym or sym["name"] in local_funcs:
                errors.append(f"duplicate local function symbol `{sym['name']}` in `.text`")
                continue
            local_funcs[sym["name"]] = sym

    if errors:
        return res

    # 7. Parse `.proof` (or auto-prove loop-free single-function binary when `--proof` is omitted).
    bound_spec = ode_canon.bind_symbol(canonical_ocl, exp_sym)
    auto_proved = False
    raw_proof_text = None
    if proof_path is None:
        if local_funcs:
            errors.append(
                f"multi-function binary has {len(local_funcs)} local helper function(s) "
                f"({sorted(local_funcs)}); pass `--proof FILE`"
            )
            return res
        order = [exp_sym]
        combined_spec = bound_spec
        auto_proved = True
    else:
        if not os.path.isfile(proof_path):
            errors.append(f"proof file not found: {proof_path}")
            return res
        with open(proof_path, "r", encoding="utf-8") as pf:
            proof_text = pf.read()
        try:
            p_order, helper_spec, raw_proof_text = split_proof_bundle(proof_text)
        except ValueError as exc:
            errors.append(f"malformed proof file: {exc}")
            return res
        if local_funcs:
            if p_order is None:
                errors.append(
                    f"extra local function symbol(s) in `.text` with no helper proof block: {sorted(local_funcs)}"
                )
                return res
            if len(p_order) != len(set(p_order)):
                errors.append(f"duplicate symbol in proof `order:` line: {p_order}")
                return res
            if p_order[-1] != exp_sym:
                errors.append(
                    f"proof `order:` must end with exported symbol `{exp_sym}`, got `{p_order[-1]}`"
                )
                return res
            if set(p_order[:-1]) != set(local_funcs.keys()):
                missing = sorted(set(local_funcs.keys()) - set(p_order[:-1]))
                extra = sorted(set(p_order[:-1]) - set(local_funcs.keys()))
                errors.append(
                    f"local function set mismatch between `.text` and `.proof` "
                    f"(missing from proof={missing}, absent from `.text`={extra})"
                )
                return res
            try:
                checked_sp = ode.with_proof(bound_spec, helper_spec)
            except BaseException as exc:
                errors.append(f"helper specification in `.proof` refused: {exc}")
                return res
            for hsym in p_order[:-1]:
                if hsym not in checked_sp.contracts:
                    errors.append(f"helper specification in `.proof` lacks a contract for `{hsym}`")
                    return res
            order = p_order
            combined_spec = bound_spec + "\n" + helper_spec
        else:
            if p_order is not None:
                if p_order != [exp_sym] or helper_spec.strip():
                    errors.append(f"single-function binary cannot carry extra helper proof entries: {p_order}")
                    return res
            order = [exp_sym]
            combined_spec = bound_spec

    # 8. Decode EVERY function in `order` and enforce 100% `.text` executable-byte coverage.
    sym_by_name = dict(local_funcs)
    sym_by_name[exp_sym] = exp
    spans = []
    for fn_sym in order:
        try:
            if target == "arm64":
                rows = arm64_obj.read(bin_path, fn_sym)
            else:
                rows, _ = kdecode.read(bin_path, fn_sym, 0, 0)
        except BaseException as exc:
            errors.append(f"instruction decode failed for `{fn_sym}`: {exc}")
            return res
        if not rows:
            errors.append(f"no instructions decoded for `{fn_sym}`")
            return res
        if rows[0][0] != 0:
            errors.append(f"first decoded instruction of `{fn_sym}` starts at offset {rows[0][0]} != 0")
            return res
        for idx in range(len(rows) - 1):
            if rows[idx][1] != rows[idx + 1][0]:
                errors.append(
                    f"gap in decoded `.text` of `{fn_sym}` between bytes {rows[idx][1]} and {rows[idx + 1][0]}"
                )
                return res
        start = sym_by_name[fn_sym]["value"]
        span_len = rows[-1][1]
        end = start + span_len
        if end > len(text_bytes):
            errors.append(f"decoded span of `{fn_sym}` ({start}..{end}) extends past `.text` ({len(text_bytes)})")
            return res
        if sym_by_name[fn_sym]["size"] and sym_by_name[fn_sym]["size"] < span_len:
            errors.append(
                f"symbol `{fn_sym}` size {sym_by_name[fn_sym]['size']} is smaller than decoded span {span_len}"
            )
            return res
        spans.append((start, end, fn_sym, rows))

    spans.sort(key=lambda item: (item[0], -item[1]))
    if spans[0][0] != 0:
        errors.append(f"first function `{spans[0][2]}` starts at `.text` offset {spans[0][0]} != 0 (extra leading bytes)")
        return res

    covered_end = 0
    covered_insn_starts = set()
    for start, end, fn_sym, rows in spans:
        if start >= covered_end:
            gap = text_bytes[covered_end:start]
            if not _is_pure_nop_pad(gap, target):
                errors.append(
                    f"extra non-NOP bytes in `.text` between offset {covered_end} and `{fn_sym}` ({start}): "
                    f"{len(gap)} bytes ({gap[:16].hex()})"
                )
                return res
            for a, _, _ in rows:
                covered_insn_starts.add(start + a)
            covered_end = end
        else:
            # Shared-tail secondary entry point (e.g. `p32` inside `k32`): must begin at a decoded
            # instruction boundary inside the enclosing span and end at the exact same address.
            if start not in covered_insn_starts or end != covered_end:
                errors.append(
                    f"overlapping `.text` span for `{fn_sym}` ({start}..{end}) does not share an instruction-aligned tail (covered_end={covered_end})"
                )
                return res

    tail = text_bytes[covered_end:]
    if not _is_pure_nop_pad(tail, target):
        errors.append(
            f"extra trailing executable bytes in `.text` after offset {covered_end}: "
            f"{len(tail)} bytes ({tail[:16].hex()})"
        )
        return res

    res["coverage"] = {
        "functions": len(order),
        "local_helpers": len(order) - 1,
        "instructions": len(covered_insn_starts),
        "code_bytes": covered_end,
        "text_bytes": len(text_bytes),
        "exported_symbols": 1,
        "hooks": 0,
    }

    # 9. Invoke Lean 4 `odeverify` directly on ALL functions in topological order!
    try:
        verifier = _find_odeverify(verify_bin)
    except FileNotFoundError as exc:
        errors.append(str(exc))
        return res

    with tempfile.TemporaryDirectory(prefix="ode_audit_") as tmp:
        stmt_path = os.path.join(tmp, "audit.statement")
        if auto_proved:
            auto_proof_path = os.path.join(tmp, "auto.proof")
            try:
                prove.prove(combined_spec, [(bin_path, exp_sym, "")], stmt_path, auto_proof_path)
            except BaseException as exc:
                errors.append(f"auto-proving failed (pass `--proof FILE` for functions with loops or hints): {exc}")
                return res
            verify_proof_path = auto_proof_path
            with open(stmt_path, "r", encoding="utf-8") as sf:
                stmt_lines = sf.read().splitlines()
        else:
            try:
                stmt_lines = statement.statement(combined_spec, [(bin_path, s) for s in order])
            except BaseException as exc:
                errors.append(f"statement build failed: {exc}")
                return res
            with open(stmt_path, "w", encoding="utf-8") as f:
                f.write("\n".join(stmt_lines) + "\n")
            verify_proof_path = os.path.join(tmp, "audit.proof")
            with open(verify_proof_path, "w", encoding="utf-8") as pf:
                pf.write(raw_proof_text)
        table_path = statement.table_of(stmt_lines)
        proc = subprocess.run(
            [verifier, table_path, stmt_path, verify_proof_path],
            capture_output=True,
            text=True,
            check=False,
        )
        out_txt = (proc.stdout + proc.stderr).strip()
        res["verifier_output"] = out_txt
        if proc.returncode != 0 or not out_txt.startswith("shown"):
            errors.append(f"odeverify refused (rc={proc.returncode}): {out_txt}")
            return res

    res["verdict"] = "shown"
    if auto_proved:
        res["auto_proved"] = True
    return res


def format_audit_report(res, show_contract=False, glossary=None):
    """Format a clean auditor-facing report matching `docs/ODE-FOR-AUDITORS.md`."""
    lines = [f"BINARY:   {res.get('binary', '?')}"]
    if res.get("binary_b32"):
        lines.append(f"  BLAKE3(binary):    {res['binary_b32']}")
    if res.get("contract_b32"):
        lines.append(f"  BLAKE3(contract):  {res['contract_b32']}  ({res.get('contract_source', '')})")
    if res.get("symbol"):
        lines.append(f"  SYMBOL:            {res['symbol']}")
    cov = res.get("coverage") or {}
    if cov:
        n_fn = cov["functions"]
        n_loc = cov.get("local_helpers", 0)
        fn_desc = (
            f"{n_fn} functions (1 exported, {n_loc} local)"
            if n_loc
            else f"{n_fn} function"
        )
        lines.append(
            f"  COVERAGE:          100% of executable code "
            f"({fn_desc}, {cov['instructions']} instructions, "
            f"{cov['code_bytes']} B, {cov['exported_symbols']} exported symbol, {cov['hooks']} hooks)"
        )
    lines.append(f"  VERDICT:           {res['verdict']}")
    for err in res.get("errors") or ():
        lines.append(f"  ERROR:             {err}")
    if show_contract and res.get("canonical_ocl"):
        lines.append("")
        if glossary:
            lines.append("--- CONTRACT (rendered with local glossary; hash is of canonical form) ---")
            lines.append(ode_canon.render_with_glossary(res["canonical_ocl"], glossary).rstrip())
        else:
            lines.append("--- CANONICAL CONTRACT (.ocl) ---")
            lines.append(res["canonical_ocl"].rstrip())
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Hash-bound builder (`ode_tool.py pack`) & multi-object bundler
# ---------------------------------------------------------------------------

def _map_places_text(pl_text, canon_glossary, orig_sym, new_sym, is_export):
    """Remap specification definition (and, for export, parameter) names inside loop place hints.

    Avoids alpha-capture when a loop's local `name X = REG` variable has the same name as a
    canonical target name (such as `a0..a3`, `f0..`, `C0..`) or an original mapped identifier.
    """
    if not pl_text:
        return ""
    import re as _re
    inv_map = {}
    for can, orig in canon_glossary.items():
        if can == "contract" or "." in can:
            continue
        if is_export or can[0] in ("C", "f", "s", "L"):
            inv_map[orig] = can
    inv_map[orig_sym] = new_sym
    if not inv_map:
        return pl_text

    # Collect local `place` binder names (`name VAR = REG`).
    name_line_re = _re.compile(r"^(\s*name\s+)([A-Za-z_][A-Za-z_0-9]*)(\s*=\s*.*)$")
    local_names = []
    for line in pl_text.splitlines():
        m = name_line_re.match(line)
        if m and m.group(2) not in local_names:
            local_names.append(m.group(2))

    # Alpha-rename any local binder that collides with a canonical output name or mapped key.
    reserved = set(local_names) | set(inv_map.keys()) | set(inv_map.values())
    local_rename = {}
    fresh_idx = 0
    for v in local_names:
        if v in inv_map or v in inv_map.values():
            while f"ode_p{fresh_idx}" in reserved:
                fresh_idx += 1
            fresh = f"ode_p{fresh_idx}"
            fresh_idx += 1
            local_rename[v] = fresh
            reserved.add(fresh)

    # Single-pass simultaneous substitution per line (leaving register names on `name VAR = REG` untouched).
    local_set = set(local_names)
    all_keys = sorted(set(inv_map.keys()) | set(local_rename.keys()) | local_set, key=len, reverse=True)
    pat = _re.compile(r"\b(" + "|".join(_re.escape(k) for k in all_keys) + r")\b")

    def subst_expr(s):
        def repl(m):
            tok = m.group(1)
            if tok in local_rename:
                return local_rename[tok]
            if tok in local_set:
                return tok
            return inv_map.get(tok, tok)
        return pat.sub(repl, s)

    out_lines = []
    for line in pl_text.splitlines():
        m = name_line_re.match(line)
        if m:
            v = m.group(2)
            out_lines.append(f"{m.group(1)}{local_rename.get(v, v)}{m.group(3)}")
        elif line.lstrip().startswith(("keep ", "at ")):
            out_lines.append(line)
        else:
            out_lines.append(subst_expr(line))
    return "\n".join(out_lines) + ("\n" if pl_text.endswith("\n") else "")


class PackProofError(SystemExit):
    """Structured prover refusal raised by `pack_verified` / `pack_bundle`, preserving exact
    original function name, bytecode offset, compile `line_map`, contract, and spec text."""

    def __init__(self, message, *, fn_sym=None, pc=None, reason="", info=None,
                 contract=None, spec_text=None, target="x86_64"):
        super().__init__(message)
        self.fn_sym = fn_sym
        self.pc = pc
        self.reason = reason
        self.info = info
        self.contract = contract
        self.spec_text = spec_text
        self.target = target


def _raise_pack_proof_error(exc, stmt_path, proof_path, inv_rename, compiled_by_sym, full_spec_text, target):
    """Locate the exact failing function & PC while `stmt_path` is still on disk and raise `PackProofError`."""
    pc, can_sym, loc_msg = prove.locate(stmt_path, proof_path)
    orig_sym = inv_rename.get(can_sym, can_sym)
    msg = str(exc)
    if orig_sym is None:
        m = re.search(r"no proof of (\S+) found", msg)
        if m:
            orig_sym = inv_rename.get(m.group(1), m.group(1))
    reason = loc_msg or msg
    info = compiled_by_sym.get(orig_sym) if (compiled_by_sym and orig_sym) else None
    contract = None
    if full_spec_text and orig_sym:
        try:
            sp = ode.Spec(full_spec_text)
            contract = sp.contracts.get(orig_sym)
        except Exception:
            contract = None
    raise PackProofError(
        msg, fn_sym=orig_sym, pc=pc, reason=reason, info=info,
        contract=contract, spec_text=full_spec_text, target=target,
    ) from exc


def pack_bundle(
    unit_elfs,
    orig_order,
    export_orig_sym,
    full_spec_text,
    out_obj,
    out_proof,
    places_by_sym=None,
    existing_proof_path=None,
    glossary_out=None,
    verify_bin=None,
    compiled_by_sym=None,
):
    """Pack a pre-compiled multi-function set of relocatable ELF64 `.o` blobs into one hash-bound
    `.o` + self-contained `.proof`, and run Bob's full `audit_binary`.

    - `orig_order`: topological list of original symbol names ending in `export_orig_sym`.
    - `existing_proof_path`: optional pre-built `odeverify` proof file for `orig_order`; when given,
      remaps its symbols/definitions instead of re-running the prover from scratch.
    """
    if not orig_order or orig_order[-1] != export_orig_sym:
        raise ValueError(f"orig_order must end with exported symbol `{export_orig_sym}`")
    target = parse_elf64(unit_elfs[0])["target"]
    canon = ode_canon.canonicalize(full_spec_text, contract_name=export_orig_sym)
    cid = canon["contract_id"]
    hash_sym = canon["symbol"]

    rename_map = {}
    helper_rename = {}
    for idx, orig in enumerate(orig_order[:-1]):
        hnm = f"h{idx}"
        rename_map[orig] = hnm
        helper_rename[orig] = hnm
    rename_map[export_orig_sym] = hash_sym
    new_order = [rename_map[s] for s in orig_order]

    obj_bytes = merge_elf_objects(
        unit_elfs, target, rename_map, hash_sym,
        embedded_ocl_bytes=canon["canonical"].encode("utf-8"),
    )
    os.makedirs(os.path.dirname(os.path.abspath(out_obj)), exist_ok=True)
    with open(out_obj, "wb") as f:
        f.write(obj_bytes)

    bound_spec = ode_canon.bind_symbol(canon["canonical"], hash_sym)
    helper_spec, top_map = ode_canon.build_helper_spec(full_spec_text, export_orig_sym, helper_rename, canon)
    # Validate disjointness via `ode.with_proof` immediately.
    if helper_rename:
        ode.with_proof(bound_spec, helper_spec)
    combined_spec = bound_spec + ("\n" + helper_spec if helper_spec else "")

    os.makedirs(os.path.dirname(os.path.abspath(out_proof)), exist_ok=True)
    if existing_proof_path is not None:
        with open(existing_proof_path, "r", encoding="utf-8") as pf:
            orig_proof = pf.read()
        export_param_map = {
            orig: can for can, orig in canon["glossary"].items()
            if can != "contract" and "." not in can and can[0] == "a"
        }
        raw_proof = ode_canon.remap_proof_text(
            orig_proof, rename_map, top_map, export_orig_sym, hash_sym, export_param_map,
        )
    else:
        places_by_sym = places_by_sym or {}
        prove_items = []
        for orig in orig_order:
            new_nm = rename_map[orig]
            pl = _map_places_text(
                places_by_sym.get(orig, ""), canon["glossary"], orig, new_nm, orig == export_orig_sym,
            )
            prove_items.append((out_obj, new_nm, pl))
        with tempfile.TemporaryDirectory(prefix="ode_bundle_") as tmp:
            stmt_path = os.path.join(tmp, "bundle.statement")
            raw_path = os.path.join(tmp, "bundle.raw.proof")
            try:
                prove.prove(combined_spec, prove_items, stmt_path, raw_path)
            except SystemExit as exc:
                inv_rename = {v: k for k, v in rename_map.items()}
                _raise_pack_proof_error(exc, stmt_path, raw_path, inv_rename, compiled_by_sym, full_spec_text, target)
            with open(raw_path, "r", encoding="utf-8") as rf:
                raw_proof = rf.read()

    bundle_proof = format_proof_bundle(new_order, helper_spec, raw_proof)
    with open(out_proof, "w", encoding="utf-8") as pf:
        pf.write(bundle_proof)

    if glossary_out:
        os.makedirs(os.path.dirname(os.path.abspath(glossary_out)), exist_ok=True)
        with open(glossary_out, "w", encoding="utf-8") as f:
            json.dump({"contract_id": cid, "glossary": canon["glossary"]}, f, indent=2, sort_keys=True)
            f.write("\n")

    audit_res = audit_binary(out_obj, out_proof, expect_contract=cid, verify_bin=verify_bin)
    audit_res["proof"] = out_proof
    audit_res["proof_bytes"] = os.path.getsize(out_proof)
    audit_res["glossary"] = canon["glossary"]
    audit_res["helper_map"] = helper_rename
    return audit_res


def pack_verified(
    source_path,
    spec_path=None,
    out_obj=None,
    out_proof=None,
    fn_name=None,
    target=None,
    glossary_out=None,
    includes=None,
    verify_bin=None,
    existing_bundle_proof=None,
):
    """Compile `.ode`, bind symbol to `ode_<52-char-b32>`, embed `.ode.ocl`, prove, and audit.

    Accepts either a unified `.ode` file (single-function or multi-function with local callees
    and custom `calling { ... }`, `spec_path=None`) or a legacy `(source_path, spec_path)` pair.
    Refuses contractless functions loudly.
    """
    import ode_unified
    src_text = odec.read_source(source_path)
    unified = ode_unified.is_unified(src_text)

    if unified:
        parsed = ode_unified.parse_unified(src_text, source_path)
        arch, _, _, fns = odec.source(src_text, source_path, target=target)
        if not fns:
            raise ValueError(f"{source_path}: no `fn` found for target {target!r}")
        chosen_fn = fn_name or fns[-1][0]
        fn_rec = parsed["fns_by_name"].get(chosen_fn)
        if fn_rec is None:
            raise ValueError(f"{source_path}: function `{chosen_fn}` not found")
        use_target = target or arch
        impl = ode_unified._select_impl(fn_rec, use_target, source_path)
        if impl is not None and impl["calling_text"] is not None:
            raise ValueError(
                f"{source_path}: exported C-ABI function `{chosen_fn}` cannot declare custom `calling {{ ... }}`"
            )

        # Build symbol -> unified fn_name map and compile reachable local callees in topological order.
        sym_to_fn = {f["symbol"]: f["name"] for f in parsed["fns"]}
        compiled = {}
        topo_fns = []
        visiting = set()
        visited = set()

        def visit(name):
            if name in visited or name in visiting:
                return
            visiting.add(name)
            inf = odec.compile_info(source_path, name, target=use_target)
            compiled[name] = inf
            for csym in _called_symbols(inf["elf"]):
                if csym == inf["symbol"]:
                    continue  # direct self-recursion
                if csym not in sym_to_fn:
                    raise ValueError(
                        f"{source_path}: `{name}` calls `{csym}`, which is not defined in this `.ode` file"
                    )
                visit(sym_to_fn[csym])
            visiting.remove(name)
            visited.add(name)
            topo_fns.append(name)

        visit(chosen_fn)

        if len(topo_fns) > 1:
            full_spec_text, _ = ode_unified.extract_spec(
                parsed, target_key=use_target, fn_name=None, include_calling=True, src=source_path
            )
            unit_elfs = [compiled[n]["elf"] for n in topo_fns]
            orig_order = [compiled[n]["symbol"] for n in topo_fns]
            if existing_bundle_proof is not None:
                canon = ode_canon.canonicalize(full_spec_text, contract_name=orig_order[-1])
                cid = canon["contract_id"]
                hash_sym = canon["symbol"]
                rename_map = {orig: f"h{idx}" for idx, orig in enumerate(orig_order[:-1])}
                rename_map[orig_order[-1]] = hash_sym
                obj_bytes = merge_elf_objects(
                    unit_elfs, parse_elf64(unit_elfs[0])["target"], rename_map, hash_sym,
                    embedded_ocl_bytes=canon["canonical"].encode("utf-8"),
                )
                os.makedirs(os.path.dirname(os.path.abspath(out_obj)), exist_ok=True)
                with open(out_obj, "wb") as f:
                    f.write(obj_bytes)
                audit_res = audit_binary(out_obj, existing_bundle_proof, expect_contract=cid, verify_bin=verify_bin)
                audit_res["proof"] = existing_bundle_proof
                audit_res["proof_bytes"] = os.path.getsize(existing_bundle_proof)
                audit_res["glossary"] = canon["glossary"]
                return audit_res
            places_by_sym = {
                compiled[n]["symbol"]: compiled[n].get("places", {}).get(compiled[n]["symbol"], "")
                for n in topo_fns
            }
            compiled_by_sym = {compiled[n]["symbol"]: compiled[n] for n in topo_fns}
            return pack_bundle(
                unit_elfs,
                orig_order,
                compiled[chosen_fn]["symbol"],
                full_spec_text,
                out_obj,
                out_proof,
                places_by_sym=places_by_sym,
                glossary_out=glossary_out,
                verify_bin=verify_bin,
                compiled_by_sym=compiled_by_sym,
            )

        info = compiled[chosen_fn]
        orig_sym = info["symbol"]
        spec_text, cname = ode_unified.extract_spec(
            parsed, target_key=use_target, fn_name=chosen_fn, include_calling=False, src=source_path
        )
        canon = ode_canon.canonicalize(spec_text, contract_name=cname)
    else:
        if spec_path is None:
            raise ValueError(
                f"{source_path}: every Ode function must have a contract "
                f"(use unified `.ode` syntax with contract clauses on `fn`, or supply a contract file)"
            )
        parts = []
        for inc in (includes or ()):
            with open(inc, "r", encoding="utf-8") as f:
                parts.append(f.read())
        with open(spec_path, "r", encoding="utf-8") as f:
            parts.append(f.read())
        spec_text = "\n".join(parts)

        _, _, _, fns = odec.source(src_text, source_path)
        if not fns:
            raise ValueError(f"{source_path}: no `fn` found")
        chosen_fn = fn_name or fns[-1][0]
        info = odec.compile_info(source_path, chosen_fn)
        orig_sym = info["symbol"]

        sp, is_nameless = ode_canon._parse_any(spec_text)
        cname = None if is_nameless or len(sp.contracts) == 1 else orig_sym
        canon = ode_canon.canonicalize(spec_text, contract_name=cname)
        if not includes:
            ode_canon.check_ocl_filename(spec_path, canon["contract_id"])
    cid = canon["contract_id"]
    hash_sym = canon["symbol"]

    # Rename exported symbol -> `ode_<52-char-b32>` and embed canonical `.ocl` in `.ode.ocl`.
    obj_bytes = rename_elf_symbol(info["elf"], orig_sym, hash_sym)
    obj_bytes = append_elf_section(
        obj_bytes,
        ".ode.ocl",
        canon["canonical"].encode("utf-8"),
        sh_type=SHT_PROGBITS,
        sh_flags=0,
        sh_align=1,
    )
    os.makedirs(os.path.dirname(os.path.abspath(out_obj)), exist_ok=True)
    with open(out_obj, "wb") as f:
        f.write(obj_bytes)

    # Generate `.statement` and separate `.proof` via `proof-core/prove.py`.
    bound_spec = ode_canon.bind_symbol(canon["canonical"], hash_sym)
    pl_text = _map_places_text(info.get("places", {}).get(orig_sym, ""), canon["glossary"], orig_sym, hash_sym, True)
    with tempfile.TemporaryDirectory(prefix="ode_pack_") as tmp:
        stmt_path = os.path.join(tmp, "pack.statement")
        os.makedirs(os.path.dirname(os.path.abspath(out_proof)), exist_ok=True)
        try:
            prove.prove(bound_spec, [(out_obj, hash_sym, pl_text)], stmt_path, out_proof)
        except SystemExit as exc:
            tgt = parse_elf64(obj_bytes)["target"]
            _raise_pack_proof_error(
                exc, stmt_path, out_proof, {hash_sym: orig_sym}, {orig_sym: info}, spec_text, tgt,
            )

    if glossary_out:
        os.makedirs(os.path.dirname(os.path.abspath(glossary_out)), exist_ok=True)
        with open(glossary_out, "w", encoding="utf-8") as f:
            json.dump({"contract_id": cid, "glossary": canon["glossary"]}, f, indent=2, sort_keys=True)
            f.write("\n")

    # Immediately run Bob's full auditor check on the produced artifact!
    audit_res = audit_binary(out_obj, out_proof, expect_contract=cid, verify_bin=verify_bin)
    audit_res["proof"] = out_proof
    audit_res["proof_bytes"] = os.path.getsize(out_proof)
    audit_res["glossary"] = canon["glossary"]
    return audit_res


# ---------------------------------------------------------------------------
# Concrete specification evaluator (`ode_tool.py spec-test`)
# ---------------------------------------------------------------------------

def run_spec_test(ocl_path, fn_name, raw_args, glossary_path=None):
    """Evaluate a definition inside a `.ocl` or unified `.ode` file on concrete JSON inputs."""
    import ode_unified
    with open(ocl_path, "r", encoding="utf-8") as f:
        text = f.read()
    if ode_unified.is_unified(text):
        parsed = ode_unified.parse_unified(text, ocl_path)
        text = "\n\n".join(parsed["spec_defs"]) + "\n"
        sp = ode.Spec(text)
    else:
        if ode_canon.HASH_OCL_RE.fullmatch(os.path.basename(ocl_path)):
            info = ode_canon.canonicalize(text)
            ode_canon.check_ocl_filename(ocl_path, info["contract_id"])
        sp, _ = ode_canon._parse_any(text)
    target_fn = fn_name
    if target_fn not in sp.fns and target_fn not in sp.machines and glossary_path:
        with open(glossary_path, "r", encoding="utf-8") as f:
            gdata = json.load(f)
        g = gdata.get("glossary", gdata)
        inv = {v: k for k, v in g.items()}
        if target_fn in inv:
            target_fn = inv[target_fn]
    parsed_args = [json.loads(a) for a in raw_args]
    return sp.call(ode.Numbers(), target_fn, *parsed_args)
