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
SHT_INIT_ARRAY = 14
SHT_FINI_ARRAY = 15
SHT_PREINIT_ARRAY = 16

SHF_WRITE = 0x1
SHF_ALLOC = 0x2
SHF_EXECINSTR = 0x4

STB_LOCAL = 0
STB_GLOBAL = 1
STB_WEAK = 2

STT_FUNC = 2

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


# ---------------------------------------------------------------------------
# Binary-first auditor (`ode_tool.py audit`)
# ---------------------------------------------------------------------------

def audit_binary(
    bin_path,
    proof_path,
    expect_contract=None,
    contract_path=None,
    verify_bin=None,
):
    """Audit a compiled ELF64 binary directly against its canonical `.ocl` contract and separate `.proof`.

    Returns a structured dict with `verdict` (`"shown"` or `"refused"`), both 52-char base-32
    BLAKE3 digests (`binary_b32`, `contract_b32`), coverage stats, canonical `.ocl` text, and
    any refusal errors.
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

    # 6. Check exported symbols (100% symbol coverage + hash-bound symbol rule).
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

    # Also reject any extra local STT_FUNC symbols outside the verified function.
    extra_local_funcs = [
        sym["name"] for sym in elf["symbols"]
        if sym["bind"] == STB_LOCAL and sym["type"] == STT_FUNC and sym["shndx"] == text_idx and sym["name"] != exp_sym
    ]
    if extra_local_funcs:
        errors.append(f"extra local function symbol(s) in `.text` outside the verified function: {extra_local_funcs}")

    if exp["value"] != 0:
        errors.append(f"exported function `{exp_sym}` starts at `.text` offset {exp['value']} != 0 (extra leading bytes)")

    if errors:
        return res

    # 7. Decode `.text` and confirm 100% executable-byte coverage (allowing only trailing alignment NOPs < 16 B).
    try:
        if target == "arm64":
            rows = arm64_obj.read(bin_path, exp_sym)
        else:
            rows, _ = kdecode.read(bin_path, exp_sym, 0, 0)
    except BaseException as exc:
        errors.append(f"instruction decode failed for `{exp_sym}`: {exc}")
        return res
    if not rows:
        errors.append(f"no instructions decoded for `{exp_sym}`")
        return res
    if rows[0][0] != 0:
        errors.append(f"first decoded instruction starts at offset {rows[0][0]} != 0")
    for idx in range(len(rows) - 1):
        if rows[idx][1] != rows[idx + 1][0]:
            errors.append(f"gap in decoded `.text` between bytes {rows[idx][1]} and {rows[idx + 1][0]}")
    covered_end = rows[-1][1]
    tail = text_bytes[covered_end:]
    if not _is_pure_nop_pad(tail, target):
        errors.append(
            f"extra trailing executable bytes in `.text` after offset {covered_end}: "
            f"{len(tail)} bytes ({tail[:16].hex()})"
        )
    if exp["size"] and exp["size"] < covered_end:
        errors.append(f"symbol `{exp_sym}` size {exp['size']} is smaller than decoded span {covered_end}")
    if errors:
        return res

    res["coverage"] = {
        "functions": 1,
        "instructions": len(rows),
        "code_bytes": covered_end,
        "text_bytes": len(text_bytes),
        "exported_symbols": 1,
        "hooks": 0,
    }

    # 8. Check proof file exists and invoke Lean 4 `odeverify` directly on the binary!
    if not proof_path or not os.path.isfile(proof_path):
        errors.append(f"proof file not found: {proof_path}")
        return res
    try:
        verifier = _find_odeverify(verify_bin)
    except FileNotFoundError as exc:
        errors.append(str(exc))
        return res

    bound_spec = ode_canon.bind_symbol(canonical_ocl, exp_sym)
    with tempfile.TemporaryDirectory(prefix="ode_audit_") as tmp:
        stmt_path = os.path.join(tmp, "audit.statement")
        try:
            stmt_lines = statement.statement(bound_spec, [(bin_path, exp_sym)])
        except BaseException as exc:
            errors.append(f"statement build failed: {exc}")
            return res
        with open(stmt_path, "w", encoding="utf-8") as f:
            f.write("\n".join(stmt_lines) + "\n")
        table_path = statement.table_of(stmt_lines)
        proc = subprocess.run(
            [verifier, table_path, stmt_path, proof_path],
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
        lines.append(
            f"  COVERAGE:          100% of executable code "
            f"({cov['functions']} function, {cov['instructions']} instructions, "
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
# Hash-bound builder (`ode_tool.py pack`)
# ---------------------------------------------------------------------------

def pack_verified(
    source_path,
    spec_path,
    out_obj,
    out_proof,
    fn_name=None,
    glossary_out=None,
    includes=None,
    verify_bin=None,
):
    """Compile `.ode`, bind symbol to `ode_<52-char-b32>`, embed `.ode.ocl`, prove, and audit."""
    parts = []
    for inc in (includes or ()):
        with open(inc, "r", encoding="utf-8") as f:
            parts.append(f.read())
    with open(spec_path, "r", encoding="utf-8") as f:
        parts.append(f.read())
    spec_text = "\n".join(parts)

    # Compile `.ode` source to get its original symbol and raw ELF `.o`.
    src_text = odec.read_source(source_path)
    target, _, _, fns = odec.source(src_text, source_path)
    if not fns:
        raise ValueError(f"{source_path}: no `fn` found")
    chosen_fn = fn_name or fns[-1][0]
    info = odec.compile_info(source_path, chosen_fn)
    orig_sym = info["symbol"]

    # Canonicalize the contract and derive the sole 52-char base-32 BLAKE3 ID and symbol.
    sp, is_nameless = ode_canon._parse_any(spec_text)
    cname = None if is_nameless or len(sp.contracts) == 1 else orig_sym
    canon = ode_canon.canonicalize(spec_text, contract_name=cname)
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
    pl_text = info.get("places", {}).get(orig_sym, "")
    if pl_text:
        # Map author argument/function names inside loop place hints to canonical names.
        import re as _re
        inv_map = {orig: can for can, orig in canon["glossary"].items() if can != "contract" and "." not in can}
        inv_map[orig_sym] = hash_sym
        pat = _re.compile(r"\b(" + "|".join(_re.escape(k) for k in sorted(inv_map, key=len, reverse=True)) + r")\b")
        pl_text = pat.sub(lambda m: inv_map[m.group(1)], pl_text)
    with tempfile.TemporaryDirectory(prefix="ode_pack_") as tmp:
        stmt_path = os.path.join(tmp, "pack.statement")
        os.makedirs(os.path.dirname(os.path.abspath(out_proof)), exist_ok=True)
        prove.prove(bound_spec, [(out_obj, hash_sym, pl_text)], stmt_path, out_proof)

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
    """Evaluate a definition inside a `.ocl` or `.spec` file on concrete JSON inputs."""
    with open(ocl_path, "r", encoding="utf-8") as f:
        text = f.read()
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
