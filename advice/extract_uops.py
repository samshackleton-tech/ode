#!/usr/bin/env python3
"""advice/extract_uops.py: extract per-instruction port masks, uops, latencies, and measured
throughputs from uops.info's `instructions.xml` for every row of `core/x86.tab`.

Produces `advice/uops_ports.json` for modern x86-64 microarchitectures (ZEN5, ZEN4, ZEN3, ICL,
EMR, ADL-P). Strictly advisory — never read by `proof-core/odeverify` or `lang/odec.py`.

Usage:
    python3 advice/extract_uops.py /path/to/instructions.xml
"""
import json, os, re, sys
import xml.etree.ElementTree as ET

HERE = os.path.dirname(os.path.abspath(__file__))
ARCHS = ("ZEN5", "ZEN4", "ZEN3", "ICL", "EMR", "ADL-P")

# Map every `core/x86.tab` row name -> ordered candidate `uops.info` instruction strings.
ROW_TO_UOPS = {
    "add64_rr":      ["ADD_01 (R64, R64)"],
    "add64_ri":      ["ADD (R64, I8)", "ADD (R64, I32)"],
    "add64_rm":      ["ADD (R64, M64)"],
    "sub64_rr":      ["SUB_29 (R64, R64)"],
    "sub64_ri":      ["SUB (R64, I8)", "SUB (R64, I32)"],
    "sub64_rm":      ["SUB (R64, M64)"],
    "and64_rr":      ["AND_21 (R64, R64)"],
    "and64_ri":      ["AND (R64, I8)", "AND (R64, I32)"],
    "and64_rm":      ["AND (R64, M64)"],
    "or64_rr":       ["OR_09 (R64, R64)"],
    "or64_ri":       ["OR (R64, I8)", "OR (R64, I32)"],
    "or64_rm":       ["OR (R64, M64)"],
    "xor64_same":    ["XOR_31 (R64, R64)"],
    "shl64_ri":      ["SHL (R64, I8)"],
    "shr64_ri":      ["SHR (R64, I8)"],
    "dec64":         ["DEC (R64)"],
    "cmp64_rr":      ["CMP_39 (R64, R64)"],
    "cmp64_ri":      ["CMP (R64, I8)", "CMP (R64, I32)"],
    "cmp64_rm":      ["CMP (R64, M64)"],
    "test64_same":   ["TEST (R64, R64)"],
    "mov64_rr":      ["MOV_89 (R64, R64)"],
    "mov64_ri":      ["MOV (R64, I32)", "MOV (R64, I64)"],
    "mov64_rm":      ["MOV (R64, M64)"],
    "mov64_mr":      ["MOV (M64, R64)"],
    "lea":           ["LEA_B_D8 (R64)", "LEA_B (R64)"],
    "lea_idx":       ["LEA_B_I (R64)", "LEA_B_IS (R64)"],
    "lea_data":      ["LEA_B_D32 (R64)", "LEA_B (R64)"],
    "mov32_rr":      ["MOV_89 (R32, R32)"],
    "mov32_ri":      ["MOV (R32, I32)"],
    "mov32_rm":      ["MOV (R32, M32)"],
    "or32_rr":       ["OR_09 (R32, R32)"],
    "and32_ri":      ["AND (R32, I8)", "AND (R32, I32)"],
    "xor32_same":    ["XOR_31 (R32, R32)"],
    "shr32_ri":      ["SHR (R32, I8)"],
    "dec32":         ["DEC (R32)"],
    "test32_same":   ["TEST (R32, R32)"],
    "movzx8_rm":     ["MOVZX (R32, M8)"],
    "movzx8_rr":     ["MOVZX (R32, R8l)"],
    "mov8_al_i":     ["MOV (R8l, I8)"],
    "mov8_mr":       ["MOV (M8, R8l)"],
    "mov8_mi":       ["MOV (M8, I8)"],
    "dec8_al":       ["DEC (R8l)"],
    "push":          ["PUSH (R64)"],
    "pop":           ["POP (R64)"],
    "call":          ["CALL_NEAR (Rel32)"],
    "ret":           ["RET_NEAR"],
    "jmp":           ["JMP (Rel8)", "JMP (Rel32)"],
    "je":            ["JZ (Rel8)", "JZ (Rel32)"],
    "jne":           ["JNZ (Rel8)", "JNZ (Rel32)"],
    "jae":           ["JNB (Rel8)", "JNB (Rel32)"],
    "jb":            ["JB (Rel8)", "JB (Rel32)"],
    "ja":            ["JNBE (Rel8)", "JNBE (Rel32)"],
    "jbe":           ["JBE (Rel8)", "JBE (Rel32)"],
    "nop":           ["NOP"],
    "loadu128":      ["VMOVDQU (XMM, M128)", "MOVUPS (XMM, M128)"],
    "storeu128":     ["VMOVDQU (M128, XMM)", "MOVUPS (M128, XMM)"],
    "const128":      ["VMOVAPS (XMM, M128)", "MOVAPS (XMM, M128)"],
    "mov128":        ["VMOVDQA_6F (XMM, XMM)", "MOVDQA_0F6F (XMM, XMM)"],
    "movq128":       ["VMOVQ (XMM, R64)", "MOVQ (XMM, R64)"],
    "paddd128":      ["VPADDD (XMM, XMM, XMM)", "PADDD (XMM, XMM)"],
    "pxor128":       ["VPXORD (XMM, XMM, XMM)", "VPXOR (XMM, XMM, XMM)", "PXOR (XMM, XMM)"],
    "prord128":      ["VPRORD (XMM, XMM, I8)"],
    "pslld128":      ["VPSLLD (XMM, XMM, I8)", "PSLLD (XMM, I8)"],
    "psrld128":      ["VPSRLD (XMM, XMM, I8)", "PSRLD (XMM, I8)"],
    "por128":        ["VPOR (XMM, XMM, XMM)", "POR (XMM, XMM)"],
    "pshufb128":     ["PSHUFB (XMM, XMM)", "VPSHUFB (XMM, XMM, XMM)"],
    "pshufd128":     ["PSHUFD (XMM, XMM, I8)", "VPSHUFD (XMM, XMM, I8)"],
    "shufps128":     ["VSHUFPS (XMM, XMM, XMM, I8)", "SHUFPS (XMM, XMM, I8)"],
    "unpckldq":      ["VPUNPCKLDQ (XMM, XMM, XMM)", "PUNPCKLDQ (XMM, XMM)"],
    "unpckhdq":      ["VPUNPCKHDQ (XMM, XMM, XMM)", "PUNPCKHDQ (XMM, XMM)"],
    "unpcklqdq":     ["VPUNPCKLQDQ (XMM, XMM, XMM)", "PUNPCKLQDQ (XMM, XMM)"],
    "pblendd128":    ["VPBLENDD (XMM, XMM, XMM, I8)"],
    "pblendw128":    ["VPBLENDW (XMM, XMM, XMM, I8)", "PBLENDW (XMM, XMM, I8)"],
    "vzeroupper":    ["VZEROUPPER"],
    "broadcast_r":   ["VPBROADCASTD (ZMM, R32)"],
    "broadcast_i":   ["VPBROADCASTD (ZMM, M32)"],
    "broadcast_m":   ["VPBROADCASTD (ZMM, M32)"],
    "mov512":        ["VMOVDQA32 (ZMM, ZMM)"],
    "load512a":      ["VMOVDQA32 (ZMM, M512)"],
    "load512":       ["VMOVDQU32 (ZMM, M512)"],
    "load512i":      ["VMOVDQU32 (ZMM, M512)"],
    "store512a":     ["VMOVDQA32 (M512, ZMM)"],
    "store512":      ["VMOVDQU32 (M512, ZMM)"],
    "paddd512m":     ["VPADDD (ZMM, ZMM, M512)"],
    "paddd512c":     ["VPADDD (ZMM, ZMM, M512)"],
    "pcmpud512":     ["VPCMPUD (K, ZMM, ZMM, I8)"],
    "paddd512k":     ["VPADDD (ZMM{K}, ZMM, ZMM)", "VPADDD (ZMM, ZMM, ZMM)"],
    "paddd512":      ["VPADDD (ZMM, ZMM, ZMM)"],
    "pxord512_same": ["VPXORD (ZMM, ZMM, ZMM)"],
    "pxord512":      ["VPXORD (ZMM, ZMM, ZMM)"],
    "prord512":      ["VPRORD (ZMM, ZMM, I8)"],
    "unpckldq512":   ["VPUNPCKLDQ (ZMM, ZMM, ZMM)"],
    "unpckhdq512":   ["VPUNPCKHDQ (ZMM, ZMM, ZMM)"],
    "unpcklqdq512":  ["VPUNPCKLQDQ (ZMM, ZMM, ZMM)"],
    "unpckhqdq512":  ["VPUNPCKHQDQ (ZMM, ZMM, ZMM)"],
    "shufi32x4":     ["VSHUFI32X4 (ZMM, ZMM, ZMM, I8)"],
}

ZERO_IDIOM_ROWS = {"xor64_same", "xor32_same", "pxord512_same"}


def parse_ports(port_str):
    """Parse uops.info port string like '1*FP0123' or '1*p23+1*p0156' into [(count, [port_names])]."""
    if not port_str:
        return []
    out = []
    for chunk in port_str.split("+"):
        chunk = chunk.strip()
        m = re.match(r"^(\d+)\*(.+)$", chunk)
        if not m:
            continue
        cnt = int(m.group(1))
        spec = m.group(2)
        if spec.startswith("FP"):
            ports = [f"FP{c}" for c in spec[2:] if c.isdigit()]
        elif spec.startswith("p"):
            # Intel style: p0156, p23, p06, p0123, p23A, etc.
            body = spec[1:]
            ports = []
            i = 0
            while i < len(body):
                if body[i].isdigit():
                    tok = "p" + body[i]
                    if i + 1 < len(body) and body[i + 1].isalpha():
                        tok += body[i + 1]
                        i += 2
                    else:
                        i += 1
                    ports.append(tok)
                else:
                    i += 1
        elif spec.startswith("ALU"):
            ports = [f"ALU{c}" for c in spec[3:] if c.isdigit()]
        elif spec.startswith("AGU"):
            ports = [f"AGU{c}" for c in spec[3:] if c.isdigit()]
        else:
            ports = [spec]
        if ports:
            out.append([cnt, ports])
    return out


def main():
    if len(sys.argv) < 2:
        raise SystemExit("usage: extract_uops.py /path/to/instructions.xml")
    xml_path = sys.argv[1]
    want_strings = set()
    for cands in ROW_TO_UOPS.values():
        want_strings.update(cands)

    found = {}
    for _, elem in ET.iterparse(xml_path, events=("end",)):
        if elem.tag != "instruction":
            continue
        s = elem.get("string")
        if s in want_strings:
            # Prefer non-zeroing normal entry, except keep zeroing measurements separately!
            is_zero = elem.get("zeroing") == "true" or "same_reg" in (elem.get("iform") or "")
            by_arch = found.setdefault(s, {})
            for a in elem.findall("architecture"):
                an = a.get("name")
                if an not in ARCHS:
                    continue
                m = a.find("measurement")
                if m is None:
                    continue
                # Extract non-memory register-to-register latency and memory-to-register latency separately
                reg_lats, mem_lats = [], []
                for l in m.findall("latency"):
                    for k in ("cycles", "max_cycles"):
                        v = l.get(k)
                        if v is not None:
                            try:
                                reg_lats.append(float(v))
                            except ValueError:
                                pass
                    for k in ("cycles_mem", "cycles_addr"):
                        v = l.get(k)
                        if v is not None:
                            try:
                                mem_lats.append(float(v))
                            except ValueError:
                                pass
                tp_s = m.get("TP_unrolled") or m.get("TP_loop")
                rec = {
                    "uops": int(m.get("uops")) if m.get("uops") else 1,
                    "ports_raw": m.get("ports") or "",
                    "ports": parse_ports(m.get("ports") or ""),
                    "tp": float(tp_s) if tp_s else None,
                    "lat": max(reg_lats) if reg_lats else (max(mem_lats) if mem_lats else 1.0),
                    "mem_lat": max(mem_lats) if mem_lats else None,
                }
                # Do not overwrite an earlier entry that has port details with one lacking ports
                prev = by_arch.get(an)
                if prev is None or (not prev["ports"] and rec["ports"]) or (not is_zero and prev.get("_zero")):
                    rec["_zero"] = is_zero
                    by_arch[an] = rec
        elem.clear()

    # Build clean per-row table for all 96 x86.tab rows
    table_out = {}
    missing = []
    for row_name, cands in ROW_TO_UOPS.items():
        per_arch = {}
        for an in ARCHS:
            chosen = None
            for cand in cands:
                if cand in found and an in found[cand]:
                    chosen = dict(found[cand][an])
                    chosen.pop("_zero", None)
                    chosen["uops_name"] = cand
                    break
            if chosen is not None:
                if row_name in ZERO_IDIOM_ROWS:
                    chosen["lat"] = 0.0
                    chosen["zero_idiom"] = True
                per_arch[an] = chosen
        if not per_arch:
            missing.append(row_name)
        table_out[row_name] = per_arch

    out_path = os.path.join(HERE, "uops_ports.json")
    payload = {
        "_comment": "Per-instruction uops.info data for core/x86.tab rows across modern x86-64 microarchitectures. Generated by advice/extract_uops.py. Strictly advisory.",
        "archs": list(ARCHS),
        "rows": table_out,
    }
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(payload, f, indent=2, sort_keys=True)
        f.write("\n")
    print(f"Wrote {out_path}: {len(table_out)} rows ({len(missing)} missing: {missing})")
    for an in ARCHS:
        have = sum(1 for v in table_out.values() if an in v)
        with_ports = sum(1 for v in table_out.values() if an in v and v[an]["ports"])
        print(f"  {an:6s}: {have}/{len(table_out)} rows matched ({with_ports} with explicit port masks)")


if __name__ == "__main__":
    main()
