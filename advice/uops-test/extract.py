"""extract.py ARCH...: from instructions.xml, the forms of the mnemonics below with what uops.info measured on each ARCH:
uops, ports, throughput, and the longest latency between two operands. Writes forms.json."""
import json, sys
import xml.etree.ElementTree as ET
WANT = {"VPADDD", "VPXORD", "VPRORD", "VSHUFI32X4", "VPBROADCASTD", "VMOVDQU32", "VMOVDQA32", "VPUNPCKLDQ", "VPUNPCKHDQ",
        "VPUNPCKLQDQ", "VPUNPCKHQDQ", "MOV", "PUSH", "POP", "AND", "OR", "SHR", "DEC", "JNZ", "JZ", "JMP", "SUB", "XOR",
        "MOVZX", "CMP", "ADD", "LEA", "NOP", "VZEROUPPER", "RET", "VPTERNLOGD"}
archs = sys.argv[1:]
out = {}
for event, e in ET.iterparse("instructions.xml", events=("end",)):
    if e.tag != "instruction": continue
    if e.get("asm", "").replace("{evex} ", "") in WANT:
        entry = {}
        for a in e.findall("architecture"):
            if a.get("name") not in archs: continue
            m = a.find("measurement")
            if m is None: continue
            lats = []
            for l in m.findall("latency"):
                for key in ("cycles", "cycles_addr", "cycles_mem", "max_cycles"):
                    if l.get(key) is not None:
                        try: lats.append((float(l.get(key)), key, l.get("start_op"), l.get("target_op")))
                        except ValueError: pass
            entry[a.get("name")] = {"uops": m.get("uops"), "ports": m.get("ports"), "tp": m.get("TP_unrolled") or m.get("TP_loop"),
                                    "lat": sorted(lats)}
        if entry: out[e.get("string")] = entry
    e.clear()
with open("forms.json", "w") as f: json.dump(out, f, indent=0)
print(len(out), "forms")
