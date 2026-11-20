"""predict.py ARCH (run where forms.json is): cycles per block of the 16-way kernel (blake3_servil_avx512_p16 of kcheck/b3hashr.o), predicted from
uops.info's numbers for ARCH: the longest chain of dependencies a block adds; the uops a block has against how many the
processor takes a cycle; and the uops that can go only to some ports against how many those ports are."""
import collections, json, os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
KCHECK = os.path.join(HERE, "..", "..", "kcheck")
with open("forms.json") as f: FORMS = json.load(f)          # what extract.py wrote, in the working directory
sys.path.insert(0, KCHECK)
os.chdir(KCHECK)
import kdecode
ARCH = sys.argv[1]
WIDTH = {"ZEN5": 8, "ZEN4": 6, "EMR": 6, "ICL": 5, "SKX": 4}[ARCH]            # uops renamed a cycle
rows, _ = kdecode.read("b3hashr.o", "blake3_servil_avx512_p16", 0, 0)
idx = {a: k for k, (a, b, t) in enumerate(rows)}
jumps = {k: idx[int(t.split()[1], 0)] for k, (a, b, t) in enumerate(rows) if t.split()[0] in (".jne", ".je", ".jmp")}
head = jumps[max(k for k in jumps if rows[k][2].startswith(".jne") and jumps[k] < k)]      # the loop over blocks
bottom = max(k for k in jumps if jumps[k] == head)
je = next(k for k in jumps if rows[k][2].startswith(".je") and head < k < bottom)
jmp = next(k for k in jumps if rows[k][2].startswith(".jmp") and head < k < bottom)
r1 = list(range(jumps[jmp], je + 1)); r2 = list(range(je + 1, jmp + 1))
block = list(range(head, jumps[jmp])) + r1 + (r2 + r1) * 3 + list(range(jumps[je], bottom + 1))

def info(text):
    """(what it sets, what it reads, uops.info's name)"""
    w = text.replace("(", " ").replace(")", " ").split()
    op = w[0]
    z = lambda n: "zmm" + n
    regs = [x[1:] for x in w[1:] if x.startswith(".") and x not in (".reg", ".imm", ".mem")]
    if op in (".zpaddd", ".zpxord", ".zunpckldq", ".zunpckhdq", ".zunpcklqdq", ".zunpckhqdq"):
        name = {"zpaddd": "VPADDD", "zpxord": "VPXORD", "zunpckldq": "VPUNPCKLDQ", "zunpckhdq": "VPUNPCKHDQ",
                "zunpcklqdq": "VPUNPCKLQDQ", "zunpckhqdq": "VPUNPCKHQDQ"}[op[1:]] + " (ZMM, ZMM, ZMM)"
        return [z(w[1])], ([] if op == ".zpxord" and w[2] == w[3] else [z(w[2]), z(w[3])]), name
    if op == ".zprord": return [z(w[1])], [z(w[2])], "VPRORD (ZMM, ZMM, I8)"
    if op == ".zshufi32x4": return [z(w[1])], [z(w[2]), z(w[3])], "VSHUFI32X4 (ZMM, ZMM, ZMM, I8)"
    if op == ".zmov": return [z(w[1])], [z(w[2])], "VMOVDQA32 (ZMM, ZMM)"
    if op == ".zbroadcast": return [z(w[1])], regs, "VPBROADCASTD (ZMM, R32)" if ".reg" in w else "VPBROADCASTD (ZMM, M32)"
    if op == ".zloadi": return [z(w[1])], regs, "VMOVDQU32 (ZMM, M512)"
    if op == ".zload": return [z(w[2])], regs + ["mem:" + w[3] + w[4]], "VMOVDQA32 (ZMM, M512)"
    if op == ".zstore": return ["mem:" + w[2] + w[3]], [z(w[4])], "VMOVDQA32 (M512, ZMM)"
    if op in (".jne", ".je", ".jmp"): return [], [], "JNZ (Rel8)"
    if op in (".nop", ".ret", ".vzeroupper", ".push", ".pop"): return [], [], None
    # a general instruction: the first register is set; every register is read (but for a plain move's first)
    dst = regs[:1]
    src = regs[1:] if op in (".mov", ".movzx8", ".lea") else regs
    if op == ".cmp": dst = []
    return dst, src, "MOV (R64, M64)" if ".mem" in w else "ADD (R64, I8)"

def numbers(name):
    if name is None: return 1, None, 1.0
    m = FORMS[name][ARCH]
    lat = max((l[0] for l in m["lat"]), default=0.0)
    return int(m["uops"]), m["ports"], lat

ready = collections.defaultdict(float)
ends = []
uops = collections.Counter(); byports = collections.Counter(); kinds = collections.Counter()
BLOCKS = 6
for n in range(BLOCKS):
    for k in block:
        text = rows[k][2]
        dst, src, name = info(text)
        u, ports, lat = numbers(name)
        if n == 0:
            uops["all"] += u; byports[ports] += u if ports else 0; kinds[name] += 1
        t = max((ready[s] for s in src), default=0.0) + lat
        for d in dst: ready[d] = t
    ends.append(max(ready[r] for r in list(ready) if r.startswith("zmm")))
growth = [ends[i + 1] - ends[i] for i in range(len(ends) - 1)]
print("architecture", ARCH)
print("instructions a block:", len(block), "| uops a block:", uops["all"])
print("uops by the ports they can go to:", dict(byports))
print("the longest chain a block adds (cycles):", growth)
fp = {p: n for p, n in byports.items() if p and "FP" in p or p and p.startswith("1*p")}
print("front end: uops / width =", round(uops["all"] / WIDTH, 1))
def ports_of(p): return set(re.findall(r"\d", p.split("*", 1)[1].split("+")[0])) if "FP" in p else set(p.split("*", 1)[1].split("+")[0].replace("p", "").replace("A", "").replace("B", ""))
best = 0; why = None
sets = [ports_of(p) for p in fp]
import itertools
allports = sorted(set().union(*sets)) if sets else []
for r in range(1, len(allports) + 1):
    for S in itertools.combinations(allports, r):
        S = set(S)
        need = sum(n for p, n in fp.items() if ports_of(p) <= S)
        if need / len(S) > best: best, why = need / len(S), (sorted(S), need)
print("ports: the most uops that must share some ports, per port =", round(best, 1), "for ports", why)
# the same by what uops.info MEASURED an instruction to take when it runs alone, back to back (its throughput):
# an instruction that can go to k ports and takes TP cycles each uses TP * k cycles of ports
work = 0.0
alu = ports_of(FORMS["VPADDD (ZMM, ZMM, ZMM)"][ARCH]["ports"]) | ports_of(FORMS["VPRORD (ZMM, ZMM, I8)"][ARCH]["ports"]) | ports_of(FORMS["VSHUFI32X4 (ZMM, ZMM, ZMM, I8)"][ARCH]["ports"])
for k in block:
    dst, src, name = info(rows[k][2])
    if name is None: continue
    m = FORMS[name][ARCH]
    if m["ports"] and ("FP" in m["ports"] or m["ports"].startswith("1*p")) and m["tp"] and ports_of(m["ports"]) <= alu:
        work += float(m["tp"]) * len(ports_of(m["ports"]))
print("ports, by measured throughput: cycles of the vector ports a block needs =", round(work, 1), "over", len(alu), "ports =", round(work / len(alu), 1))
print("PREDICTED cycles a block >=", round(max(growth[-1], uops["all"] / WIDTH, best, work / len(alu)), 1))
for name, n in kinds.most_common(12): print("   ", n, name, numbers(name))
