"""sim.py ARCH [CAP]: the kernel's uops put on ports one by one in program order, each at the first cycle at which what it
reads is ready and one of its ports is free (for as many cycles as uops.info's throughput says it holds a port);
CAP: at most so many vector uops start in a cycle. Prints cycles a block."""
import collections, json, os, re, sys
ARCH = sys.argv[1]; CAP = int(sys.argv[2]) if len(sys.argv) > 2 else 99
src_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "predict.py")
with open(src_path) as f: code = f.read().split("ready = collections.defaultdict(float)")[0]
sys.argv = [src_path, ARCH]
exec(code)
def ports_of(p): return sorted(set(re.findall(r"\d", p.split("*", 1)[1].split("+")[0])))
busy = collections.defaultdict(set)      # port -> cycles taken
started = collections.Counter()
ready = collections.defaultdict(int); ends = []
for n in range(8):
    for k in block:
        dst, src, name = info(rows[k][2])
        u, ports, lat = numbers(name)
        t = int(max((ready[s] for s in src), default=0))
        m = FORMS[name][ARCH] if name else None
        if m and m["ports"] and m["tp"] and ("FP" in m["ports"] or m["ports"].startswith("1*p")) and "+" not in m["ports"] and "45" not in m["ports"]:
            ps = ports_of(m["ports"]); occ = max(1, round(float(m["tp"]) * len(ps)))
            while True:
                if started[t] < CAP:
                    free = [p for p in ps if all(t + j not in busy[p] for j in range(occ))]
                    if free:
                        p = min(free, key=lambda p: len(busy[p]))
                        for j in range(occ): busy[p].add(t + j)
                        started[t] += 1
                        break
                t += 1
        t += int(lat)
        for d in dst: ready[d] = t
    ends.append(max(ready[r] for r in list(ready) if r.startswith("zmm")))
print(ARCH, "cap", CAP, "cycles a block:", [ends[i + 1] - ends[i] for i in range(len(ends) - 1)][-3:])
