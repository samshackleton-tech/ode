#!/usr/bin/env python3
"""cross: every row of arm64.tab against this machine's processor.

    python3 cross.py [--cases N] [--seed S] [--work DIR] [--table FILE] [--rows NAME,NAME...] [--out FILE]
    (an AArch64 machine, macOS or Linux; needs clang)

For each row of arm64.tab, N random instances (registers, numbers, displacements chosen at random) are
assembled from the row's ASM by clang, and N more are laid down as the very word word.py writes for them.
The two must be the same word wherever both write the instance. All are run on the processor from random
states: the general registers x0 to x30, the stack pointer, the four flags, the thirty-two vector
registers' 128 bits, and 1024 bytes of memory that base registers and the stack pointer point into. What
the processor leaves is compared with what the row's EFFECT says (../core/conc.py), part by part: a part
the row does not mention must be as it was. Exit 1 if any instance differs.

One general register a case is kept out of the comparison: it holds the address of the case's state while
the instruction runs, and it is one the instance does not name, another one from case to case. On macOS x18
is kept out too: the system keeps it for itself.

Not run: rows whose ASM is `-` (they are named at the end)."""
import json, os, platform, random, re, struct, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path[:0] = [HERE, os.path.join(HERE, "..", "core")]
import conc, table, word

MAC = platform.system() == "Darwin"
X = [f"x{i}" for i in range(31)]
SCRATCH, ROOM = 0x600000000, 1024
BASE, STACK = SCRATCH + 256, SCRATCH + 512          # where a base register points, and the stack pointer
# A case's state, as the driver hands it over: the registers going in and coming out, and what the driver's own code must find again.
IN_G, IN_F, IN_V = 0, 256, 272                      # x0 to x30 and sp; the flags; v0 to v31
OUT_G, OUT_F, OUT_V = 784, 1040, 1056
REAL_G, REAL_SP, REAL_V, SIZE = 1568, 1664, 1680, 1808        # x19 to x30; sp; v8 to v15
IN, OUT = 256 + 8 + 512 + ROOM, 256 + 8 + 512 + ROOM

DRIVER = r"""
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sys/mman.h>
#define ROOM 1024
#define SCRATCH ((uint8_t *)0x600000000)
typedef void (*one)(uint8_t *);
extern one cases[];
static uint8_t state[%(size)d] __attribute__((aligned(16)));
int main(int argc, char **argv) {
    uint8_t *m = mmap(SCRATCH, 16384, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0);
    if (m != SCRATCH) return 2;
    FILE *in = fopen(argv[1], "rb"), *out = fopen(argv[2], "wb");
    if (!in || !out) return 2;
    for (long k = 0; ; k++) {
        if (fread(state + %(in_g)d, 1, 256, in) != 256) break;
        if (fread(state + %(in_f)d, 1, 8, in) != 8 || fread(state + %(in_v)d, 1, 512, in) != 512 || fread(m, 1, ROOM, in) != ROOM) return 2;
        cases[k](state);
        fwrite(state + %(out_g)d, 1, 256, out); fwrite(state + %(out_f)d, 1, 8, out); fwrite(state + %(out_v)d, 1, 512, out); fwrite(m, 1, ROOM, out);
    }
    return fclose(out) != 0;
}
""" % {"size": SIZE, "in_g": IN_G, "in_f": IN_F, "in_v": IN_V, "out_g": OUT_G, "out_f": OUT_F, "out_v": OUT_V}


def case_code(n, home, body):
    """A case as a function of its own: the driver calls it with the address of the state. `home` is the
    general register that keeps that address while the instruction runs. Gives the code, and how many
    instruction words stand before the instance (each line before it is one word)."""
    h, t = f"x{home}", ("x10" if home == 9 else "x9")               # (t: a register for what has no load or store of its own)
    rest = [i for i in range(31) if i != home and not (MAC and i == 18)]
    lines = [f"SYM(case_{n}):"] + [f"str x{i}, [x0, {REAL_G + 8 * (i - 19)}]" for i in range(19, 31)]      # (what the driver's code must find again)
    lines += [f"mov x9, sp", f"str x9, [x0, {REAL_SP}]"] + [f"str q{i}, [x0, {REAL_V + 16 * (i - 8)}]" for i in range(8, 16)]
    lines += [f"mov {h}, x0"] if home else []
    lines += [f"ldr {t}, [{h}, {IN_F}]", f"msr nzcv, {t}"] + [f"ldr q{i}, [{h}, {IN_V + 16 * i}]" for i in range(32)]
    lines += [f"ldr {t}, [{h}, {IN_G + 8 * 31}]", f"mov sp, {t}"] + [f"ldr x{i}, [{h}, {IN_G + 8 * i}]" for i in rest]
    before = len(lines) - 1
    lines += [body]
    lines += [f"str x{i}, [{h}, {OUT_G + 8 * i}]" for i in rest]
    lines += [f"mov {t}, sp", f"str {t}, [{h}, {OUT_G + 8 * 31}]", f"mrs {t}, nzcv", f"str {t}, [{h}, {OUT_F}]"]
    lines += [f"str q{i}, [{h}, {OUT_V + 16 * i}]" for i in range(32)]
    lines += [f"ldr {t}, [{h}, {REAL_SP}]", f"mov sp, {t}"] + [f"ldr q{i}, [{h}, {REAL_V + 16 * (i - 8)}]" for i in range(8, 16)]
    lines += [f"ldr x{i}, [{h}, {REAL_G + 8 * (i - 19)}]" for i in range(19, 31) if i != home]
    lines += ([f"ldr {h}, [{h}, {REAL_G + 8 * (home - 19)}]"] if home >= 19 else []) + ["ret"]
    return lines[0] + "\n" + "\n".join("    " + line for line in lines[1:]), before


def instance(row, rng):
    """One instance of a row: what each placeholder is, and the instruction as the assembler takes it."""
    asm, bind = row.asm, {}
    free = [r for r in X if not (MAC and r == "x18")]
    for h in ("D", "S", "P"):
        if re.search(rf"\b{h}(64|32)\b", asm): bind[h] = rng.choice(free)
    if re.search(r"\bB64\b", asm): bind["B"] = rng.choice(free + ["sp"])
    for h in table.VECTORS:
        if re.search(rf"\bv{h}\b", asm): bind[h] = rng.randrange(32)
    way = word.Way(row, row.bytes[0])
    if re.search(r"\bI\b", asm):
        if "I" in way.fields: bind["I"] = rng.randrange(1 << way.fields["I"][1])
        else:
            field, how, k = way.rules["I"]
            bind["I"] = k - rng.randrange(1 << way.fields[field][1])
    if re.search(r"\bN\b", asm):
        _, _, k = way.rules["N"]
        bind["N"] = k * rng.randrange(0, (ROOM - 512 - 16) // k)       # the bytes addressed stay within the memory the case has
    text = asm
    for h in ("D", "S", "P", "B"):
        if h in bind:
            text = re.sub(rf"\b{h}64\b", bind[h], text)
            text = re.sub(rf"\b{h}32\b", "w" + bind[h][1:], text)
    for h in table.VECTORS:
        if h in bind: text = re.sub(rf"\bv{h}\b", f"v{bind[h]}", text)
    for h in ("I", "N"):
        if h in bind: text = re.sub(rf"\b{h}\b", str(bind[h]), text)
    return bind, text


def main():
    a = sys.argv[1:]
    cases = int(a[a.index("--cases") + 1]) if "--cases" in a else 200
    rng = random.Random(int(a[a.index("--seed") + 1]) if "--seed" in a else 1)
    work = a[a.index("--work") + 1] if "--work" in a else tempfile.mkdtemp()
    os.makedirs(work, exist_ok=True)
    rows = table.read(a[a.index("--table") + 1] if "--table" in a else word.TABLE)
    if "--rows" in a: rows = [r for r in rows if r.name in a[a.index("--rows") + 1].split(",")]
    left = [r.name for r in rows if r.asm == "-"]
    todo, bodies = [], []
    with open(os.path.join(work, "cases.in"), "wb") as f:
        for row in rows:
            if row.asm == "-": continue
            for how in ("as the assembler writes it", "as the table writes it"):
                for _ in range(cases):
                    bind, text = instance(row, rng)
                    way = word.Way(row, row.bytes[0])
                    if how == "as the table writes it": text = f".long 0x{int.from_bytes(word.encode(way, bind), 'little'):08x}"
                    named = {bind[h] for h in ("D", "S", "P", "B") if h in bind}
                    home = rng.choice([i for i in range(31) if f"x{i}" not in named and not (MAC and i == 18)])
                    g = {name: rng.getrandbits(64) for name in X}
                    if "B" in bind and bind["B"] != "sp": g[bind["B"]] = BASE
                    g["sp"] = STACK
                    flags = rng.randrange(16) << 28
                    v = {i: tuple(rng.getrandbits(32) for _ in range(4)) for i in range(32)}
                    mem = bytes(rng.getrandbits(8) for _ in range(ROOM))
                    n = len(todo)
                    code, before = case_code(n, home, text)
                    todo.append((row, how, bind, text, home, g, flags, v, mem, before))
                    bodies.append(code)
                    f.write(struct.pack("<32Q", *(g[r] for r in X + ["sp"])) + struct.pack("<Q", flags) + b"".join(struct.pack("<4I", *v[i]) for i in range(32)) + mem)
    with open(os.path.join(work, "cases.S"), "w") as f:
        f.write("#ifdef __APPLE__\n#define SYM(x) _##x\n#else\n#define SYM(x) x\n#endif\n.text\n.p2align 2\n" + "\n".join(bodies)
                + "\n.data\n.p2align 3\n.globl SYM(cases)\nSYM(cases):\n" + "\n".join(f"    .quad SYM(case_{n})" for n in range(len(todo))) + "\n")
    with open(os.path.join(work, "driver.c"), "w") as f: f.write(DRIVER)
    subprocess.run(["clang", "-O1", "-o", os.path.join(work, "cross"), os.path.join(work, "driver.c"), os.path.join(work, "cases.S")], check=True)
    subprocess.run([os.path.join(work, "cross"), os.path.join(work, "cases.in"), os.path.join(work, "cases.out")], check=True)
    # the words clang wrote for the instances it assembled: each must be the word the table writes
    listing = subprocess.run(["objdump", "-d", os.path.join(work, "cross")], capture_output=True, text=True, check=True).stdout
    at, laid = None, {}
    for line in listing.splitlines():
        m = re.search(r"<_?case_(\d+)>:", line)
        if m: at = int(m.group(1)); laid[at] = []; continue
        m = re.match(r"\s*[0-9a-f]+:\s+((?:[0-9a-f]{2} ){4}|[0-9a-f]{8})\s", line)
        if m and at is not None:
            w = m.group(1).replace(" ", "")
            laid[at].append(bytes.fromhex(w) if " " in m.group(1) else int(w, 16).to_bytes(4, "little"))
    bad, other, per = 0, 0, {}
    with open(os.path.join(work, "cases.out"), "rb") as f:
        for n, (row, how, bind, text, home, g, flags, v, mem, where) in enumerate(todo):
            got = f.read(OUT)
            assert len(got) == OUT, "the run wrote less than a case's results"
            gg = dict(zip(X + ["sp"], struct.unpack("<32Q", got[:256])))
            gflags, = struct.unpack("<Q", got[256:264])
            gv = {i: struct.unpack("<4I", got[264 + 16 * i:280 + 16 * i]) for i in range(32)}
            gm = got[776:776 + ROOM]
            s = conc.run(row, bind, conc.State(g, {i: v[i] + (0,) * 12 for i in range(32)}, {SCRATCH + i: b for i, b in enumerate(mem)}, 0, 0))
            skip = {f"x{home}"} | ({"x18"} if MAC else set())
            wrong = [r for r in X + ["sp"] if r not in skip and s.g[r] != gg[r]]
            wrong += [f"v{i}" for i in range(32) if tuple(s.x[i][:4]) != gv[i]]
            wrong += ["memory"] if bytes(s.mem[SCRATCH + i] for i in range(ROOM)) != gm else []
            wrong += ["the flags"] if gflags != flags else []
            name = f"{row.name}, {how}"
            per.setdefault(name, [0, 0, 0]); per[name][0] += 1
            if how == "as the assembler writes it":
                want = word.encode(word.Way(row, row.bytes[0]), bind)
                words = laid.get(n, [])
                if where >= len(words) or words[where] != want:
                    per[name][2] += 1; other += 1
                    if per[name][2] <= 2: print(f"ANOTHER WORD {row.name}: {text}: clang {words[where].hex() if where < len(words) else '?'}, the table {want.hex()}")
            if wrong:
                per[name][1] += 1; bad += 1
                if per[name][1] <= 2: print(f"DIFFERS {name}: {text}: {', '.join(wrong)}")
    for name, (n, b, o) in per.items(): print(f"{name:42} {n} instances, {b} differ" + (f", {o} are another word than the table writes" if o else ""))
    ran = sorted({name.split(",")[0] for name in per})
    summary = {"machine": platform.machine(), "system": platform.system(), "processor": processor(), "rows run": len(ran), "instances": sum(p[0] for p in per.values()),
               "differ from the processor": bad, "another word than the table writes": other, "rows not run": left, "cases a row and way": cases}
    print(f"cross: {len(ran)} rows, each as the assembler writes it and as the table writes it, {summary['instances']} instances: {bad} differ from this processor"
          + ("" if bad else ": every row run is what the processor does") + f"; {other} of the assembler's words are not the table's"
          + (f"; {len(left)} rows are not run: {', '.join(left)}" if left else ""))
    if "--out" in a:
        with open(a[a.index("--out") + 1], "w") as f: json.dump(summary, f, indent=1, sort_keys=True); f.write("\n")
    sys.exit(1 if bad or other else 0)


def processor():
    """What this machine says its processor is."""
    if MAC: return subprocess.run(["sysctl", "-n", "machdep.cpu.brand_string"], capture_output=True, text=True).stdout.strip()
    try:
        with open("/proc/cpuinfo") as f: text = f.read()
    except OSError: return ""
    found = dict(re.findall(r"^(CPU implementer|CPU part|model name)\s*:\s*(.+)$", text, flags=re.M))
    return found.get("model name") or f"implementer {found.get('CPU implementer', '?')}, part {found.get('CPU part', '?')}"


if __name__ == "__main__":
    main()
