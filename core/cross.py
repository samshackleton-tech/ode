#!/usr/bin/env python3
"""cross: every row of the instruction table against this machine's processor.

    python3 cross.py [--cases N] [--seed S] [--work DIR] [--table FILE]      (x86-64 Linux; needs clang)

For each row of x86.tab, N random instances (registers, immediates, displacements chosen at random) are
assembled from the row's ASM by clang and run on the processor from random states: every general register
but the stack pointer, the sixteen vector registers' low 128 bits, and 256 bytes of memory that the base
register points into. What the processor leaves is compared with what the row's EFFECT says (table.py),
part by part; a part the row calls `unknown` is left out. Exit 1 if any instance differs.

Not compared yet, and said so in the output: the flags a row leaves alone (the states do not set them); the
stack pointer as an operand; bits of vector registers above 127."""
import os, random, struct, subprocess, sys, tempfile
import table

G64 = "rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15".split()
G32 = "eax ecx edx ebx esp ebp esi edi r8d r9d r10d r11d r12d r13d r14d r15d".split()
G8 = "al cl dl bl spl bpl sil dil r8b r9b r10b r11b r12b r13b r14b r15b".split()
SCRATCH, ROOM = 0x60000000, 256
FREE = [i for i in range(16) if i != 4]

STUB = """.intel_syntax noprefix
.text
.globl run_case
run_case:
    push rbx
    push rbp
    push r12
    push r13
    push r14
    push r15
    lea rax, [rip + cases]
    mov rax, [rax + rdi * 8]
    mov [rip + target], rax
%(load)s
    jmp qword ptr [rip + target]
done:
%(save)s
    setz byte ptr [rip + out_zf]
    setc byte ptr [rip + out_cf]
    vzeroupper
    pop r15
    pop r14
    pop r13
    pop r12
    pop rbp
    pop rbx
    ret
%(bodies)s
.data
cases:
%(table)s
.bss
.globl in_g, in_x, out_g, out_x, out_zf, out_cf
target: .skip 8
in_g: .skip 128
in_x: .skip 256
out_g: .skip 128
out_x: .skip 256
out_zf: .skip 1
out_cf: .skip 1
.section .note.GNU-stack,"",%%progbits
"""

DRIVER = r"""
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sys/mman.h>
extern uint64_t in_g[16], out_g[16]; extern uint8_t in_x[256], out_x[256], out_zf, out_cf;
void run_case(long k);
int main(int argc, char **argv) {
    uint8_t *m = mmap((void *)0x60000000, 4096, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0);
    if (m != (uint8_t *)0x60000000) return 2;
    FILE *in = fopen(argv[1], "rb"), *out = fopen(argv[2], "wb");
    if (!in || !out) return 2;
    for (long k = 0; ; k++) {
        if (fread(in_g, 8, 16, in) != 16) break;
        if (fread(in_x, 1, 256, in) != 256 || fread(m, 1, 256, in) != 256) return 2;
        run_case(k);
        fwrite(out_g, 8, 16, out); fwrite(out_x, 1, 256, out); fwrite(m, 1, 256, out); fwrite(&out_zf, 1, 1, out); fwrite(&out_cf, 1, 1, out);
    }
    return fclose(out) != 0;
}
"""


def instance(row, rng):
    """One instance of a row: what each placeholder is, and the instruction as the assembler takes it."""
    bind, asm = {}, row.asm
    for h in "DSB":
        if any(h + w in asm for w in ("64", "32", "8")):
            bind[h] = G64[rng.choice(FREE)]
    for h in "XYZ":
        if "xmm" + h in asm: bind[h] = rng.randrange(16)
    if " I" in asm or asm.endswith("I"):
        first = asm.split()[0]
        if first in ("shl", "shr"): bind["I"] = rng.randrange(1, 64)
        elif first == "vprord": bind["I"] = rng.randrange(1, 32)
        elif "xmm" in asm or " al," in asm: bind["I"] = rng.randrange(256)
        else: bind["I"] = rng.choice([rng.randrange(-2 ** 31, 2 ** 31), rng.randrange(-128, 128), rng.randrange(0, 2 ** 16)])
    if "N]" in asm: bind["N"] = 8 * rng.randrange(0, 13)
    text = asm
    for h in "DSB":
        if h in bind:
            i = G64.index(bind[h])
            text = text.replace(h + "64", G64[i]).replace(h + "32", G32[i]).replace(h + "8", G8[i])
    for h in "XYZ":
        if h in bind: text = text.replace("xmm" + h, f"xmm{bind[h]}")
    if "I" in bind: text = text[:-1] + str(bind["I"]) if text.endswith("I") else text.replace(" I", f" {bind['I']}")
    if "N" in bind: text = text.replace("N]", f"{bind['N']}]")
    return bind, text


def main():
    a = sys.argv[1:]
    cases = int(a[a.index("--cases") + 1]) if "--cases" in a else 200
    rng = random.Random(int(a[a.index("--seed") + 1]) if "--seed" in a else 1)
    work = a[a.index("--work") + 1] if "--work" in a else tempfile.mkdtemp()
    os.makedirs(work, exist_ok=True)
    rows = table.read(a[a.index("--table") + 1]) if "--table" in a else table.read()
    todo, blob = [], b""
    for row in rows:
        for _ in range(cases):
            bind, text = instance(row, rng)
            g = {name: rng.getrandbits(64) for name in G64}
            if "B" in bind: g[bind["B"]] = SCRATCH + 64
            x = {i: tuple(rng.getrandbits(32) for _ in range(4)) for i in range(16)}
            mem = bytes(rng.getrandbits(8) for _ in range(ROOM))
            todo.append((row, bind, text, g, x, mem))
            blob += struct.pack("<16Q", *(g[n] for n in G64)) + b"".join(struct.pack("<4I", *x[i]) for i in range(16)) + mem
    load = "\n".join(f"    vmovdqu xmm{i}, [rip + in_x + {16 * i}]" for i in range(16)) + "\n" + "\n".join(f"    mov {G64[i]}, [rip + in_g + {8 * i}]" for i in FREE)
    save = "\n".join(f"    mov [rip + out_g + {8 * i}], {G64[i]}" for i in FREE) + "\n" + "\n".join(f"    vmovdqu [rip + out_x + {16 * i}], xmm{i}" for i in range(16))
    bodies = "\n".join(f"case_{k}:\n    {t[2]}\n    jmp done" for k, t in enumerate(todo))
    with open(os.path.join(work, "cases.S"), "w") as f:
        f.write(STUB % {"load": load, "save": save, "bodies": bodies, "table": "\n".join(f"    .quad case_{k}" for k in range(len(todo)))})
    with open(os.path.join(work, "driver.c"), "w") as f: f.write(DRIVER)
    with open(os.path.join(work, "cases.in"), "wb") as f: f.write(blob)
    subprocess.run(["clang", "-O1", "-no-pie", "-o", os.path.join(work, "cross"), os.path.join(work, "driver.c"), os.path.join(work, "cases.S")], check=True)
    subprocess.run([os.path.join(work, "cross"), os.path.join(work, "cases.in"), os.path.join(work, "cases.out")], check=True)
    with open(os.path.join(work, "cases.out"), "rb") as f: out = f.read()
    size = 128 + 256 + ROOM + 2
    assert len(out) == size * len(todo), (len(out), size * len(todo))
    bad, per = 0, {}
    for k, (row, bind, text, g, x, mem) in enumerate(todo):
        got = out[k * size:(k + 1) * size]
        gg = dict(zip(G64, struct.unpack("<16Q", got[:128])))
        gx = {i: struct.unpack("<4I", got[128 + 16 * i:144 + 16 * i]) for i in range(16)}
        gm, zf, cf = got[384:384 + ROOM], got[384 + ROOM], got[385 + ROOM]
        s = table.run(row, bind, table.State(g, x, {SCRATCH + i: b for i, b in enumerate(mem)}, table.UNKNOWN, table.UNKNOWN))
        wrong = [n for n in G64 if n != "rsp" and s.g[n] != table.UNKNOWN and s.g[n] != gg[n]]
        wrong += [f"xmm{i}" for i in range(16) if tuple(s.x[i]) != tuple(gx[i])]
        wrong += ["memory"] if bytes(s.mem[SCRATCH + i] for i in range(ROOM)) != gm else []
        wrong += [f for f, v, w in (("zf", s.zf, zf), ("cf", s.cf, cf)) if v != table.UNKNOWN and v != w]
        per.setdefault(row.name, [0, 0]); per[row.name][0] += 1
        if wrong:
            per[row.name][1] += 1; bad += 1
            if per[row.name][1] <= 2: print(f"DIFFERS {row.name}: {text}: {', '.join(wrong)}")
    for name, (n, b) in per.items(): print(f"{name:11} {n} instances, {b} differ")
    print(f"cross: {len(rows)} rows, {len(todo)} instances, {bad} differ from this processor"
          + ("" if bad else ": every row is what the processor does") + " (flags a row leaves alone, the stack pointer, and vector bits above 127: not compared)")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
