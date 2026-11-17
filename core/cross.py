#!/usr/bin/env python3
"""cross: every row of the instruction table against this machine's processor.

    python3 cross.py [--cases N] [--seed S] [--work DIR] [--table FILE] [--rows NAME,NAME...]
    (x86-64 Linux with AVX-512; needs clang)

For each row of x86.tab, N random instances (registers, numbers, displacements chosen at random) are
assembled from the row's ASM by clang and run on the processor from random states: the sixteen general
registers (the stack pointer among them: it points into the memory below), the flags, the thirty-two vector
registers' 512 bits, seven mask registers, and 1024 bytes of memory that base registers and the stack
pointer point into. What the processor leaves is compared with what the row's EFFECT says (table.py), part
by part: a part the row calls `unknown` is left out, and a part the row does not mention must be as it was.
For a jump, whether it was taken. Exit 1 if any instance differs.

Not run: rows whose ASM is `-` (they are named at the end)."""
import os, random, re, struct, subprocess, sys, tempfile
import table

G64 = "rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15".split()
G32 = "eax ecx edx ebx esp ebp esi edi r8d r9d r10d r11d r12d r13d r14d r15d".split()
G8 = "al cl dl bl spl bpl sil dil r8b r9b r10b r11b r12b r13b r14b r15b".split()
SCRATCH, ROOM = 0x60000000, 1024
BASE, STACK = SCRATCH + 256, SCRATCH + 512          # where a base register points, and the stack pointer
IN = 128 + 8 + 2048 + 16 + ROOM
OUT = 128 + 2048 + 16 + ROOM + 3

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
    mov [rip + real_rsp], rsp
    lea rax, [rip + cases]
    mov rax, [rax + rdi * 8]
    mov [rip + target], rax
%(load)s
    jmp qword ptr [rip + target]
done:
%(save)s
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
.globl in_g, in_flags, in_x, in_k, out_g, out_x, out_k, out_zf, out_cf, out_taken
target: .skip 8
real_rsp: .skip 8
in_g: .skip 128
in_flags: .skip 8
in_x: .skip 2048
in_k: .skip 16
out_g: .skip 128
out_x: .skip 2048
out_k: .skip 16
out_zf: .skip 1
out_cf: .skip 1
out_taken: .skip 1
.section .note.GNU-stack,"",%%progbits
"""
LOAD = ("\n".join(f"    vmovdqu32 zmm{i}, [rip + in_x + {64 * i}]" for i in range(32)) + "\n"
        + "\n".join(f"    kmovw k{i}, word ptr [rip + in_k + {2 * i}]" for i in range(1, 8)) + "\n"
        + "    push qword ptr [rip + in_flags]\n    popfq\n"
        + "\n".join(f"    mov {r}, [rip + in_g + {8 * i}]" for i, r in enumerate(G64)))
SAVE = ("\n".join(f"    mov [rip + out_g + {8 * i}], {r}" for i, r in enumerate(G64)) + "\n"
        + "    setz byte ptr [rip + out_zf]\n    setc byte ptr [rip + out_cf]\n    mov rsp, [rip + real_rsp]\n"
        + "\n".join(f"    vmovdqu32 [rip + out_x + {64 * i}], zmm{i}" for i in range(32)) + "\n"
        + "\n".join(f"    kmovw word ptr [rip + out_k + {2 * i}], k{i}" for i in range(1, 8)))

DRIVER = r"""
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sys/mman.h>
#define ROOM 1024
extern uint64_t in_g[16], out_g[16], in_flags; extern uint8_t in_x[2048], out_x[2048], in_k[16], out_k[16], out_zf, out_cf, out_taken;
void run_case(long k);
int main(int argc, char **argv) {
    uint8_t *m = mmap((void *)0x60000000, 4096, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0);
    if (m != (uint8_t *)0x60000000) return 2;
    FILE *in = fopen(argv[1], "rb"), *out = fopen(argv[2], "wb");
    if (!in || !out) return 2;
    for (long k = 0; ; k++) {
        if (fread(in_g, 8, 16, in) != 16) break;
        if (fread(&in_flags, 8, 1, in) != 1 || fread(in_x, 1, 2048, in) != 2048 || fread(in_k, 1, 16, in) != 16 || fread(m, 1, ROOM, in) != ROOM) return 2;
        out_taken = 0;
        run_case(k);
        fwrite(out_g, 8, 16, out); fwrite(out_x, 1, 2048, out); fwrite(out_k, 1, 16, out); fwrite(m, 1, ROOM, out);
        fwrite(&out_zf, 1, 1, out); fwrite(&out_cf, 1, 1, out); fwrite(&out_taken, 1, 1, out);
    }
    return fclose(out) != 0;
}
"""


def number(asm, rng):
    """A number for the row's I: one the instruction can hold."""
    first = asm.split()[0]
    if first in ("shl", "shr"): return rng.randrange(0, 32 if "32" in asm.split(",")[0] else 64)
    if first in ("vpslld", "vpsrld"): return rng.choice([rng.randrange(0, 32), rng.randrange(0, 256)])
    if "mm" in asm or " al," in asm or "byte ptr" in asm: return rng.randrange(256)
    if first == "mov" and "32" in asm.split(",")[0]: return rng.getrandbits(32)
    return rng.choice([rng.randrange(-2 ** 31, 2 ** 31), rng.randrange(-128, 128), rng.randrange(0, 2 ** 16)])


def instance(row, rng):
    """One instance of a row: what each placeholder is, the instruction as the assembler takes it, and what the
    registers that address memory must hold."""
    asm, bind, fixed = row.asm, {}, {}
    index = "S" if re.search(r"\[B64 \+ S64", asm) else None
    for h in ("B", "D", "S", "P"):
        if re.search(rf"\b{h}(64|32|8)\b", asm):
            bind[h] = rng.choice([r for r in G64 if not (r == "rsp" and (h == "P" or h == index)) and not (h == index and r == bind.get("B"))])
    for h in table.VECTORS:
        if re.search(rf"mm{h}\b", asm): bind[h] = rng.randrange(32 if "zmm" + h in asm else 16)
    if re.search(r"\bkM\b", asm): bind["M"] = rng.randrange(1, 8)
    if re.search(r"\bI\b", asm): bind["I"] = number(asm, rng)
    if re.search(r"\bN\b", asm): bind["N"] = 64 * rng.randrange(-2, 3) if "vmovdqa32" in asm else rng.randrange(-128, 129)
    if "B" in bind: fixed[bind["B"]] = BASE
    if index: fixed[bind[index]] = 4 * rng.randrange(0, 65)
    text = asm
    for h in table.REGISTERS:
        if h in bind:
            i = G64.index(bind[h])
            text = re.sub(rf"\b{h}64\b", G64[i], text); text = re.sub(rf"\b{h}32\b", G32[i], text); text = re.sub(rf"\b{h}8\b", G8[i], text)
    for h in table.VECTORS:
        if h in bind: text = re.sub(rf"mm{h}\b", f"mm{bind[h]}", text)
    if "M" in bind: text = re.sub(r"\bkM\b", f"k{bind['M']}", text)
    if "I" in bind: text = re.sub(r"\bI\b", str(bind["I"]), text)
    if "N" in bind: text = re.sub(r"\bN\b", str(bind["N"]), text)
    return bind, text, fixed


def main():
    a = sys.argv[1:]
    cases = int(a[a.index("--cases") + 1]) if "--cases" in a else 200
    rng = random.Random(int(a[a.index("--seed") + 1]) if "--seed" in a else 1)
    work = a[a.index("--work") + 1] if "--work" in a else tempfile.mkdtemp()
    os.makedirs(work, exist_ok=True)
    rows = table.read(a[a.index("--table") + 1]) if "--table" in a else table.read()
    if "--rows" in a: rows = [r for r in rows if r.name in a[a.index("--rows") + 1].split(",")]
    left = [r.name for r in rows if r.asm == "-"]; rows = [r for r in rows if r.asm != "-"]
    todo, bodies = [], []
    with open(os.path.join(work, "cases.in"), "wb") as f:
        for row in rows:
            jump = any(st[0] == "jump" for st in row.effect)
            for _ in range(cases):
                bind, text, fixed = instance(row, rng)
                g = {name: rng.getrandbits(64) for name in G64}
                g.update(fixed); g["rsp"] = STACK
                zf, cf = rng.randrange(2), rng.randrange(2)
                x = {i: tuple(rng.getrandbits(32) for _ in range(16)) for i in range(32)}
                k = {i: tuple(rng.randrange(2) for _ in range(16)) for i in range(1, 8)}
                mem = bytes(rng.getrandbits(8) for _ in range(ROOM))
                n = len(todo)
                if jump: bind["I"] = 1; text = re.sub(r"\bI\b", f"taken_{n}", row.asm) + f"\n    jmp done\ntaken_{n}:\n    mov byte ptr [rip + out_taken], 1"
                todo.append((row, bind, text, g, x, k, mem, zf, cf))
                bodies.append(f"case_{n}:\n    {text}\n    jmp done")
                f.write(struct.pack("<16Q", *(g[r] for r in G64)) + struct.pack("<Q", 0x202 | zf << 6 | cf) + b"".join(struct.pack("<16I", *x[i]) for i in range(32))
                        + b"\0\0" + b"".join(struct.pack("<H", sum(b << j for j, b in enumerate(k[i]))) for i in range(1, 8)) + mem)
    with open(os.path.join(work, "cases.S"), "w") as f:
        f.write(STUB % {"load": LOAD, "save": SAVE, "bodies": "\n".join(bodies), "table": "\n".join(f"    .quad case_{n}" for n in range(len(todo)))})
    with open(os.path.join(work, "driver.c"), "w") as f: f.write(DRIVER)
    subprocess.run(["clang", "-O1", "-no-pie", "-o", os.path.join(work, "cross"), os.path.join(work, "driver.c"), os.path.join(work, "cases.S")], check=True)
    subprocess.run([os.path.join(work, "cross"), os.path.join(work, "cases.in"), os.path.join(work, "cases.out")], check=True)
    bad, per = 0, {}
    with open(os.path.join(work, "cases.out"), "rb") as f:
        for row, bind, text, g, x, k, mem, zf, cf in todo:
            got = f.read(OUT)
            assert len(got) == OUT, "the run wrote less than a case's results"
            gg = dict(zip(G64, struct.unpack("<16Q", got[:128])))
            gx = {i: struct.unpack("<16I", got[128 + 64 * i:192 + 64 * i]) for i in range(32)}
            gk = {i: tuple((struct.unpack("<H", got[2176 + 2 * i:2178 + 2 * i])[0] >> j) & 1 for j in range(16)) for i in range(1, 8)}
            gm, gzf, gcf, taken = got[2192:2192 + ROOM], got[2192 + ROOM], got[2193 + ROOM], got[2194 + ROOM]
            s = table.run(row, bind, table.State(g, x, {SCRATCH + i: b for i, b in enumerate(mem)}, zf, cf, k))
            wrong = [n for n in G64 if s.g[n] != table.UNKNOWN and s.g[n] != gg[n]]
            wrong += [f"zmm{i}" for i in range(32) if any(w != table.UNKNOWN and w != v for w, v in zip(s.x[i], gx[i]))]
            wrong += [f"k{i}" for i in range(1, 8) if tuple(s.k[i]) != gk[i]]
            wrong += ["memory"] if bytes(s.mem[SCRATCH + i] for i in range(ROOM)) != gm else []
            wrong += [n for n, v, w in (("zf", s.zf, gzf), ("cf", s.cf, gcf)) if v != table.UNKNOWN and v != w]
            wrong += ["whether it jumps"] if (s.to is not None) != bool(taken) else []
            per.setdefault(row.name, [0, 0]); per[row.name][0] += 1
            if wrong:
                per[row.name][1] += 1; bad += 1
                if per[row.name][1] <= 2: print(f"DIFFERS {row.name}: {text.splitlines()[0]}: {', '.join(wrong)}")
    for name, (n, b) in per.items(): print(f"{name:13} {n} instances, {b} differ")
    print(f"cross: {len(rows)} rows, {len(todo)} instances, {bad} differ from this processor" + ("" if bad else ": every row run is what the processor does")
          + (f"; {len(left)} rows are not run: {', '.join(left)}" if left else ""))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
