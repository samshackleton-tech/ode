#!/usr/bin/env python3
"""decoder: every row's ASM against its ROW, by the verifier's decoder.

    python3 decoder.py [--cases N] [--seed S]        (needs clang; any machine: nothing is run)

A row joins three things: how an assembler writes the instruction (ASM), how the decoder writes it (ROW)
and what it does (EFFECT). cross.py runs ASM on a processor against EFFECT. This holds ASM against ROW: N
random instances of each row are assembled, the verifier's decoder (kcheck/kdecode.py) reads the bytes,
and what it reads must be an instance of this row's ROW with the same registers and numbers (an assembler
may exchange the two sources of a sum, an xor or an or: that is the same instance). Where the decoder stops (an encoding it does not know: it knows only what the
shipped code uses) nothing is compared; a row none of whose instances the decoder reads is named.
Exit 1 if an instance is read as anything else."""
import os, random, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "kcheck")); sys.path.insert(0, HERE)
import kdecode, kterms
import cross, table

M64, M32 = table.M64, table.M32


def swappable(row):
    """A row whose effect is one of add32, xor32, or32 of each pair of lanes of Y and Z: the same with the two exchanged."""
    st = row.effect[0]
    return len(row.effect) == 1 and st[0] == "set" and st[2][0] == "call" and st[2][1] == "each32" and st[2][2][0] in (("name", "add32"), ("name", "xor32"), ("name", "and32"), ("name", "or32")) \
        and [x[1] for x in st[2][2][1:]] in (["Y", "Z"], ["Y512", "Z512"])


def main():
    a = sys.argv[1:]
    cases = int(a[a.index("--cases") + 1]) if "--cases" in a else 40
    rng = random.Random(int(a[a.index("--seed") + 1]) if "--seed" in a else 1)
    rows = [r for r in table.read() if r.asm != "-" and "DATA" not in r.asm]        # (a row that reads the file's data: the decoder needs the file)
    todo, text = [], [".intel_syntax noprefix", ".text"]
    for row in rows:
        jump = any(st[0] == "jump" for st in row.effect)
        for _ in range(cases):
            bind, ins, _ = cross.instance(row, rng)
            k = len(todo)
            if jump: ins = ins.replace(str(bind["I"]), f"c_{k}")                 # a jump to itself: where it goes is not compared
            todo.append((row, bind, ins, jump))
            text += [f".globl c_{k}", f"c_{k}:", f"    {ins}", "    ret"]
    work = tempfile.mkdtemp()
    with open(os.path.join(work, "all.S"), "w") as f: f.write("\n".join(text) + "\n.section .note.GNU-stack,\"\",%progbits\n")
    subprocess.run(["clang", "--target=x86_64-unknown-linux-gnu", "-c", "-o", os.path.join(work, "all.o"), os.path.join(work, "all.S")], check=True)
    with open(os.path.join(work, "all.o"), "rb") as f: obj = f.read()
    read, bad, stopped, why = {}, 0, {}, {}
    for k, (row, bind, ins, jump) in enumerate(todo):
        try: decoded = kdecode.read(obj, f"c_{k}", 0x10000, 0x50000000)[0][0][2]
        except kdecode.Stop as e:
            stopped[row.name] = stopped.get(row.name, 0) + 1; why.setdefault(row.name, f"{ins}: {e}"); continue
        # (the instruction's row is the first of the table it is an instance of; an instance of this row may be one of an
        # earlier, narrower row too, as an xor of a register with itself is: what matters here is that it is one of this row)
        got = row.match(table.parse_row(decoded))
        wrong = None
        if got is None: wrong = "not an instance of its row"
        else:
            for h, v in bind.items():
                g = got.get(h)
                if h in table.NUMBERS:
                    if jump and h == "I": continue
                    mask = M32 if h == "I" and "D32, I" in row.asm else M64
                    if g is None or kterms.num(g) & mask != v & mask: wrong = f"{h} is {g}, not {v}"
                elif g != v: wrong = f"{h} is {g}, not {v}"
        if wrong and got is not None and swappable(row) and {**got, "Y": got["Z"], "Z": got["Y"]} == {h: (v if h not in table.NUMBERS else got[h]) for h, v in bind.items()}:
            wrong = None                                                         # the assembler has exchanged the two sources of a sum, an xor or an or: the same thing
        read[row.name] = read.get(row.name, 0) + 1
        if wrong:
            bad += 1
            if bad <= 12: print(f"DIFFERS {row.name}: `{ins}` is read as `{decoded}`: {wrong}")
    if "--why" in a:
        for name, n in sorted(stopped.items()): print(f"stops at {n} of {name}, e.g. {why[name]}")
    never = [f"{r.name} (e.g. {why[r.name]})" for r in rows if not read.get(r.name)]
    print(f"decoder: {len(rows)} rows, {len(todo)} instances assembled; the decoder reads {sum(read.values())} of them, {bad} otherwise than as their row"
          + f"; it stops at {sum(stopped.values())} (encodings it does not know)" + (f"; NO INSTANCE READ of: {'; '.join(never)}" if never else ""))
    return 1 if bad or never else 0


if __name__ == "__main__":
    sys.exit(main())
