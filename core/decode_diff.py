#!/usr/bin/env python3
"""decode_diff: the reader of code by the table (decode.py) beside the reader written by hand (kdecode.decode).

    python3 decode_diff.py [--flips] [--jobs N] FILE...        (in the kcheck folder's files; default: every shipped file)

Every instruction of every function the files give a linker is read both ways; with --flips, so is what
follows every single-bit change of the functions' bytes (from the changed instruction to the function's
end). Counted apart:
    same            both read the same row, or both refuse
    no row          the reader by hand writes a row that is an instance of no row of the table (the verifier would
                    refuse it at that instruction); the reader by the table refuses the bytes
    DIFFERS         both read a row, and not the same
    STRICTER        the table refuses what the reader by hand reads as an instance of a row
    WIDER           the table reads what the reader by hand refuses
A file of the tools' kind (an object with relocations) is read too when it is named."""
import os, sys
from concurrent.futures import ProcessPoolExecutor
import multiprocessing

HERE = os.path.dirname(os.path.abspath(__file__))
KCHECK = os.path.join(HERE, "..", "kcheck")
sys.path.insert(0, KCHECK); sys.path.insert(0, HERE)
import kdecode, table, decode

BASE = 0x10000


def both(text, at, relocs, rodata, start):
    out = []
    for f in (kdecode.decode, kdecode.by_table):
        try: out.append(f(text, at, relocs, rodata, 0, BASE, start))
        except kdecode.Stop: out.append(None)
        except Exception as e: out.append(("CRASH", f"{type(e).__name__}: {e}"))
    return out


def judge(old, new):
    if old == new: return "same"
    if old and old[0] == "CRASH" or new and new[0] == "CRASH": return "CRASH"
    if old and new: return "DIFFERS"
    if old: return "no row" if table.find(decode.HEADS, table.parse_row(old[1]))[0] is None else "STRICTER"
    return "WIDER"


def walk(text, start, relocs, rodata, at, count, notes, where):
    """Read on from `at` both ways until either refuses or the function ends."""
    while True:
        old, new = both(text, at, relocs, rodata, start)
        kind = judge(old, new)
        count[kind] = count.get(kind, 0) + 1
        if kind == "STRICTER":
            # why: is it the same instance, written otherwise than the table writes it?
            why = "the table has no way to write it"
            for way, bind, n in decode.candidates(text, at, BASE + at - start):
                try: written = decode.encode.encode(way, bind, BASE + at - start)
                except decode.encode.Refuse: continue
                if way.late: continue
                if way.fill(bind) == old[1] and written != bytes(text[at:at + n]): why = "the same instance, which the table writes otherwise"
            kind = f"STRICTER ({why})"
            count[kind] = count.get(kind, 0) + 1
        if kind != "same" and len(notes.setdefault(kind, [])) < 400:
            notes[kind].append(f"{where} +{at - start:#x} {bytes(text[at:at + 12]).hex(' ')}: by hand {old}; by the table {new}")
        if kind != "same" or old is None or old[1] == ".ret" or at + old[0] >= len(text): return
        at += old[0]


def one(job):
    path, name, flips = job
    count, notes = {}, {}
    e = kdecode.Elf(path)
    text, start, relocs, rodata = kdecode.place(e, name)
    where = f"{os.path.basename(path)} {name}"
    rows, at = [], start
    while True:                                 # the instructions as they are (by hand), to know where each starts
        try: n, ins = kdecode.decode(text, at, relocs, rodata, 0, BASE, start)
        except kdecode.Stop: break
        rows.append((at, n)); at += n
        if ins == ".ret": break
    walk(text, start, relocs, rodata, start, count, notes, where)
    if flips:
        text = bytearray(text)
        for at, n in rows:
            for k in range(at, at + n):
                for bit in range(8):
                    text[k] ^= 1 << bit
                    walk(text, start, relocs, rodata, at, count, notes, f"{where} (bit {bit} of +{k - start:#x})")
                    text[k] ^= 1 << bit
    return count, notes


def main():
    a = sys.argv[1:]
    flips = "--flips" in a
    jobs = int(a[a.index("--jobs") + 1]) if "--jobs" in a else 8
    files = [x for k, x in enumerate(a) if not x.startswith("--") and (k == 0 or a[k - 1] != "--jobs")]
    if not files:
        files = [os.path.join(KCHECK, "b3hashr.o")] + sorted(os.path.join(KCHECK, "programs", d, f) for d in os.listdir(os.path.join(KCHECK, "programs"))
                                                             if os.path.isdir(os.path.join(KCHECK, "programs", d)) for f in os.listdir(os.path.join(KCHECK, "programs", d)) if f.startswith("ode") and f.endswith(".o"))
    todo = []
    for path in files:
        e = kdecode.Elf(path)
        if kdecode.settled(e): names = sorted(kdecode.Settled(e).at)
        else: names = sorted(s["name"] for s in e.symbols if s["name"] and s["type"] in (0, 2) and s["bind"] == 1 and s["shndx"] == e.index.get(".text"))
        todo += [(path, name, flips) for name in names]
    count, notes = {}, {}
    with ProcessPoolExecutor(jobs, mp_context=multiprocessing.get_context("fork")) as pool:
        for c, n in pool.map(one, todo):
            for k, v in c.items(): count[k] = count.get(k, 0) + v
            for k, v in n.items(): notes.setdefault(k, []).extend(v)
    for kind in sorted(notes):
        if "no way" in kind:
            heads = {}
            for line in notes[kind]: h = line.split(": by hand (")[1].split("'")[1].split()[0]; heads[h] = heads.get(h, 0) + 1
            print(f"{kind}, by the row read by hand: {heads}")
        seen = set()
        for line in notes[kind]:
            key = line.split(": by hand ")[1][:60]
            if key in seen or len(seen) >= 12: continue
            seen.add(key); print(f"{kind}: {line[:330]}")
    print(f"decode_diff: {len(files)} files, {len(todo)} functions" + (", every single-bit change of their bytes" if flips else "") + ": "
          + ", ".join(f"{count.get(k, 0)} {k}" for k in ("same", "no row", "DIFFERS", "STRICTER", "WIDER", "CRASH"))
          + "".join(f"; {v} {k}" for k, v in sorted(count.items()) if k.startswith("STRICTER (")))
    return 1 if any(count.get(k) for k in ("DIFFERS", "CRASH")) else 0


if __name__ == "__main__":
    sys.exit(main())
