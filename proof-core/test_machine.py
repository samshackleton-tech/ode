#!/usr/bin/env python3
"""The machine as Machine.lean says it against the machine as ../core/conc.py says it.

    python3 test_machine.py [CASES]        (skipped where Lean's `lake` is not installed)

The theorem in SoundTop.lean is about the machine of Machine.lean. Processors were compared with conc.py
(../core/cross.py). Both read the same table; each works a row's EFFECT out in its own code. Here every row
of the table is run from random states by both: random registers and numbers, the flags, 1024 bytes of
memory that a base register and the stack pointer point into. Part by part they must leave the same: the
sixteen registers, the two flags, memory, and where a jump goes. A part conc.py calls unknown is left out.

A row that has no meaning in Machine.lean (a vector register, a call, the address of the file's data) is
named, and no function that has such a row is verified there. A return is no row conc.py runs; what
Machine.lean does at one is compared with what is said here: the address at the stack pointer is taken and
the stack pointer goes up by eight.

A control: with one row's effect changed in the table Machine.lean reads, the two must differ."""
import os, random, re, shutil, subprocess, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
CORE = os.path.join(HERE, "..", "core")
sys.path.insert(0, CORE)
import conc, cross, table

LAKE = shutil.which("lake") or (os.path.expanduser("~/.elan/bin/lake") if os.path.exists(os.path.expanduser("~/.elan/bin/lake")) else None)
G64, SCRATCH, ROOM, STACK = cross.G64, cross.SCRATCH, cross.ROOM, cross.STACK
FUNCTION = 0x400000                       # where the function is taken to start; a jump's number counts from there
# the rows the functions verified in Lean so far are made of: each must be among the rows compared
NEEDED = ["mov64_rr", "mov64_ri", "mov64_rm", "mov64_mr", "add64_rr", "add64_ri", "sub64_ri", "cmp64_rr", "cmp64_ri",
          "movzx8_rm", "xor32_same", "dec64", "lea", "push", "pop", "jmp", "je", "jne", "jae", "jb"]


def fill(row, bind):
    """The decoded row of this instance, as the reader of code writes it."""
    def one(m):
        t = m.group(0)
        if t[:1] == "." and t[1:] in table.REGISTERS: return "." + bind[t[1:]]
        return str(bind[t]) if t in table.NUMBERS else t
    return re.sub(r"[^\s()]+", one, row.row)


def cases(rows, n, rng):
    """For each row n instances and states: (row, bind, registers, flags, memory, the number an unknown is, where the next instruction is)."""
    out = []
    for row in rows:
        if row.asm == "-" or "DATA" in row.asm or any(v in row.row.split() for v in table.VECTORS + table.MASKS): continue
        for _ in range(n):
            bind, _, fixed = cross.instance(row, rng)
            if any(st[0] == "jump" for st in row.effect): bind["I"] = rng.randrange(1 << 16)
            g = {name: rng.getrandbits(64) for name in G64}
            g.update(fixed); g["rsp"] = STACK
            out.append((row, bind, g, rng.randrange(2), rng.randrange(2), bytes(rng.getrandbits(8) for _ in range(ROOM)),
                        rng.getrandbits(64), rng.randrange(1 << 16)))
    return out


def lean(tab, todo, work):
    """What Machine.lean leaves, case by case: (kind, rip, zf, cf, registers, memory) or the word it answers."""
    path = os.path.join(work, "cases.txt")
    with open(path, "w") as f:
        for row, bind, g, zf, cf, mem, u, nxt in todo:
            f.write(f"c {FUNCTION} {nxt} {u} {zf} {cf} {' '.join(str(g[r]) for r in G64)} {SCRATCH} {mem.hex()} | {fill(row, bind)}\n")
    got = subprocess.run([os.path.join(HERE, ".lake", "build", "bin", "odemachine"), tab, path], capture_output=True, text=True, check=True).stdout.split("\n")
    out = []
    for line in got[:len(todo)]:
        w = line.split()
        out.append(line if len(w) < 21 else (w[0], int(w[1]), int(w[2]), int(w[3]), [int(x) for x in w[4:20]], bytes.fromhex(w[20])))
    assert len(out) == len(todo), "the Lean program answered fewer cases than it was given"
    return out


def compare(todo, answers):
    """({row: instances compared}, {row: why it differs, the first time}, rows with no meaning in Lean)."""
    same, differs, none = {}, {}, set()
    for (row, bind, g, zf, cf, mem, u, nxt), got in zip(todo, answers):
        if got == "none": none.add(row.name); continue
        if isinstance(got, str): differs.setdefault(row.name, f"Lean answers `{got}` to {fill(row, bind)}"); continue
        s = conc.run(row, bind, conc.State(g, {i: (0,) * 16 for i in range(32)}, {SCRATCH + i: b for i, b in enumerate(mem)}, zf, cf, {}))
        kind, rip, lzf, lcf, regs, lmem = got
        wrong = [n for n, v in zip(G64, regs) if s.g[n] != table.UNKNOWN and s.g[n] != v]
        wrong += [n for n, v, w in (("zf", s.zf, lzf), ("cf", s.cf, lcf)) if v != table.UNKNOWN and int(v) != w]
        wrong += ["memory"] if bytes(s.mem[SCRATCH + i] for i in range(ROOM)) != lmem else []
        wrong += ["where it goes on"] if rip != FUNCTION + (nxt if s.to is None else s.to) or kind != "next" else []
        if wrong: differs.setdefault(row.name, f"{fill(row, bind)}: {', '.join(wrong)}")
        else: same[row.name] = same.get(row.name, 0) + 1
    return same, differs, none


@unittest.skipUnless(LAKE, "Lean's lake is not installed")
class Machine(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        subprocess.run([LAKE, "build", "odemachine"], cwd=HERE, check=True, capture_output=True)
        cls.n = int(os.environ.get("MACHINE_CASES", "60"))
        cls.rows = table.read()
        cls.work = tempfile.mkdtemp()

    def test_every_row_that_has_a_meaning_in_lean_means_what_conc_says(self):
        todo = cases(self.rows, self.n, random.Random(1))
        same, differs, none = compare(todo, lean(os.path.join(CORE, "x86.tab"), todo, self.work))
        self.assertEqual(differs, {})
        self.assertEqual(none & set(same), set(), "a row with a meaning for some instances and none for others")
        for name in NEEDED: self.assertIn(name, same)
        self.assertGreaterEqual(len(same), 40)
        left = [r.name for r in self.rows if r.name not in same and r.name != "ret"]
        print(f"\nmachine: {len(same)} rows, {sum(same.values())} instances: Machine.lean leaves what conc.py leaves; "
              f"{len(left)} rows have no meaning in Machine.lean yet: {' '.join(left)}", file=sys.stderr)

    def test_a_return_takes_the_address_at_the_stack_pointer(self):
        rng = random.Random(2)
        row = next(r for r in self.rows if r.name == "ret")
        todo = [(row, {}, {**{name: rng.getrandbits(64) for name in G64}, "rsp": STACK + 8 * rng.randrange(-8, 8)}, rng.randrange(2), rng.randrange(2),
                 bytes(rng.getrandbits(8) for _ in range(ROOM)), 0, 0) for _ in range(self.n)]
        for (row, bind, g, zf, cf, mem, u, nxt), got in zip(todo, lean(os.path.join(CORE, "x86.tab"), todo, self.work)):
            at = g["rsp"] - SCRATCH
            want = ("returned", int.from_bytes(mem[at:at + 8], "little"), zf, cf, [g[r] + 8 if r == "rsp" else g[r] for r in G64], mem)
            self.assertEqual(got, want)

    def test_a_changed_table_is_told(self):
        with open(os.path.join(CORE, "x86.tab")) as f: text = f.read()
        changed = None
        for line in text.split("\n"):
            if line.startswith("add64_rr "):
                self.assertIn("add64(D, S)", line)
                changed = text.replace(line, line.replace("add64(D, S)", "sub64(D, S)"))
        self.assertIsNotNone(changed)
        tab = os.path.join(self.work, "wrong.tab")
        with open(tab, "w") as f: f.write(changed)
        todo = cases([r for r in self.rows if r.name == "add64_rr"], self.n, random.Random(3))
        same, differs, none = compare(todo, lean(tab, todo, self.work))
        self.assertIn("add64_rr", differs)


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1].isdigit(): os.environ["MACHINE_CASES"] = sys.argv.pop(1)
    unittest.main()
