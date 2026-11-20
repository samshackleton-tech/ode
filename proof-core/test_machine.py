#!/usr/bin/env python3
"""The machine as Machine.lean says it against the machine as ../core/conc.py says it.

    python3 test_machine.py [CASES]        (skipped where Lean's `lake` is not installed)

The theorem in SoundTop.lean is about the machine of Machine.lean. Processors were compared with conc.py
(../core/cross.py). Both read the same table; each works a row's EFFECT out in its own code. Here every row
of the table is run from random states by both: random registers and numbers, the flags, 1024 bytes of
memory that a base register and the stack pointer point into, random vector registers. Part by part they
must leave the same: the general registers, the flags, memory, every 32-bit lane of each vector register,
every bit of each mask register,
and where a jump goes. The comparison skips values conc.py leaves unspecified. The aligned 512-bit
memory operations must also fault on a misaligned address.

The test lists rows whose effects it does not compare. A return is no row conc.py runs; what
Machine.lean does at one is compared with what is said here: the address at the stack pointer is taken and
the stack pointer goes up by eight.

The control changes an effect in the table that Machine.lean reads and requires the comparison to find
the difference."""
import os, random, re, shutil, subprocess, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
CORE = os.path.join(HERE, "..", "core")
KCHECK = os.path.join(HERE, "..", "kcheck")
sys.path.insert(0, CORE)
sys.path.insert(0, KCHECK)
import conc, cross, kdecode, table
import built

LAKE = shutil.which("lake") or (os.path.expanduser("~/.elan/bin/lake") if os.path.exists(os.path.expanduser("~/.elan/bin/lake")) else None)
G64, SCRATCH, ROOM, STACK = cross.G64, cross.SCRATCH, cross.ROOM, cross.STACK
FUNCTION = 0x400000                       # where the function is taken to start; a jump's number counts from there
# the rows the functions verified in Lean so far are made of: each must be among the rows compared
NEEDED = ["mov64_rr", "mov64_ri", "mov64_rm", "mov64_mr", "add64_rr", "add64_ri", "sub64_ri", "cmp64_rr", "cmp64_ri",
          "movzx8_rm", "xor32_same", "dec64", "lea", "push", "pop", "jmp", "je", "jne", "jae", "jb"]
# the 128-bit rows the two one-block kernels are made of
VECTOR = ["loadu128", "storeu128", "const128", "mov128", "movq128", "paddd128", "pxor128", "prord128", "pslld128", "psrld128",
          "por128", "pshufb128", "pshufd128", "shufps128", "unpckldq", "unpckhdq", "unpcklqdq", "pblendd128", "pblendw128"]
WIDE = ["broadcast_r", "broadcast_i", "broadcast_m", "mov512", "load512a", "load512", "load512i", "store512a", "store512",
        "paddd512", "paddd512m", "pxord512_same", "pxord512", "prord512", "unpckldq512", "unpckhdq512", "unpcklqdq512", "unpckhqdq512", "shufi32x4",
        "paddd512c", "pcmpud512", "paddd512k"]            # (the last three: a constant of the file added; a compare into a mask register; an add under one)


def fill(row, bind):
    """The decoded row of this instance, as the reader of code writes it."""
    def one(m):
        t = m.group(0)
        if t[:1] == "." and t[1:] in table.REGISTERS: return "." + bind[t[1:]]
        if t == "K" and "DATA16" in row.asm: return f"0x{bind[t]:0128X}#512"       # (as the decoder writes sixteen words of the file's data)
        return str(bind[t]) if t in table.NUMBERS + table.VECTORS + table.MASKS else t
    return re.sub(r"[^\s()]+", one, row.row)


def cases(rows, n, rng):
    """For each row n instances and states: (row, bind, registers, flags, memory, the number an unknown is, where the
    next instruction is, the vector registers' lanes, the mask registers' bits)."""
    out = []
    for row in rows:
        if row.name not in WIDE and (row.asm == "-" or ("DATA" in row.asm and "DATA4" not in row.asm) or "zmm" in row.asm or "ymm" in row.asm): continue
        if any(v in row.row.split() for v in table.MASKS) and row.name not in WIDE: continue
        for _ in range(n):
            bind, _, fixed = cross.instance(row, rng)
            if any(st[0] == "jump" for st in row.effect): bind["I"] = rng.randrange(1 << 16)
            g = {name: rng.getrandbits(64) for name in G64}
            g.update(fixed); g["rsp"] = STACK
            out.append((row, bind, g, rng.randrange(2), rng.randrange(2), bytes(rng.getrandbits(8) for _ in range(ROOM)),
                        rng.getrandbits(64), rng.randrange(1 << 16), {i: tuple(rng.getrandbits(32) for _ in range(16)) for i in range(32)},
                        {m: tuple(rng.randrange(2) for _ in range(16)) for m in range(8)}))
    return out


def lean(tab, todo, work):
    """What Machine.lean leaves, case by case: (kind, rip, zf, cf, registers, memory, lanes) or the word it answers."""
    path = os.path.join(work, "cases.txt")
    with open(path, "w") as f:
        for row, bind, g, zf, cf, mem, u, nxt, x, k in todo:
            lanes = "".join(f"{v:08x}" for i in range(32) for v in x[i]) + "".join(f"{v:08x}" for m in range(8) for v in k[m])
            f.write(f"c {FUNCTION} {nxt} {u} {zf} {cf} {' '.join(str(g[r]) for r in G64)} {SCRATCH} {mem.hex()} {lanes} | {fill(row, bind)}\n")
    got = subprocess.run([os.path.join(HERE, ".lake", "build", "bin", "odemachine"), tab, path], capture_output=True, text=True, check=True).stdout.split("\n")
    out = []
    for line in got[:len(todo)]:
        w = line.split()
        out.append(line if len(w) < 22 else (w[0], int(w[1]), int(w[2]), int(w[3]), [int(x) for x in w[4:20]], bytes.fromhex(w[20]),
                                             [int(w[21][8 * i:8 * i + 8], 16) for i in range(40 * 16)]))
    assert len(out) == len(todo), "the Lean program answered fewer cases than it was given"
    return out


def compare(todo, answers):
    """({row: instances compared}, {row: why it differs, the first time}, rows with no meaning in Lean)."""
    same, differs, none = {}, {}, set()
    for (row, bind, g, zf, cf, mem, u, nxt, x, k), got in zip(todo, answers):
        if got == "none": none.add(row.name); continue
        if isinstance(got, str): differs.setdefault(row.name, f"Lean answers `{got}` to {fill(row, bind)}"); continue
        s = conc.run(row, bind, conc.State(g, x, {SCRATCH + i: b for i, b in enumerate(mem)}, zf, cf, k))
        kind, rip, lzf, lcf, regs, lmem, lanes = got
        wrong = [n for n, v in zip(G64, regs) if s.g[n] != table.UNKNOWN and s.g[n] != v]
        wrong += [n for n, v, w in (("zf", s.zf, lzf), ("cf", s.cf, lcf)) if v != table.UNKNOWN and int(v) != w]
        wrong += [f"vector register {i} lane {j}" for i in range(32) for j in range(16)
                  if s.x[i][j] != table.UNKNOWN and s.x[i][j] != lanes[16 * i + j]]
        wrong += [f"mask register {m} bit {j}" for m in range(8) for j in range(16) if int(s.k[m][j]) != lanes[16 * (32 + m) + j]]
        wrong += ["memory"] if bytes(s.mem[SCRATCH + i] for i in range(ROOM)) != lmem else []
        wrong += ["where it goes on"] if rip != FUNCTION + (nxt if s.to is None else s.to) or kind != "next" else []
        if wrong: differs.setdefault(row.name, f"{fill(row, bind)}: {', '.join(wrong)}")
        else: same[row.name] = same.get(row.name, 0) + 1
    return same, differs, none


@unittest.skipUnless(LAKE, "Lean's lake is not installed")
class Machine(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odemachine")
        cls.n = int(os.environ.get("MACHINE_CASES", "60"))
        cls.rows = table.read()
        cls.work = tempfile.mkdtemp()
        cls.addClassCleanup(shutil.rmtree, cls.work)

    def test_every_row_that_has_a_meaning_in_lean_means_what_conc_says(self):
        todo = cases(self.rows, self.n, random.Random(1))
        same, differs, none = compare(todo, lean(os.path.join(CORE, "x86.tab"), todo, self.work))
        self.assertEqual(differs, {})
        self.assertEqual(none & set(same), set(), "a row with a meaning for some instances and none for others")
        for name in NEEDED + VECTOR + WIDE: self.assertIn(name, same)
        self.assertGreaterEqual(len(same), 78)
        left = [r.name for r in self.rows if r.name not in same and r.name != "ret"]
        # not compared here: the address of the file's data and a call are said in Machine.lean itself (conc.py
        # runs neither)
        self.assertEqual(left, ["lea_data", "call"])
        print(f"\nmachine: {len(same)} rows, {sum(same.values())} instances: Machine.lean leaves what conc.py leaves; "
              f"not compared: {' '.join(left)}", file=sys.stderr)

    def test_a_return_takes_the_address_at_the_stack_pointer(self):
        rng = random.Random(2)
        row = next(r for r in self.rows if r.name == "ret")
        todo = [(row, {}, {**{name: rng.getrandbits(64) for name in G64}, "rsp": STACK + 8 * rng.randrange(-8, 8)}, rng.randrange(2), rng.randrange(2),
                 bytes(rng.getrandbits(8) for _ in range(ROOM)), 0, 0, {i: (i,) * 16 for i in range(32)}, {m: (m % 2,) * 16 for m in range(8)})
                for _ in range(self.n)]
        for (row, bind, g, zf, cf, mem, u, nxt, x, k), got in zip(todo, lean(os.path.join(CORE, "x86.tab"), todo, self.work)):
            at = g["rsp"] - SCRATCH
            want = ("returned", int.from_bytes(mem[at:at + 8], "little"), zf, cf, [g[r] + 8 if r == "rsp" else g[r] for r in G64], mem,
                    [i for i in range(32) for _ in range(16)] + [m % 2 for m in range(8) for _ in range(16)])
            self.assertEqual(got, want)

    def test_p16_uses_only_wide_forms_compared_here(self):
        rows, _ = kdecode.read(os.path.join(KCHECK, "b3hashr.o"), "blake3_servil_avx512_p16", FUNCTION, SCRATCH)
        heads = table.by_head(self.rows)
        used = set()
        for _, _, instruction in rows:
            row, _ = table.find(heads, table.parse_row(instruction))
            self.assertIsNotNone(row, instruction)
            if "zmm" in row.asm:
                used.add(row.name)
        self.assertTrue(used)
        self.assertEqual(used - set(WIDE), set())

    def test_aligned_vector_memory_operands_require_alignment(self):
        rows = {r.name: r for r in self.rows}
        for aligned, unaligned in (("load512a", "load512"), ("store512a", "store512")):
            row, bind, g, zf, cf, mem, u, nxt, x, k = cases([rows[aligned]], 1, random.Random(4))[0]
            args = (bind, g, zf, cf, mem, u, nxt, x, k)
            g2 = {**g, bind["B"]: g[bind["B"]] + 1}
            bad = (bind, g2, zf, cf, mem, u, nxt, x, k)
            can, cannot, control = lean(os.path.join(CORE, "x86.tab"),
                                        [(row, *args), (row, *bad), (rows[unaligned], *bad)], self.work)
            self.assertIsInstance(can, tuple)
            self.assertEqual(cannot, "none")
            self.assertIsInstance(control, tuple)

    def test_a_changed_table_is_told(self):
        with open(os.path.join(CORE, "x86.tab")) as f: text = f.read()
        for name, old, new in (("add64_rr", "add64(D, S)", "sub64(D, S)"), ("paddd128", "each32(add32, Y, Z)", "each32(xor32, Y, Z)"),
                               ("pshufd128", "pick4(Y, Y, I)", "Y"),
                               ("shufi32x4", "quarters(Y512, Z512, I)", "quarters(Z512, Y512, I)"),
                               # the compare the other way round; the add under a mask, where a lane whose bit is not set
                               # takes what another register holds
                               ("pcmpud512", "each32(ult32, X512, Y512)", "each32(ult32, Y512, X512)"),
                               ("paddd512k", "choose16(M, each32(add32, Y512, Z512), X512)", "choose16(M, each32(add32, Y512, Z512), Y512)"),
                               ("paddd512c", "each32(add32, Y512, words16(K))", "each32(xor32, Y512, words16(K))")):
            changed = None
            for line in text.split("\n"):
                if line.startswith(name + " "):
                    self.assertIn(old, line)
                    changed = text.replace(line, line.replace(old, new))
            self.assertIsNotNone(changed)
            tab = os.path.join(self.work, f"wrong-{name}.tab")
            with open(tab, "w") as f: f.write(changed)
            todo = cases([r for r in self.rows if r.name == name], self.n, random.Random(3))
            same, differs, none = compare(todo, lean(tab, todo, self.work))
            self.assertIn(name, differs)


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1].isdigit(): os.environ["MACHINE_CASES"] = sys.argv.pop(1)
    unittest.main()
