"""The first table of AArch64 instruction forms (arm64.tab) and its tools.

On any machine: every way of the table writes a word and reads it back as the same instance; what the table
does not write is not read; and, where clang is, the word the table writes for an instance is the word
clang writes for the row's assembly. On an AArch64 machine with clang: every row is what the processor
does (cross.py), and a table with one row changed is found out.

    python3 test_arm64.py"""
from pathlib import Path
import os, platform, random, re, shutil, subprocess, sys, tempfile, unittest

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE), str(HERE.parent / "core")]
import cross, table, word

ARM = platform.machine() in ("arm64", "aarch64")
# A row changed, and whether the processor then differs from it ("differs") or only the assembler's word ("word").
CHANGED = [("add is sub", "| D = add64(S, P)", "| D = sub64(S, P)", "differs"),
           ("the immediate is added twice", "| D = add64(S, I)", "| D = add64(add64(S, I), I)", "differs"),
           ("ldr64 reads four bytes", "| D = mem64(B, N)", "| D = mem32(B, N)", "differs"),
           ("str32 stores eight bytes", "| mem32(B, N) = low32(S)", "| mem64(B, N) = S", "differs"),
           ("the displacement of ldr32 counts in eights", "nnnnnnnnnnnn BBBBB DDDDD ; N=n*4", "nnnnnnnnnnnn BBBBB DDDDD ; N=n*8", "differs"),
           ("rev32 turns by 8", "each32(ror32, Y, 16)", "each32(ror32, Y, 8)", "differs"),
           ("ushr shifts by the field itself", "; I=32-i", "; I=31-i", "differs"),
           ("eor is or", "each32(xor32, Y, Z)", "each32(or32, Y, Z)", "differs"),
           ("st1 writes nothing", "| mem128(B, 0) = X", "| nothing", "differs"),
           ("nop sets x0", "| nothing", "| x0 = 0", "differs"),
           ("add sp moves x0", "| sp = add64(sp, I)", "| x0 = add64(sp, I)", "differs"),
           ("a load at a stack pointer that is no multiple of 16 has no fault", "| D = mem64(on16(sp), N)", "| D = mem64(sp, N)", "differs"),
           ("a store at a stack pointer that is no multiple of 16 has no fault", "| mem64(on16(sp), N) = S", "| mem64(sp, N) = S", "differs"),
           ("adding to a stack pointer that is no multiple of 16 has a fault", "| sp = add64(sp, I)", "| sp = add64(on16(sp), I)", "differs"),
           ("sub's registers the other way in the word", "= 1 1 0 01011 00 0 PPPPP 000000 SSSSS DDDDD", "= 1 1 0 01011 00 0 SSSSS 000000 PPPPP DDDDD", "differs"),
           ("add's registers the other way in the word", "= 1 0 0 01011 00 0 PPPPP 000000 SSSSS DDDDD", "= 1 0 0 01011 00 0 SSSSS 000000 PPPPP DDDDD", "word")]
# Words that are instructions and no instance of a row: each has 31 in a field of D, S or P, or a bit the row has fixed.
NOT_READ = {"aa1f03e0": "mov x0, xzr", "aa0103ff": "mov xzr, x1", "8b1f0020": "add x0, x1, xzr", "91401020": "add x0, x1, #4, lsl #12",
            "f8626820": "ldr x0, [x1, x2]", "f85f8020": "ldur x0, [x1, #-8]", "d65f0020": "ret x1", "4c407420": "ld1 {v0.8h}, [x1]",
            "00000000": "udf #0"}


def text_of(obj):
    """The bytes of an ELF object file's `.text`."""
    import struct
    shoff, = struct.unpack_from("<Q", obj, 40)
    size, count, names = struct.unpack_from("<HHH", obj, 58)
    at = lambda i: struct.unpack_from("<IIQQQQ", obj, shoff + i * size)
    strings = at(names)[4]
    for i in range(count):
        name, _, _, _, off, n = at(i)
        if obj[strings + name:obj.index(b"\0", strings + name)] == b".text": return obj[off:off + n]
    raise AssertionError("no .text")


class Words(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rows = table.read(word.TABLE)
        cls.ways = word.ways(cls.rows)

    def test_the_table_is_read(self):
        self.assertEqual(len(self.rows), 27)
        self.assertEqual(len(self.ways), 27)
        heads = [row.pattern[0] for row in self.rows]
        self.assertEqual(len(set(heads)), len(heads))             # a decoded instruction's first word says its row
        for way in self.ways:                                     # every placeholder of a row is in each of its ways
            row = way.row
            names = {t.lstrip(".") for t in row.pattern[1:] if isinstance(t, str)}
            self.assertEqual(names, {n for n in set(way.fields) | set(way.rules) if n.isupper()}, row.name)

    def test_a_word_written_is_read_back_as_the_instance(self):
        rng = random.Random(7)
        for way in self.ways:
            row = way.row
            for _ in range(200):
                bind = {}
                for name, (low, width) in way.fields.items():
                    v = rng.randrange(1 << width)
                    if name in word.REGISTER: bind[name] = word.GENERAL[v % 31]
                    elif name.isupper(): bind[name] = v
                    else:
                        placeholder, (_, how, k) = next((p, rule) for p, rule in way.rules.items() if rule[0] == name)
                        bind[placeholder] = v * k if how == "times" else k - v
                got = word.decode(self.ways, word.encode(way, bind))
                self.assertIsNotNone(got, (row.name, bind))
                self.assertEqual((got[0].name, got[1]), (row.name, bind))

    def test_what_is_not_written_is_not_read(self):
        for text in NOT_READ:
            with self.subTest(word=text): self.assertIsNone(word.decode(self.ways, int(text, 16).to_bytes(4, "little")), NOT_READ[text])
        rng = random.Random(11)
        read = 0
        for _ in range(20000):                                     # any word: read as an instance only if that instance is written as it
            w = rng.getrandbits(32).to_bytes(4, "little")
            got = word.decode(self.ways, w)
            if got is None: continue
            read += 1
            self.assertEqual(word.encode(next(way for way in self.ways if way.row is got[0]), got[1]), w)
        self.assertGreater(read, 20)

    def test_an_instance_a_way_cannot_write_is_refused(self):
        way = {w.row.name: w for w in self.ways}
        for name, bind in (("mov_rr", {"D": "x0", "S": "sp"}), ("mov_rr", {"D": "sp", "S": "x1"}), ("mov_ri", {"D": "x0", "I": 65536}),
                           ("add_rri", {"D": "x0", "S": "x1", "I": 4096}), ("ldr64", {"D": "x0", "B": "x1", "N": 12}), ("ldr64", {"D": "x0", "B": "x1", "N": 32768}),
                           ("ldr32", {"D": "x0", "B": "x1", "N": 6}), ("ushr_4s", {"X": 0, "Y": 1, "I": 0}), ("ushr_4s", {"X": 0, "Y": 1, "I": 33}),
                           ("shl_4s", {"X": 0, "Y": 1, "I": 32}), ("eor_v", {"X": 32, "Y": 1, "Z": 2}), ("ldr64", {"D": "x0", "B": "x31", "N": 8}),
                           ("ldr64", {"D": "x0", "B": "sp", "N": 16}), ("ldr64_sp", {"D": "sp", "N": 16}), ("str64_sp", {"S": "x0", "N": 4})):
            with self.subTest(row=name, bind=bind):
                with self.assertRaises(word.Refuse): word.encode(way[name], bind)
        self.assertEqual(word.encode(way["ldr64_sp"], {"D": "x0", "N": 16}).hex(), "e00b40f9")
        self.assertEqual(word.decode(self.ways, bytes.fromhex("e00b40f9"))[0].name, "ldr64_sp")       # (a base field of 31 is the stack pointer's row)
        self.assertEqual(word.encode(way["ushr_4s"], {"X": 0, "Y": 1, "I": 32}).hex(), "2004206f")

    @unittest.skipUnless(shutil.which("clang"), "clang writes the words to compare with")
    def test_the_word_is_the_one_clang_writes(self):
        """On any machine: clang assembles for AArch64 whatever it runs on."""
        rng = random.Random(3)
        lines, want = [], []
        for row in self.rows:
            way = next(w for w in self.ways if w.row is row)
            for _ in range(50):
                if row.asm == "-":
                    text, bind = {"bl": "bl there", "ret": "ret"}[row.name], ({"I": 0} if row.name == "bl" else {})
                else: bind, text = cross.instance(row, rng)
                lines.append(text); want.append(word.encode(way, bind))
        with tempfile.TemporaryDirectory() as d:
            src, obj = Path(d) / "words.s", Path(d) / "words.o"
            src.write_text(".text\n" + "".join(f"    {line}\n" for line in lines))
            subprocess.run(["clang", "--target=aarch64-unknown-linux-gnu", "-c", "-o", str(obj), str(src)], check=True, capture_output=True)
            code = text_of(obj.read_bytes())
        self.assertEqual(len(code), 4 * len(lines))
        for k, (line, w) in enumerate(zip(lines, want)):
            with self.subTest(line=line): self.assertEqual(code[4 * k:4 * k + 4].hex(), w.hex())


@unittest.skipUnless(ARM and shutil.which("clang"), "an AArch64 processor and clang are needed")
class Processor(unittest.TestCase):
    def cross(self, text, cases):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "changed.tab"
            path.write_text(text)
            r = subprocess.run([sys.executable, str(HERE / "cross.py"), "--cases", str(cases), "--table", str(path), "--work", d], capture_output=True, text=True, timeout=250)
        return r.returncode, r.stdout.strip().splitlines()[-1] if r.stdout.strip() else r.stderr[-300:]

    def test_every_row_is_what_the_processor_does(self):
        code, last = self.cross(Path(word.TABLE).read_text(), 100)
        self.assertEqual(code, 0, last)
        self.assertIn("25 rows, each as the assembler writes it and as the table writes it, 5000 instances: 0 differ from this processor", last)
        self.assertIn("0 of the assembler's words are not the table's; 2 rows are not run: bl, ret", last)
        faults = int(re.search(r"; (\d+) are faults, as the row says", last).group(1))
        self.assertGreater(faults, 50)            # (the two rows whose base is the stack pointer, where it is no multiple of 16)

    def test_a_changed_row_is_found_out(self):
        base = Path(word.TABLE).read_text()
        for what, old, new, how in CHANGED:
            with self.subTest(what=what):
                self.assertEqual(base.count(old), 1 if "nnnn" not in old else 1, old)
                code, last = self.cross(base.replace(old, new), 20)
                self.assertEqual(code, 1, last)
                if how == "differs": self.assertNotIn(": 0 differ from this processor", last)
                else:
                    self.assertIn(": 0 differ from this processor", last)
                    self.assertNotIn("; 0 of the assembler's words are not the table's", last)


if __name__ == "__main__": unittest.main()
