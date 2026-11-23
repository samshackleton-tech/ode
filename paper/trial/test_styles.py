"""The trial's sources (src/): one function in each notation gives the same bytes; what the compiler says of
a mistake names its line; and, where asked, what the prover and the verifier say, and what an AArch64
processor computes.

    python3 test_styles.py                   compiles, compares bytes, tries the refusals (any machine)
    python3 test_styles.py --verify OUT      also proves and verifies each x86-64 function, and writes what was
                                             found to OUT (`odeverify` must be built; no AVX-512 is needed)
    python3 test_styles.py --arm OUT         assembles src/arm.ode2 with clang and runs it against src/arm_check.c
                                             (an AArch64 Mac), and writes what was found to OUT

Not one of the suite's tests: tests.sh does not run it. The x86-64 sources are built by the repository's
compiler (../../lang/odec.py), which has the forms the trial tried: inline functions, a place written at its
loop, names for registers, a frame of named fields and `:=` (their own tests: lang/test_inline.py,
test_places.py, test_forms.py). The prototype front end (ode2.py), a trial's tool, is left with the AArch64
source: the compiler has no table of AArch64 instructions yet.
"""
import json, os, re, subprocess, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
SRC = os.path.join(HERE, "src")
CORE, PROOF_CORE = os.path.join(ROOT, "core"), os.path.join(ROOT, "proof-core")
QUAD_RAW = os.path.join(PROOF_CORE, "examples", "quad", "quad32.ode")          # quad32 with every instruction written out
sys.path[:0] = [HERE, PROOF_CORE, os.path.join(ROOT, "kcheck"), os.path.join(ROOT, "lang")]
import ode2
import odec


def text(name):
    with open(os.path.join(SRC, name)) as f: return f.read()


def today(name, fn, folder):
    """The object file the compiler makes of a function of a source in src/."""
    obj = os.path.join(folder, name + ".o")
    odec.build(os.path.join(SRC, name), fn, obj)
    with open(obj, "rb") as f: return f.read()


def today_of(source, fn, folder):
    """The object file the compiler makes of a function of a source's text."""
    path, obj = os.path.join(folder, "changed.ode"), os.path.join(folder, "changed.o")
    with open(path, "w") as f: f.write(source)
    odec.build(path, fn, obj)
    with open(obj, "rb") as f: return f.read()


def places_today(source, fn, folder):
    """The places the compiler finds in a source's text, as the prover reads them."""
    path = os.path.join(folder, "places.ode")
    with open(path, "w") as f: f.write(source)
    return odec.places(path, fn)


def code_of(obj):
    """The bytes of an object file's `.text`."""
    import struct
    shoff, = struct.unpack_from("<Q", obj, 40)
    size, count, names = struct.unpack_from("<HHH", obj, 58)
    at = lambda i: struct.unpack_from("<IIQQQQ", obj, shoff + i * size)
    strings = at(names)[4]
    for i in range(count):
        name, _, _, _, off, n = at(i)
        if obj[strings + name:obj.index(b"\0", strings + name)] == b".text": return obj[off:off + n]
    raise AssertionError("no .text")


def refusal(name, fn, old, new):
    """What is said of a source of src/ with one piece changed: (the line it names, the lines the change is on,
    its words). An x86-64 source is put to the compiler; the AArch64 one to the prototype."""
    source = text(name)
    assert source.count(old) == 1, old
    changed = source.replace(old, new)
    at = [i + 1 for i, line in enumerate(changed.splitlines()) if new.strip() in line]
    if name.endswith(".ode2"):
        try: ode2.compile_source(changed, name)
        except ode2.OdeError as e: return e.line, at, str(e)
    else:
        try: odec.instructions(changed, fn, name)
        except SystemExit as e: return int(re.match(r".*?: line (\d+): ", str(e)).group(1)), at, str(e)
    raise AssertionError(f"{name}: {new} is taken")


# (the source, its function, a piece of it, what it is changed to, words the refusal must hold)
REFUSALS = [
    ("quad32.ode", "quad32", "table[1] := tmp", "table[32] := tmp", ["`table[32]`", "0 to 31"]),                  # a slot past the table's end
    ("quad32.ode", "quad32", "table[0] := tmp", "table[-1] := tmp", ["`table[-1]`", "0 to 31"]),                  # a slot before its start
    ("quad32.ode", "quad32", "tmp := r2.u64[$w]", "tmp := r2.u64[128]", ["`r2.u64[128]`", "0 to 127"]),            # past the end of the results
    ("quad32.ode", "quad32", "r9  := &r1", "r9  := &missing", ["`missing` is no field"]),                         # a field the frame has not
    ("quad32.ode", "quad32", "table[0] := tmp", "table[0] := eax", ["`table[0]` has 8 and `eax` has 4"]),          # a store whose two sides have different sizes
    ("mix16.ode", "mix16_3", "mix16(zmm1, zmm0)", "mix16(zmm1, zmm1)", ["must differ", "zmm1"]),                   # one register for two that must differ
    ("mix16.ode", "mix16_3", "vprord d, d, 16", "vprord a, d, 16", ["changes zmm", "`changes` of mix16 does not list"]),   # a register changed that is not listed
    ("mix16.ode", "mix16_3", "mix16(zmm1, zmm0)", "mix16(rax, zmm0)", ["`rax`", "class zmm"]),                     # a general register for a vector register
    ("arm.ode2", None, "mix12(v0, v1, v2)", "mix12(v0, v1, v0)", ["distinct(d, tmp)", "v0"]),                      # the scratch register is the destination
    ("arm.ode2", None, "rev32 d.8h, d.8h", "rev32 v5.8h, d.8h", ["v5", "changes"]),                                # a register changed that is not declared
]


class Styles(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.folder = tempfile.TemporaryDirectory(prefix="ode-styles-")
        cls.d = cls.folder.name

    @classmethod
    def tearDownClass(cls):
        cls.folder.cleanup()

    def test_the_mixing_steps_are_the_same_bytes_written_out_and_by_inline_function(self):
        raw, inline = today("mix16_raw.ode", "mix16_3", self.d), today("mix16.ode", "mix16_3", self.d)
        self.assertEqual(raw, inline)
        self.assertEqual(len(code_of(raw)), 61)

    def test_the_scan_is_the_same_bytes_and_the_same_place_in_both_notations(self):
        raw, named = today("all_zero.ode", "all_zero_early", self.d), today("all_zero_named.ode", "all_zero_early", self.d)
        self.assertEqual(raw, named)
        places = places_today(text("all_zero.ode"), "all_zero_early", self.d)
        self.assertEqual(places, places_today(text("all_zero_named.ode"), "all_zero_early", self.d))
        self.assertTrue(places.startswith("place +0x2 {\n"), places)

    def test_an_instruction_before_the_loop_moves_the_place_with_it(self):
        for name in ("all_zero.ode", "all_zero_named.ode"):
            source = text(name)
            self.assertEqual(source.count("  xor ecx, ecx\n"), 1)
            places = places_today(source.replace("  xor ecx, ecx\n", "  xor ecx, ecx\n  nop\n"), "all_zero_early", self.d)
            self.assertTrue(places.startswith("place +0x3 {\n"), places)

    def test_quad32_with_a_frame_is_the_kept_object_file(self):
        new = today("quad32.ode", "quad32", self.d)
        with open(os.path.join(PROOF_CORE, "examples", "quad", "odequad32.o"), "rb") as f: self.assertEqual(new, f.read())
        with open(QUAD_RAW) as f: self.assertEqual(new, today_of(f.read(), "quad32", self.d))
        self.assertIn("sub rsp, 2312", odec.instructions(text("quad32.ode"), "quad32"))

    def test_the_arm_source_becomes_the_instructions_it_names(self):
        target, _, fns = ode2.compile_source(text("arm.ode2"), "arm.ode2")
        self.assertEqual(target, "aarch64")
        asm = ode2.emit_aarch64_asm(fns, macho=True)
        for line in ("eor v0.16b, v0.16b, v1.16b", "rev32 v0.8h, v0.8h", "ushr v2.4s, v0.4s, #12", "cset x0, eq"):
            self.assertIn(line, asm)

    def test_each_refusal_names_the_line_and_the_fault(self):
        for name, fn, old, new, words in REFUSALS:
            with self.subTest(new=new):
                line, at, said = refusal(name, fn, old, new)
                self.assertIn(line, at, said)
                for word in words: self.assertIn(word, said)


def verify(out):
    """What the prover and the verifier say of each x86-64 function of src/."""
    import prove, statement
    exe, table = os.path.join(PROOF_CORE, ".lake", "build", "bin", "odeverify"), os.path.join(CORE, "x86.tab")
    found = {}

    def shown(st, pf):
        r = subprocess.run([exe, table, st, pf], capture_output=True, text=True)
        return r.stdout.strip()

    def proved(tag, spec, obj_bytes, symbol, places, limit=120):
        """The prover on one function, in a process of its own with a limit of seconds, then the verifier on what it wrote."""
        obj, st, pf, sp, pl = (os.path.join(d, tag + end) for end in (".o", ".statement", ".proof", ".spec", ".places"))
        with open(obj, "wb") as f: f.write(obj_bytes)
        with open(sp, "w") as f: f.write(spec)
        with open(pl, "w") as f: f.write(places)
        try:
            r = subprocess.run([sys.executable, os.path.abspath(__file__), "--prove", sp, obj, symbol, pl, st, pf], capture_output=True, text=True, timeout=limit)
        except subprocess.TimeoutExpired:
            return {"prover": f"no answer within {limit} seconds"}
        if r.returncode != 0:
            return {"prover": "no proof found", "last word": (r.stdout + r.stderr).strip().split("\n")[-1][:200]}
        return {"verifier": shown(st, pf), "statement bytes": os.path.getsize(st), "proof bytes": os.path.getsize(pf),
                "instructions": sum(1 for line in open(st) if line.startswith("i ")), "code bytes": len(code_of(obj_bytes)), "proof": pf}

    def note(name, what):
        found[name] = {k: v for k, v in what.items() if k != "proof"}
        print(name, "->", found[name], flush=True)

    with tempfile.TemporaryDirectory(prefix="ode-styles-") as d:
        # the scan: written out and with names; one object, one place
        raw = today("all_zero.ode", "all_zero_early", d)
        places = places_today(text("all_zero.ode"), "all_zero_early", d)
        assert raw == today("all_zero_named.ode", "all_zero_early", d) and places == places_today(text("all_zero_named.ode"), "all_zero_early", d)
        note("all_zero", proved("all_zero", text("all_zero.spec"), raw, "ode_all_zero", places))
        # an instruction added before the loop: the place moves with it; a count of bytes that is not moved goes wrong
        moved_source = text("all_zero.ode").replace("  xor ecx, ecx\n", "  xor ecx, ecx\n  nop\n")
        moved, moved_places = today_of(moved_source, "all_zero_early", d), places_today(moved_source, "all_zero_early", d)
        with_place = proved("moved", text("all_zero.spec"), moved, "ode_all_zero", moved_places)
        note("all_zero with an instruction added before the loop, the place the tool finds", dict(with_place, place=moved_places.split(" {")[0]))
        # the proof just found, with the count of bytes as it was for the function before the change
        with open(with_place["proof"]) as f: proof = f.read()
        assert proof.count("place 3\n") == 1, proof[:200]
        stale = os.path.join(d, "stale.proof")
        with open(stale, "w") as f: f.write(proof.replace("place 3\n", "place 2\n"))
        note("all_zero with an instruction added before the loop, that proof with the place at the count typed before",
             {"verifier": shown(os.path.join(d, "moved.statement"), stale), "place": "place +0x2"})
        note("all_zero with an instruction added before the loop, the prover with the place file typed before",
             dict(proved("stale", text("all_zero.spec"), moved, "ode_all_zero", places, limit=60), place="place +0x2"))
        # the mixing steps: written out and with an inline function, one object file
        raw = today("mix16_raw.ode", "mix16_3", d)
        assert raw == today("mix16.ode", "mix16_3", d)
        note("mix16_3", proved("mix16", text("mix16.spec"), raw, "ode_mix16_3", ""))
        # quad32: with a frame it is the kept object file, so the kept statement's inputs and the kept proofs stand
        new = today("quad32.ode", "quad32", d)
        kept = os.path.join(PROOF_CORE, "examples", "quad", "odequad32.o")
        with open(kept, "rb") as f: assert new == f.read()
        qobj, st, pf = os.path.join(d, "odequad32.o"), os.path.join(d, "quad32.statement"), os.path.join(d, "quad32.proof")
        with open(qobj, "wb") as f: f.write(new)
        spec = "\n".join(open(p).read() for p in (os.path.join(ROOT, "kcheck", "blake3.spec"),
                                                  os.path.join(PROOF_CORE, "examples", "kernel", "p32.contract"),
                                                  os.path.join(PROOF_CORE, "examples", "quad", "quad32.contract")))
        with open(st, "w") as f:
            f.write("\n".join(statement.statement(spec, [(os.path.join(ROOT, "kcheck", "b3hashr.o"), "blake3_servil_avx512_p32"), (qobj, "ode_quad32")])) + "\n")
        with open(pf, "w") as f:
            for name in ("blake3_servil_avx512_p32", "ode_quad32"):
                with open(os.path.join(PROOF_CORE, "proofs", name + ".proof")) as g: f.write(g.read())
        note("quad32", {"verifier": shown(st, pf), "with": "the kept proofs of the kernel and of ode_quad32",
                        "proof bytes of ode_quad32": os.path.getsize(os.path.join(PROOF_CORE, "proofs", "ode_quad32.proof")),
                        "code bytes": len(code_of(new))})
    with open(out, "w") as f: json.dump(found, f, indent=1, sort_keys=True); f.write("\n")


def arm(out):
    """Assemble src/arm.ode2 and run it against the C of src/arm_check.c: a run, not a verification. Then the
    same with one instruction of the source changed, twice: the C must say that those differ."""
    def run(source):
        _, _, fns = ode2.compile_source(source, "arm.ode2")
        with tempfile.TemporaryDirectory(prefix="ode-styles-") as d:
            s, o, exe = (os.path.join(d, n) for n in ("arm.s", "arm.o", "arm_check"))
            with open(s, "w") as f: f.write(ode2.emit_aarch64_asm(fns, macho=True))
            subprocess.run(["clang", "-c", "-o", o, s], check=True)
            subprocess.run(["clang", "-O2", "-o", exe, os.path.join(SRC, "arm_check.c"), o], check=True)
            r = subprocess.run([exe], capture_output=True, text=True)
        return {"exit": r.returncode, "printed": r.stdout.strip()}

    source = text("arm.ode2")
    found = {"machine": subprocess.run(["uname", "-m"], capture_output=True, text=True).stdout.strip(), "as written": run(source), "changed": {}}
    for old, new in (("ushr tmp.4s, d.4s, #12", "ushr tmp.4s, d.4s, #11"), ("rev32 d.8h, d.8h", "rev32 d.16b, d.16b"), ("orr acc, acc, w", "and acc, acc, w")):
        assert source.count(old) == 1, old
        found["changed"][f"{old} -> {new}"] = run(source.replace(old, new))
    with open(out, "w") as f: json.dump(found, f, indent=1, sort_keys=True); f.write("\n")
    for name, what in found.items(): print(name, "->", what)
    good = found["as written"]["exit"] == 0 and all(c["exit"] != 0 for c in found["changed"].values())
    sys.exit(0 if good else 1)


def prove_one(spec, obj, symbol, places, st, pf):
    """The prover on one function (a process of its own: see `proved`)."""
    import prove
    with open(spec) as f, open(places) as g: prove.prove(f.read(), [(obj, symbol, g.read())], st, pf)


if __name__ == "__main__":
    if sys.argv[1:2] == ["--verify"]: verify(sys.argv[2])
    elif sys.argv[1:2] == ["--prove"]: prove_one(*sys.argv[2:8])
    elif sys.argv[1:2] == ["--arm"]: arm(sys.argv[2])
    else: unittest.main()
