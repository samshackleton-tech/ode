#!/usr/bin/env python3
"""`b3l_node_out`, the function of the hash that gives a node's chaining value: it reads a record in memory
and calls one of the two one-block kernels.

    python3 test_node.py        (needs Lean's `lake`; the tests are skipped where it is not installed)

The function is in ../kcheck/b3hashr.o; its contract and the record's layout are in
examples/kernel/node_out.contract, as ../kcheck/proofs/inner.spec has them but for the `trace` line.

Here:
- the contract as statement.py writes it: a record in memory is written out field by field from its layout,
  with what the layout asks of the numbers in it; `needs … if` is a line of its own; what statement.py does
  not read is refused;
- what those lines mean: `number.le`, the number that bytes are, and the record of a layout, worked out by
  the account in Lean (`odespec`) on bytes drawn at random, against Python's own reading of the layout;
- what the verifier says of the function."""
import os, random, shutil, subprocess, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
KCHECK = os.path.join(HERE, "..", "kcheck")
sys.path.insert(0, HERE); sys.path.insert(0, KCHECK)
import built, lean_verify, statement

OBJ = os.path.join(KCHECK, "b3hashr.o")
NODE, AVX512, SSE41 = "b3l_node_out", "blake3_servil_compress_in_place_avx512", "blake3_servil_compress_in_place_sse41"
FUNCTIONS = [(OBJ, NODE), (OBJ, AVX512), (OBJ, SSE41)]
CONTRACT = ["arg out inout 32", "arg nd fixed 120", "arg root number", "arg plat number",
            "mbelow nd 104 65", "mbelow nd 112 256", "below root 256", "needs sse41", "needsif avx512 plat 5",
            "ensuresw out (call bytes_of (call node_value (record (h (call words (slice (name nd) (num 0) (num 32)))) "
            "(block (slice (name nd) (num 32) (num 96))) (counter (call number.le (slice (name nd) (num 96) (num 104)))) "
            "(length (call number.le (slice (name nd) (num 104) (num 112)))) (flags (call number.le (slice (name nd) (num 112) (num 120))))) "
            "(name root)))",
            "stack 128"]
LAYOUT = "layout node120 120 { h: cv at 0, block: 64 bytes at 32, counter: number at 96, length: number at 104 below 65, flags: byte at 112 }"
# What the verifier in Lean says of the function today (it reads the contract; the rule it lacks first is named).
TODAY = "refused: a read that is neither of the frame nor of a run given"
IF, TRACE = "if plat == 5", "\n    trace depends on out, nd"       # (the hash's own contract in blake3.spec has the same condition)


def spec_text(change=lambda t: t):
    with open(os.path.join(KCHECK, "blake3.spec")) as f: text = f.read()
    for name in ("kernel.contract", "kernel_sse41.contract", "node_out.contract"):
        with open(os.path.join(HERE, "examples", "kernel", name)) as f: text += "\n" + f.read()
    return change(text)


def once(old, new):
    def change(text):
        assert text.count(old) == 1, (old, text.count(old))
        return text.replace(old, new)
    return change


class Statement(unittest.TestCase):
    def lines(self, change=lambda t: t): return statement.statement(spec_text(change), FUNCTIONS)

    def test_the_contract_in_the_accounts_terms(self):
        lines = self.lines()
        at = lines.index(f"fn {NODE}")
        self.assertGreater(at, lines.index(f"fn {SSE41}"))                      # after the two functions it calls
        mine = [l for l in lines[at + 1:] if not l.startswith(("i ", "def "))]
        self.assertEqual(mine, CONTRACT)
        self.assertEqual(len([l for l in lines[at + 1:] if l.startswith("i ")]), 18)

    def test_a_layout_no_argument_is_of_says_nothing(self):
        other = "layout pair 16 { x: number at 0, y: number at 8 below 9 }\n"
        self.assertEqual(self.lines(once(LAYOUT, other + LAYOUT)), self.lines())

    def test_what_a_layout_asks_is_written(self):
        for old, new, lines in ((" below 65", "", ["mbelow nd 112 256"]),
                                (" below 65", " below 1", ["mbelow nd 104 1", "mbelow nd 112 256"]),
                                ("flags: byte at 112", "flags: number at 112", ["mbelow nd 104 65"]),
                                ("counter: number at 96", "counter: number at 96 below 4", ["mbelow nd 96 4", "mbelow nd 104 65", "mbelow nd 112 256"])):
            with self.subTest(new=new):
                self.assertEqual([l for l in self.lines(once(old, new)) if l.startswith("mbelow")], lines)

    def test_what_is_not_read_is_refused(self):
        for what, change, word in (
                ("a field that is several things", once("h: cv at 0", "h[1]: cv at 0"), "several things"),
                ("a field of a kind that is not read", once("block: 64 bytes at 32", "block: block at 32"), "does not read yet"),
                ("a record that is written", once("ensures out = node_value(nd, root)", "ensures out = node_value(nd, root)\n    ensures nd = nd"), ""),
                ("a need on a condition that is no argument's being a number", once(IF + TRACE, "if plat != 5" + TRACE), "condition"),
                ("a need on a condition of what is no register", once(IF + TRACE, "if nd == 5" + TRACE), "condition"),
                ("a need on a condition of a sum", once(IF + TRACE, "if plat + 1 == 6" + TRACE), "condition"),
                ("an expression that speaks of an argument of the kind `any`", once("node_value(nd, root)", "node_value(nd, plat)"), "`any`"),
                ("the trace may not depend on the record's bytes", once("trace depends on out, nd", "trace depends on out"), "trace"),
                ("no `requires no_overlap`", once("    requires no_overlap(out, nd)\n", ""), "no_overlap")):
            with self.subTest(what=what):
                with self.assertRaises((SystemExit, Exception)) as e: self.lines(change)
                self.assertIn(word, str(e.exception))

    def test_a_functions_own_instructions_need_what_it_says_without_condition(self):
        # What a contract says it needs on a condition does not count for the function's own instructions: they
        # run whatever the arguments are. The AVX-512 kernel, were its contract to need AVX-512 only if its
        # length is 5, is refused.
        old = "    stack 0\n    needs avx512\n"
        self.assertIn("needs avx512", self.lines(once(old, old)))
        with self.assertRaises(SystemExit) as e: self.lines(once(old, "    stack 0\n    needs avx512 if length == 5\n"))
        self.assertIn("does not say it needs", str(e.exception))


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Meaning(unittest.TestCase):
    """The lines of the statement mean what the layout says: by the account in Lean, on bytes drawn at random."""
    @classmethod
    def setUpClass(cls):
        built.built("odespec")
        cls.dir = tempfile.mkdtemp(prefix="odenode-")
        cls.defs = os.path.join(cls.dir, "defs")
        with open(cls.defs, "w") as f: f.write("\n".join(l for l in statement.statement(spec_text(), FUNCTIONS) if l.startswith("def ")) + "\n")
    @classmethod
    def tearDownClass(cls): shutil.rmtree(cls.dir)

    def lean(self, cases):
        """What the account says of each (expression as a statement has it, {name: bytes or a number})."""
        path = os.path.join(self.dir, "cases")
        with open(path, "w") as f:
            for e, env in cases:
                f.write(" ".join(f"{n}=b:{bytes(v).hex()}" if isinstance(v, (list, bytes)) else f"{n}=i:{v}" for n, v in env.items()) + " | " + e + "\n")
        out = subprocess.run([os.path.join(HERE, ".lake", "build", "bin", "odespec"), self.defs, path], capture_output=True, text=True, check=True).stdout.split("\n")[:len(cases)]
        self.assertEqual(len(out), len(cases))
        return out

    def test_the_number_that_bytes_are(self):
        rng = random.Random(41)
        cases, want = [], []
        for _ in range(200):
            b = bytes(rng.randrange(256) for _ in range(rng.randrange(0, 12)))
            lo = rng.randrange(0, len(b) + 1); hi = rng.randrange(lo, len(b) + 1)
            cases.append((f"(call number.le (slice (name a) (num {lo}) (num {hi})))", {"a": b}))
            want.append(f"int {int.from_bytes(b[lo:hi], 'little')}")
        # a control: a number of 256 or more is no byte, and a number is no list of bytes
        cases += [("(call number.le (list (num 255) (num 256)))", {}), ("(call number.le (num 7))", {}), ("(call number.le (list (num 255) (num 1)))", {})]
        want += ["none", "none", "int 511"]
        self.assertEqual(self.lean(cases), want)

    def test_a_record_in_memory_means_what_its_layout_says(self):
        record = CONTRACT[9][len("ensuresw out (call bytes_of (call node_value "):-len(" (name root)))")]
        self.assertTrue(record.startswith("(record (h ") and record.endswith(")))))"), record)
        rng = random.Random(42)
        cases, want = [], []
        for _ in range(60):
            nd = bytes(rng.randrange(256) for _ in range(120))
            for field, value in (("counter", f"int {int.from_bytes(nd[96:104], 'little')}"), ("length", f"int {int.from_bytes(nd[104:112], 'little')}"),
                                 ("flags", f"int {int.from_bytes(nd[112:120], 'little')}"), ("block", f"bytes {nd[32:96].hex()}")):
                cases.append((f"(field {record} {field})", {"nd": nd})); want.append(value)
            cases.append((f"(call bytes_of (field {record} h))", {"nd": nd})); want.append(f"bytes {nd[:32].hex()}")
            cases.append((f"(index (field {record} h) (num 7))", {"nd": nd})); want.append(f"val w{int.from_bytes(nd[28:32], 'little')}")
        self.assertEqual(self.lean(cases), want)

    def test_the_contracts_value_is_the_hash_of_one_block(self):
        """`node_value` of a record with the key, a block, no counter, the block's length and the flags of a
        whole message of one block: the hash, as Python's hashlib has it where it has BLAKE3; else as ode.py."""
        import ode
        with open(os.path.join(KCHECK, "blake3.spec")) as f: spec = ode.Spec(f.read())
        iv = bytes(spec.eval(ode.Numbers(), ("call", "bytes_of", [("call", "iv_words", [])]), {}))
        rng = random.Random(43)
        cases, want = [], []
        for n in (0, 1, 3, 31, 63, 64):
            message = bytes(rng.randrange(256) for _ in range(n))
            nd = iv + message.ljust(64, b"\0") + (0).to_bytes(8, "little") + n.to_bytes(8, "little") + (3).to_bytes(8, "little")   # CHUNK_START | CHUNK_END
            cases.append((CONTRACT[9][len("ensuresw out "):], {"nd": nd, "root": 8}))                                                 # ROOT
            want.append("bytes " + bytes(spec.eval(ode.Numbers(), ("call", "blake3", [("name", "m")]), {"m": list(message)})).hex())
        self.assertEqual(self.lean(cases), want)
        # a control: with the length and the flags laid out the other way round, the empty message's value is another
        swapped = [l for l in statement.statement(spec_text(once("length: number at 104 below 65, flags: byte at 112", "length: number at 112 below 65, flags: byte at 104")), FUNCTIONS)
                   if l.startswith("ensuresw out ")][0]
        self.assertNotEqual(swapped, CONTRACT[9])
        got = self.lean([(swapped[len("ensuresw out "):], env) for _, env in cases])
        self.assertTrue(got[0].startswith("bytes ") and got[0] != want[0], got[0])


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Verify(unittest.TestCase):
    def test_what_the_verifier_says_of_the_function_today(self):
        """The two kernels it calls are shown by their kept proofs; of the function itself the verifier names
        the first rule it lacks."""
        with tempfile.TemporaryDirectory() as d:
            proof = os.path.join(d, "proof")
            with open(proof, "w") as out:
                for symbol in (AVX512, SSE41):
                    with open(os.path.join(HERE, "proofs", symbol + ".proof")) as f: out.write(f.read())
            # the kernels alone are shown by this file
            shown, said = lean_verify.verify(spec_text(), FUNCTIONS[1:], proof)
            self.assertTrue(shown, said)
            with open(proof, "a") as out: out.write(f"for {NODE}\n")
            shown, said = lean_verify.verify(spec_text(), FUNCTIONS, proof)
            self.assertFalse(shown)
            self.assertEqual(said.split("\n"), [TODAY, f"in {NODE}"])


if __name__ == "__main__":
    unittest.main()
