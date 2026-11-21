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
- the function is shown, with the two kernels it calls (each taken by its contract): the kept proof
  (proofs/b3l_node_out.proof) is three lines, one for each way the comparison of `plat` with 5 can go. The
  function built again from its source (../kcheck/hash.ode) with one line changed is refused where the
  change makes it wrong, each with the reason, and shown where the changed function is still right; the
  same with the contract and the layout changed.

What is shown is the statement's contract, where `out` is a run the function may read and write: the kernel
it is handed to reads it. (../kcheck's contract lets the function only write `out`; the function reads no
byte of it before it has written it, which kcheck shows and the verifier here does not.)"""
import os, random, re, shutil, subprocess, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
KCHECK = os.path.join(HERE, "..", "kcheck")
sys.path.insert(0, HERE); sys.path.insert(0, KCHECK); sys.path.insert(0, os.path.join(HERE, "..", "lang"))
import built, lean_verify, odec, prove, statement

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
# Why the verifier refuses a function or a contract that is wrong.
FOLLOW = "refused: the specification's words are not followed on the terms the function made"
ARGS = "refused: what a called function's contract says of its arguments is not followed"
NO_PART = "refused: a called function is given a run that is no part of a run this function was given to read"
NEEDS = "refused: a called function needs of the processor what this function's contract does not say it needs"
NOT_WHOLE = "refused: a called function is given to write what is not whole words of a run this function may read and write, each of them known"
VEC = "refused: a store of a vector register whose words are not known, or at an address that is not a register and a number"
BYTE_W = "refused: a byte written to a run that words were written to: not here yet"
NO_WRITE = "refused: a write to a run given only to read, or to no run given"
LEAVES = "refused: the stack pointer leaves the frame the contract allows"
MORE_STACK = "refused: a call needs more stack than this function's contract allows"
NOT_BACK = "refused: at the return the stack pointer is not where it was at entry"
NOT_WITHIN = "refused: a read of a run of a fixed count that is not eight bytes within it: not here yet"
NO_RUN = "refused: a read that is neither of the frame nor of a run given"
IF, TRACE = "if plat == 5", "\n    trace depends on nd"       # (the hash's own contract in blake3.spec has the same condition)


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
                                (" below 65", " below 18446744073709551616", ["mbelow nd 112 256"]),
                                ("counter: number at 96", "counter: number at 96 below 4", ["mbelow nd 96 4", "mbelow nd 104 65", "mbelow nd 112 256"])):
            with self.subTest(new=new):
                self.assertEqual([l for l in self.lines(once(old, new)) if l.startswith("mbelow")], lines)

    def test_what_is_not_read_is_refused(self):
        for what, change, word in (
                ("a field that is several things", once("h: cv at 0", "h[1]: cv at 0"), "several things"),
                ("a field of a kind that is not read", once("block: 64 bytes at 32", "block: block at 32"), "does not read yet"),
                ("`below` of a field that is no number", once("block: 64 bytes at 32", "block: 64 bytes at 32 below 7"), "has `below`, and is not a single number"),
                ("a need on a condition that is no argument's being a number", once(IF + TRACE, "if plat != 5" + TRACE), "condition"),
                ("a need on a condition of what is no register", once(IF + TRACE, "if nd == 5" + TRACE), "condition"),
                ("a need on a condition of a sum", once(IF + TRACE, "if plat + 1 == 6" + TRACE), "condition"),
                ("an expression that speaks of an argument of the kind `any`", once("node_value(nd, root)", "node_value(nd, plat)"), "`any`"),
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


def last_word(functions, change=lambda t: t):
    """What the verifier says at last of the functions [(object, symbol)] with the proof that the prover
    writes for them: `shown`, or its last word where the prover has nothing more to write."""
    with tempfile.TemporaryDirectory() as d:
        try: prove.prove(spec_text(change), [(obj, symbol, "") for obj, symbol in functions], os.path.join(d, "statement"), os.path.join(d, "proof"))
        except SystemExit as e:
            lines = [l for l in str(e).split("\n") if l.startswith(("refused:", "need "))]
            return lines[0] if lines else str(e)
        return "shown"


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Verify(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.dir = tempfile.mkdtemp(prefix="odenode-")
        with open(os.path.join(KCHECK, "hash.ode")) as f: cls.source = f.read()
    @classmethod
    def tearDownClass(cls): shutil.rmtree(cls.dir)

    def node_from(self, old=None, new=None):
        """The function built again from its source, with one line of it changed: the functions to show."""
        text = self.source
        if old is not None:
            start = text.index('fn node_out as "b3l_node_out" {'); end = text.index("\n}\n", start)
            body = text[start:end]
            self.assertEqual(body.count(old), 1, old)
            text = text[:start] + body.replace(old, new) + text[end:]
        src, obj = os.path.join(self.dir, "changed.ode"), os.path.join(self.dir, "changed.o")
        with open(src, "w") as f: f.write(text)
        odec.build(src, "node_out", obj)
        return [(obj, NODE)] + FUNCTIONS[1:]

    def kept(self, symbols=(NODE, AVX512, SSE41)):
        """The kept proofs of these functions, in one file."""
        path = os.path.join(self.dir, "kept.proof")
        with open(path, "w") as out:
            for symbol in symbols:
                with open(os.path.join(HERE, "proofs", symbol + ".proof")) as f: out.write(f.read())
        return path

    def test_the_function_is_shown_with_the_kernels_it_calls(self):
        self.assertEqual(lean_verify.verify(spec_text(), FUNCTIONS, self.kept()), (True, "shown"))
        # the prover finds the kept proof again
        statement_path, proof_path = os.path.join(self.dir, "s"), os.path.join(self.dir, "p")
        prove.prove(spec_text(), [(obj, symbol, "") for obj, symbol in FUNCTIONS], statement_path, proof_path)
        with open(proof_path) as f: found = f.read()
        with open(os.path.join(HERE, "proofs", NODE + ".proof")) as f: kept = f.read()
        self.assertEqual(kept, "for b3l_node_out\nt live\nt live\nt live\n")
        self.assertEqual(found[found.index("for " + NODE):], kept)
        # controls: the kernels are not taken as shown without their proofs, nor left out of what is to be shown
        shown, said = lean_verify.verify(spec_text(), FUNCTIONS, self.kept((NODE,)))
        self.assertFalse(shown)
        self.assertEqual(said.split("\n")[-1], "in " + AVX512)
        with self.assertRaises(SystemExit) as e: lean_verify.verify(spec_text(), FUNCTIONS[:1], self.kept())
        self.assertIn("which is not among the functions to be shown", str(e.exception))

    def test_a_changed_proof_is_refused(self):
        with open(os.path.join(HERE, "proofs", NODE + ".proof")) as f: lines = f.read().split("\n")[:-1]
        changed = [("a line left out", lines[:k] + lines[k + 1:]) for k in range(1, len(lines))] + \
                  [("dead for live", lines[:k] + ["t dead"] + lines[k + 1:]) for k in range(1, len(lines))] + \
                  [("a line more", lines + ["t live"]), ("another function's name", ["for " + SSE41] + lines[1:])]
        for what, new in changed:
            with self.subTest(what=what):
                path = os.path.join(self.dir, "changed.proof")
                with open(path, "w") as out:
                    out.write("\n".join(new) + "\n")
                    for symbol in (AVX512, SSE41):
                        with open(os.path.join(HERE, "proofs", symbol + ".proof")) as f: out.write(f.read())
                self.assertFalse(lean_verify.verify(spec_text(), FUNCTIONS, path)[0])

    def test_the_function_built_again_from_its_source_is_the_same(self):
        instructions = lambda fns: [l for l in statement.statement(spec_text(), fns) if l.startswith("i ")]
        self.assertEqual(instructions(self.node_from()), instructions(FUNCTIONS))
        self.assertEqual(lean_verify.verify(spec_text(), self.node_from(), self.kept()), (True, "shown"))

    def test_a_read_outside_the_record_is_refused(self):
        for what, old, new, word in (
                ("eight bytes that end past the record", "mov r8, qword ptr [rsi + 112]", "mov r8, qword ptr [rsi + 113]", NOT_WITHIN),
                ("eight bytes after the record", "mov rdx, qword ptr [rsi + 104]", "mov rdx, qword ptr [rsi + 120]", NOT_WITHIN),
                ("eight bytes before the record", "mov rcx, qword ptr [rsi + 96]", "mov rcx, qword ptr [rsi - 8]", NOT_WITHIN),
                ("eight bytes of the run given to write", "mov rcx, qword ptr [rsi + 96]", "mov rcx, qword ptr [rdi + 8]", "refused: a read of a run given only to write"),
                ("eight bytes at an address that is no run's", "mov rcx, qword ptr [rsi + 96]", "mov rcx, qword ptr [rdx + 96]", NO_RUN),
                # the record may end where memory ends: its address and 121 need not be an address
                ("the record's address moved past the record", "add rsi, 32", "add rsi, 121", "need entail")):
            with self.subTest(what=what):
                self.assertEqual(last_word(self.node_from(old, new)), word)

    def test_a_wrong_function_is_refused(self):
        for what, old, new, word in (
                ("the or left out", "  or r8, rdx\n", "", FOLLOW),
                ("the or of another register", "or r8, rdx", "or r8, rsi", ARGS),
                ("the flags added, not or-ed", "or r8, rdx", "add r8, rdx", ARGS),
                ("the length read at the counter's place", "mov rdx, qword ptr [rsi + 104]", "mov rdx, qword ptr [rsi + 96]", ARGS),
                ("the counter read at the length's place", "mov rcx, qword ptr [rsi + 96]", "mov rcx, qword ptr [rsi + 104]", FOLLOW),
                ("the flags read at the length's place", "mov r8, qword ptr [rsi + 112]", "mov r8, qword ptr [rsi + 104]", FOLLOW),
                ("the block four bytes early", "add rsi, 32", "add rsi, 28", FOLLOW),
                ("the block four bytes late", "add rsi, 32", "add rsi, 36", FOLLOW),
                ("the block two bytes late", "add rsi, 32", "add rsi, 34", ARGS),
                ("the block past the record's end", "add rsi, 32", "add rsi, 60", NO_PART),
                ("the block is the run given to write", "add rsi, 32", "mov rsi, rdi", NO_PART),
                ("the kernels exchanged", "jne @sse41", "je @sse41", NEEDS),
                ("the wide kernel for another number", "cmp rax, 5", "cmp rax, 6", NEEDS),
                ("plat taken from root", "mov rax, rcx", "mov rax, rdx", NEEDS),
                ("the second half not stored", "  movups xmmword ptr [rdi + 16], xmm0\n", "", NOT_WHOLE),
                ("the first half stored twice", "movups xmmword ptr [rdi + 16], xmm0", "movups xmmword ptr [rdi + 0], xmm0", NOT_WHOLE),
                ("the value taken from the block", "movups xmm0, xmmword ptr [rsi + 16]", "movups xmm0, xmmword ptr [rsi + 32]", FOLLOW),
                ("the halves exchanged", "movups xmmword ptr [rdi + 16], xmm0",
                 "movups xmmword ptr [rdi + 0], xmm0\n  movups xmm0, xmmword ptr [rsi + 0]\n  movups xmmword ptr [rdi + 16], xmm0", FOLLOW),
                ("sixteen bytes stored after the call", "@done:\n", "@done:\n  movups xmmword ptr [rdi + 0], xmm0\n", VEC),
                ("a byte stored after the call", "@done:\n", "@done:\n  mov byte ptr [rdi + 0], al\n", NO_WRITE),
                ("a byte stored before the call", "  sub rsp, 8\n", "  mov byte ptr [rdi + 3], al\n  sub rsp, 8\n", BYTE_W),
                ("the run given to write moved before the call", "  sub rsp, 8\n", "  add rdi, 4\n  sub rsp, 8\n", NOT_WHOLE),
                ("the record handed over to be written", "  sub rsp, 8\n", "  mov rdi, rsi\n  sub rsp, 8\n", NOT_WHOLE),
                ("no frame", "sub rsp, 8", "sub rsp, 0", LEAVES),
                ("a frame too large", "sub rsp, 8", "sub rsp, 128", MORE_STACK),
                ("the frame not given back", "add rsp, 8", "add rsp, 0", NOT_BACK),
                ("no call", "  jne @sse41\n  call blake3_servil_compress_in_place_avx512\n  jmp @done\n@sse41:\n  call blake3_servil_compress_in_place_sse41\n", "@sse41:\n", FOLLOW),
                ("called twice", "@done:\n", "@done:\n  call blake3_servil_compress_in_place_sse41\n", NOT_WHOLE)):
            with self.subTest(what=what):
                self.assertEqual(last_word(self.node_from(old, new)), word)

    def test_a_changed_function_that_is_right_is_shown(self):
        for what, old, new in (
                ("the or the other way", "or r8, rdx", "or rdx, r8\n  mov r8, rdx"),
                ("the SSE4.1 kernel whatever `plat` is", "  jne @sse41\n  call blake3_servil_compress_in_place_avx512\n  jmp @done\n", ""),
                ("another read within the record, of no use", "  sub rsp, 8\n", "  mov r9, qword ptr [rsi + 73]\n  sub rsp, 8\n")):
            with self.subTest(what=what):
                self.assertEqual(last_word(self.node_from(old, new)), "shown")

    def test_the_trace(self):
        """The contract says the trace may depend on the record `nd`. Without that line the function is NOT
        shown, though what the line then promises is true of it: it reads the counter, the length and the flags
        of the record into registers and gives them to a kernel, whose contract asks that the registers it is
        given be not marked (a contract cannot yet say that a number given is one the trace does not depend on).
        A limit of the verifier, kept here so that it is seen when it goes."""
        self.assertIn("at a call, something the called function's contract asks not to depend on a secret may depend on one",
                      last_word(FUNCTIONS, once(TRACE, "")))

    def test_a_wrong_contract_is_refused(self):
        needs = "    needs sse41\n    needs avx512 if plat == 5\n    trace depends on nd"
        for what, old, new, word in (
                ("the length's bound left out", "length: number at 104 below 65", "length: number at 104", ARGS),
                ("the length up to 256", "below 65", "below 257", ARGS),
                ("the length up to 2^32", "below 65", "below 4294967297", ARGS),
                ("the flags any number", "flags: byte at 112", "flags: number at 112", ARGS),
                ("root any number", "root: byte", "root: number", ARGS),
                ("the counter and the length at each other's places", "counter: number at 96, length: number at 104 below 65",
                 "counter: number at 104, length: number at 96 below 65", ARGS),
                ("the wide kernel for another number", needs, needs.replace("plat == 5", "plat == 6"), NEEDS),
                ("the wide kernel not said", needs, needs.replace("    needs avx512 if plat == 5\n", ""), NEEDS),
                ("sse41 not said", needs, needs.replace("    needs sse41\n", ""), NEEDS),
                ("too little stack", "stack 128", "stack 15", MORE_STACK)):
            with self.subTest(what=what):
                self.assertEqual(last_word(FUNCTIONS, once(old, new)), word)
        # refused before the verifier: what the statement cannot say
        for what, old, new, word in (
                ("the value with `plat` for root", "node_value(nd, root)", "node_value(nd, plat)", "of the kind `any`: an expression cannot speak of it"),
                ("no `no_overlap`", "    requires no_overlap(out, nd)\n", "", "does not say `requires no_overlap(out, nd)`"),
                ("the block at another place", "block: 64 bytes at 32", "block: 64 bytes at 28", "have a byte in common")):
            with self.subTest(what=what):
                try: said = last_word(FUNCTIONS, once(old, new))
                except Exception as e: said = str(e)          # (a layout that is no layout: ../kcheck/ode.py says so)
                self.assertIn(word, said)

    def test_a_changed_contract_that_is_true_is_shown(self):
        needs = "    needs sse41\n    needs avx512 if plat == 5\n    trace depends on nd"
        for what, old, new in (
                ("the length up to 255", "below 65", "below 256"),
                ("the length a byte", "length: number at 104 below 65", "length: byte at 104"),
                ("a counter with a bound", "counter: number at 96", "counter: number at 96 below 4294967296"),
                ("as little stack as it uses", "stack 128", "stack 16"),
                ("a record of one byte more", "layout node120 120", "layout node120 121"),
                ("avx512 whatever `plat` is", needs, needs.replace(" if plat == 5", ""))):
            with self.subTest(what=what):
                self.assertEqual(last_word(FUNCTIONS, once(old, new)), "shown")


if __name__ == "__main__":
    unittest.main()
