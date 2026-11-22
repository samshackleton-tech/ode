#!/usr/bin/env pypy3
"""Verify `b3l_chunk_node`, the hash's function that compresses a chunk's blocks but the last, from the
shipped bytes, with the three functions it calls.

    pypy3 test_chunk.py        (the tests of the verifier are skipped where Lean's `lake` is not installed)

The function is `b3l_chunk_node` as it lies in ../kcheck/b3hashr.o: 81 instructions. Its contract and the
layout of the record it writes are the ones in ../kcheck/proofs/inner.spec, as they are written there:

    layout node120 120 { h: cv at 0, block: 64 bytes at 32, counter: number at 96, length: number at 104 below 65, flags: byte at 112 }

    contract b3l_chunk_node(nd: node120, input: len bytes, len: number, t: number, flags: byte, plat: any) {
        requires no_overlap(nd, input)
        requires len <= 1024
        ensures nd = chunk_node(nd.h, t, flags, input)
        trace depends on len, plat
        stack 256
        needs sse41
        needs avx512 if plat == 5
    }

A chunk is at most 1024 bytes: up to sixteen blocks of 64. The function gives each block but the last to a
one-block kernel (the AVX-512 one where `plat` is 5, else the SSE4.1 one), which compresses it into the
first 32 bytes of the record `nd`; it has `b3l_pad` write the last block, padded with zeros, into the
record at byte 32; and it stores the chunk's number, the last block's length and the flags as three
numbers of eight bytes. The contract says `trace depends on len, plat`: which instructions run and which
addresses are touched depend on the length and on `plat`, and on nothing else that is given: on no byte of
the input or of the record, and not on the chunk's number or the flags. (The function keeps the flags in its
frame and gives them and the chunk's number to a kernel, whose contract hides both.)

The function has a loop and no place is said of it: the length is at most 1024, so the loop is gone
round at most fifteen times, and the verifier goes through every count of turns, each with what is then
known of the length.

What the verifier in Lean takes here that it refused before:
- eight bytes of a number stored into a run the function may read and write, at a place that is a number
  divisible by four: two words of the run then hold the number's low half and its high half;
- a called function may write a part of such a run while cells of the frame are known not to depend on a
  secret (before, only the whole run);
- `x | 0` in the code is `x`;
- in the specification: `the least number n in a..b with …`; `<` and `>=` of numbers the verifier holds,
  where one of the two answers is seen at once; `|` of such a number and a number of the text, where the
  code has put the same two together;
- a record that is written whose layout has numbers: each is the two words of its eight bytes, where it
  is below what the layout asks. Where it is not, the `ensures` has no value, so nothing false is shown.

The function, its contract and the kept proof are shown; with the contract or the function changed in one
place, so that what is stated is false, nothing is shown, and each case names what the verifier then
refuses or what it lacks."""
import os, random, re, shutil, subprocess, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
KCHECK = os.path.join(HERE, "..", "kcheck")
sys.path.insert(0, HERE); sys.path.insert(0, KCHECK); sys.path.insert(0, os.path.join(HERE, "..", "lang"))
import built, lean_verify, odec, prove, statement

OBJ = os.path.join(KCHECK, "b3hashr.o")
CHUNK, AVX512, SSE41, PAD = "b3l_chunk_node", "blake3_servil_compress_in_place_avx512", "blake3_servil_compress_in_place_sse41", "b3l_pad"
FUNCTIONS = [(OBJ, AVX512), (OBJ, SSE41), (OBJ, PAD), (OBJ, CHUNK)]
# the record the contract says the run becomes, and its bytes: those of its fields' words, a number being the
# two words of its eight bytes where it is below what the layout asks
RECORD = "(call chunk_node (call words (slice (name nd) (num 0) (num 32))) (name t) (name flags) (name input))"
def number_words(field, bound):
    x = f"(field (name record) {field})"
    return f"(ifx (bin < {x} (num {bound})) (list (call lo (call counter {x})) (call hi (call counter {x}))) (index (list (num 0)) (num 1)))"
ENSURES = (f"(call bytes_of (let record {RECORD} (bin ++ (field (name record) h) (bin ++ (call words (field (name record) block)) "
           f"(bin ++ {number_words('counter', 2 ** 64)} (bin ++ {number_words('length', 65)} {number_words('flags', 256)}))))))")
CONTRACT = ["arg nd inout 120", "arg input bytes len", "arg len number", "arg t number", "arg flags number", "arg plat number",
            "below flags 256", "needs sse41", "needsif avx512 plat 5", "below len 1025", "hidden input", "hidden t", "hidden flags",
            "ensuresw nd " + ENSURES, "stack 256"]
NEEDS = "    stack 256\n    needs sse41\n    needs avx512 if plat == 5\n"
# Why the verifier refuses, or what the prover cannot give it.
FOLLOW = "refused: the specification's words are not followed on the terms the function made"
WORD = "refused: a word of the run is not known to hold what the specification says"
ARGS = "refused: what a called function's contract says of its arguments is not followed"
NEEDS_MORE = "refused: a called function needs of the processor what this function's contract does not say it needs"
STACK = "refused: a call needs more stack than this function's contract allows"
NOT_TWO = "refused: eight bytes that are not two words of the run, or of a run that single bytes were written to"
JUMP = "refused: a jump on a flag that may depend on a secret: which instructions run would depend on it"
ENTAIL = "need entail"            # an address is to be shown not to pass 2^64, a number to be below its bound, or a part given to a
                                  # called function to lie within the run it is a part of, and it is not so
KNOW = "need know"                # the proof file has run out before an `ensures` or a call, and of the rows that the prover
                                  # would name there (that a part lies within its run; how two numbers compare) none is shown
# (what is changed, the contract as it is, the contract changed, what the verifier then says)
CONTRACTS = [
    ("a chunk of 1025 bytes may be given: it has no count of blocks", "len <= 1024", "len <= 1025", FOLLOW),
    ("the flags are said to be 0", "chunk_node(nd.h, t, flags, input)", "chunk_node(nd.h, t, 0, input)", FOLLOW),
    ("the chunk's number and the flags the other way round", "chunk_node(nd.h, t, flags, input)", "chunk_node(nd.h, flags, t, input)", FOLLOW),
    ("the chunk's number is said to be 0", "chunk_node(nd.h, t, flags, input)", "chunk_node(nd.h, 0, flags, input)", FOLLOW),
    ("the key is said to be the first half of the record's block", "chunk_node(nd.h, t, flags, input)",
     "chunk_node(words(nd.block[0 .. 32]), t, flags, input)", FOLLOW),
    ("the number and the length at each other's places", "counter: number at 96, length: number at 104 below 65",
     "counter: number at 104, length: number at 96 below 65", WORD),
    ("the length is said to be below 64: a last block of 64 bytes has none", "length: number at 104 below 65", "length: number at 104 below 64", KNOW),
    ("the flags may be any number: a kernel takes a byte", "t: number, flags: byte, plat: any", "t: number, flags: number, plat: any", ARGS),
    ("one byte less of stack than is used", "stack 256", "stack 143", STACK),
    ("AVX-512 is not said to be needed", NEEDS, "    stack 256\n    needs sse41\n", NEEDS_MORE),
    ("AVX-512 is said to be needed for another number", NEEDS, NEEDS.replace("plat == 5", "plat == 6"), NEEDS_MORE),
    ("SSE4.1 is not said to be needed", NEEDS, NEEDS.replace("    needs sse41\n", ""), NEEDS_MORE),
    # the trace: the loop is gone round as often as the length says, and which kernel is called is `plat`'s to say
    ("the length is hidden", "trace depends on len, plat", "trace depends on plat", JUMP),
    ("`plat` is hidden", "trace depends on len, plat", "trace depends on len", JUMP),
    ("no `trace` line: every number is hidden", "    trace depends on len, plat\n", "", JUMP),
]
TRUE_CONTRACTS = [
    ("chunks of at most 512 bytes", "len <= 1024", "len <= 512"),
    ("as little stack as is used", "stack 256", "stack 144"),
    ("AVX-512 whatever `plat` is", NEEDS, NEEDS.replace(" if plat == 5", "")),
    ("the length below 256", "length: number at 104 below 65", "length: number at 104 below 256"),
    # the trace: a contract that hides less says less
    ("every number is named", "trace depends on len, plat", "trace depends on len, t, flags, plat"),
    ("the input is named too", "trace depends on len, plat", "trace depends on len, plat, input"),
]
# (what is changed, the source as it is, the source changed, what the verifier then says)
KERNEL = "  mov rcx, r14\n  mov r8, qword ptr [rsp + 24]\n  call blake3_servil_compress_in_place_"
T_JUMP = ("a jump on the chunk's number", "  mov r14, rcx\n", "  mov r14, rcx\n  cmp rcx, 0\n  je @t0\n  mov rax, rax\n@t0:\n")
F_JUMP = ("a jump on the flags", "  mov qword ptr [rsp + 16], r8\n", "  mov qword ptr [rsp + 16], r8\n  cmp r8, 0\n  je @f0\n  mov rax, rax\n@f0:\n")
SOURCES = [
    ("the first block is not marked as the chunk's first", "  mov rax, 1\n  mov r12, rax\n", "  mov rax, 0\n  mov r12, rax\n", FOLLOW),
    ("every block is marked as the chunk's first", "  mov rax, 0\n  mov r12, rax\n", "  mov rax, 0\n", FOLLOW),
    ("the loop goes on while 63 < rem: the address after a last whole block may pass 2^64", "  mov rax, 64\n  mov rcx, rbp\n", "  mov rax, 63\n  mov rcx, rbp\n", ENTAIL),
    ("the loop goes on while 65 < rem: b3l_pad may be given 65 bytes", "  mov rax, 64\n  mov rcx, rbp\n", "  mov rax, 65\n  mov rcx, rbp\n", ENTAIL),
    ("the next block is taken 60 bytes on", "  mov rax, rbx\n  add rax, 64\n", "  mov rax, rbx\n  add rax, 60\n", FOLLOW),
    ("60 bytes are counted for a block: a kernel is given bytes past the input", "  mov rax, rbp\n  sub rax, 64\n", "  mov rax, rbp\n  sub rax, 60\n", KNOW),
    ("b3l_pad writes at byte 36 of the record", "  mov rax, r13\n  add rax, 32\n", "  mov rax, r13\n  add rax, 36\n", WORD),
    ("b3l_pad writes at byte 28 of the record", "  mov rax, r13\n  add rax, 32\n", "  mov rax, r13\n  add rax, 28\n", WORD),
    ("b3l_pad is given the whole length to read", "  mov rdx, rbp\n  call b3l_pad\n", "  mov rdx, qword ptr [rsp + 8]\n  call b3l_pad\n", KNOW),
    ("b3l_pad is given the input from its start", "  mov rsi, rbx\n  mov rdx, rbp\n  call b3l_pad\n", "  mov rsi, qword ptr [rsp + 0]\n  mov rdx, rbp\n  call b3l_pad\n", FOLLOW),
    ("b3l_pad is not called", "  call b3l_pad\n", "", FOLLOW),
    ("the chunk's number is stored at byte 100", "  add rcx, 96\n", "  add rcx, 100\n", WORD),
    ("the length left is stored for the chunk's number", "  mov rax, r14\n  mov rcx, r13\n  add rcx, 96\n", "  mov rax, rbp\n  mov rcx, r13\n  add rcx, 96\n", FOLLOW),
    ("the length is stored at byte 108", "  add rcx, 104\n", "  add rcx, 108\n", WORD),
    ("the flags are stored at byte 116: four bytes past the record", "  add rcx, 112\n", "  add rcx, 116\n", NOT_TWO),
    ("the flags are stored at byte 110: at no whole word", "  add rcx, 112\n", "  add rcx, 110\n", NOT_TWO),
    ("the flags are given 1 where the chunk's end is 2", "  or rax, 2\n", "  or rax, 1\n", FOLLOW),
    ("the flags are not given the chunk's end", "  or rax, 2\n", "", FOLLOW),
    ("the AVX-512 kernel is told a block is 63 bytes", "  mov rdx, 64\n" + KERNEL + "avx512\n", "  mov rdx, 63\n" + KERNEL + "avx512\n", FOLLOW),
    ("the SSE4.1 kernel is given 0 for the chunk's number", KERNEL + "sse41\n", KERNEL.replace("mov rcx, r14", "mov rcx, 0") + "sse41\n", FOLLOW),
    ("the AVX-512 kernel where `plat` is not 5", "  cmp rax, rcx\n  jne @l2\n", "  cmp rax, rcx\n  je @l2\n", NEEDS_MORE),
    # the trace: one instruction more is run where a number that the contract hides is not 0
    T_JUMP + (JUMP,),
    F_JUMP + (JUMP,),
]
TRUE_SOURCES = [
    ("the SSE4.1 kernel whatever `plat` is", "  cmp rax, rcx\n  jne @l2\n", "  cmp rax, rcx\n  jmp @l2\n"),
    ("the flags put together the other way round", "  mov rax, qword ptr [rsp + 16]\n  or rax, r12\n  or rax, 2\n",
     "  mov rax, r12\n  or rax, qword ptr [rsp + 16]\n  or rax, 2\n"),
]


def read(path):
    with open(path) as f: return f.read()


def inner(pattern):
    """A contract or a layout as ../kcheck/proofs/inner.spec has it."""
    (found,) = re.findall(pattern, read(os.path.join(KCHECK, "proofs", "inner.spec")), re.S | re.M)
    return found


def spec_text(change=lambda t: t):
    text = read(os.path.join(KCHECK, "blake3.spec"))
    for name in ("kernel.contract", "kernel_sse41.contract"): text += "\n" + read(os.path.join(HERE, "examples", "kernel", name))
    text += "\n" + inner(r"^contract b3l_pad\(.*?^\}\n") + "\n" + inner(r"^layout node120 .*?\n") + "\n" + inner(r"^contract b3l_chunk_node\(.*?^\}\n")
    return change(text)


def once(old, new):
    def change(text):
        assert text.count(old) == 1, (old, text.count(old))
        return text.replace(old, new)
    return change


def places(symbol): return read(os.path.join(HERE, "examples", "hash", "pad.places")) if symbol == PAD else ""


def last_word(functions, change=lambda t: t):
    """What the verifier says at last of the functions [(object, symbol)] with the proof that the prover
    writes for them: `shown`, or its last word where the prover has nothing more to write."""
    with tempfile.TemporaryDirectory() as d:
        try: prove.prove(spec_text(change), [(obj, symbol, places(symbol)) for obj, symbol in functions], os.path.join(d, "statement"), os.path.join(d, "proof"))
        except SystemExit as e:
            lines = [l for l in str(e).split("\n") if l.startswith(("refused:", "need "))]
            return lines[0] if lines else str(e)
        return "shown"


class Statement(unittest.TestCase):
    def test_the_contract_in_the_accounts_terms(self):
        lines = statement.statement(spec_text(), FUNCTIONS)
        at = lines.index(f"fn {CHUNK}")
        self.assertGreater(at, lines.index(f"fn {PAD}"))                         # after the three functions it calls
        mine = [l for l in lines[at + 1:] if not l.startswith(("i ", "def "))]
        self.assertEqual(mine, CONTRACT)
        self.assertEqual(len([l for l in lines[at + 1:] if l.startswith("i ")]), 81)
        # the record is written: what its layout asks of its numbers is part of the `ensures`, not asked at entry
        self.assertFalse([l for l in lines if l.startswith("mbelow nd")])
        # the specification's definitions the contract uses, as the account reads them
        defs = {l.split()[1]: l for l in lines if l.startswith("def ")}
        self.assertEqual(defs["block_count"], "def block_count bytes = (thenumber least n (num 1) (num 17) (bin >= (bin * (num 64) (name n)) (call len (name bytes))))")
        self.assertIn("(call chunk (name key) (call counter (name t)) (name flags) (call CHUNK_START) (num 0) (num 64) (bin - (name n) (num 1))", defs["chunk_node"])

    def test_no_overlap_must_be_said(self):
        with self.assertRaises(SystemExit) as e: statement.statement(spec_text(once("    requires no_overlap(nd, input)\n", "")), FUNCTIONS)
        self.assertIn("does not say `requires no_overlap(nd, input)`", str(e.exception))


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Meaning(unittest.TestCase):
    """The lines of the statement mean what the contract says: by the account in Lean (`odespec`), on bytes
    drawn at random, against ../kcheck/ode.py's reading of the specification."""
    @classmethod
    def setUpClass(cls):
        import ode
        built.built("odespec")
        cls.dir = tempfile.mkdtemp(prefix="odechunk-")
        cls.defs = os.path.join(cls.dir, "defs")
        with open(cls.defs, "w") as f: f.write("\n".join(l for l in statement.statement(spec_text(), FUNCTIONS) if l.startswith("def ")) + "\n")
        cls.ode, cls.spec = ode, ode.Spec(read(os.path.join(KCHECK, "blake3.spec")))
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

    def node(self, key, t, flags, message):
        """The 120 bytes of the record that ode.py's reading of `chunk_node` gives, laid out as node120."""
        A = self.ode.Numbers()
        env = {"k": list(key), "t": t, "f": flags, "m": list(message)}
        use = ("call", "chunk_node", [("call", "words", [("name", "k")]), ("name", "t"), ("name", "f"), ("name", "m")])
        r = self.spec.eval(A, use, env)
        h = bytes(self.spec.eval(A, ("call", "bytes_of", [("field", use, "h")]), env))
        return h + bytes(r["block"]) + r["counter"].to_bytes(8, "little") + r["length"].to_bytes(8, "little") + r["flags"].to_bytes(8, "little")

    def test_the_ensures_says_the_record_of_the_specification(self):
        rng = random.Random(51)
        cases, want = [], []
        for n in [0, 1, 63, 64, 65, 127, 128, 129, 500, 960, 961, 1023, 1024] + [rng.randrange(1025) for _ in range(12)]:
            nd = bytes(rng.randrange(256) for _ in range(120))
            message = bytes(rng.randrange(256) for _ in range(n))
            t, flags = rng.choice([0, 1, 2 ** 32 - 1, 2 ** 32, rng.randrange(2 ** 64), 2 ** 64 - 1]), rng.choice([0, 16, 32, 64, rng.randrange(256)])
            cases.append((ENSURES, {"nd": nd, "t": t, "flags": flags, "input": message}))
            want.append("bytes " + self.node(nd[:32], t, flags, message).hex())
        got = self.lean(cases)
        self.assertEqual(got, want)
        self.assertEqual(len(set(got)), len(got))
        # where a number is not below what the layout asks, the `ensures` has no value: a chunk's number of
        # 2^64, flags of 256 or more, and a chunk of more than 1024 bytes (it has no count of blocks)
        nd, message = bytes(120), bytes(100)
        self.assertEqual(self.lean([(ENSURES, {"nd": nd, "t": 2 ** 64, "flags": 0, "input": message}),
                                    (ENSURES, {"nd": nd, "t": 0, "flags": 256, "input": message}),
                                    (ENSURES, {"nd": nd, "t": 0, "flags": 0, "input": bytes(1025)}),
                                    (ENSURES, {"nd": nd, "t": 2 ** 64 - 1, "flags": 253, "input": message})]),
                         ["none", "none", "none", "bytes " + self.node(nd[:32], 2 ** 64 - 1, 253, message).hex()])

    def test_a_chunks_node_gives_the_hash_of_a_message_of_one_chunk(self):
        """`node_value` of the record `chunk_node` gives with the key of plain hashing, the chunk's number 0 and
        no flags, taken as the root: the hash of the message, as ode.py works out `blake3` of it."""
        A = self.ode.Numbers()
        rng = random.Random(52)
        cases, want = [], []
        for n in (0, 1, 64, 65, 128, 1023, 1024):
            message = bytes(rng.randrange(256) for _ in range(n))
            cases.append(("(call bytes_of (call node_value (call chunk_node (call iv_words) (num 0) (num 0) (name m)) (call ROOT)))", {"m": message}))
            want.append("bytes " + bytes(self.spec.eval(A, ("call", "blake3", [("name", "m")]), {"m": list(message)})).hex())
        self.assertEqual(self.lean(cases), want)


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Verify(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.dir = tempfile.mkdtemp(prefix="odechunk-")
        cls.source = read(os.path.join(KCHECK, "hash.ode"))
    @classmethod
    def tearDownClass(cls): shutil.rmtree(cls.dir)

    def chunk_from(self, old, new):
        """The function built again from its source, with one place of it changed: the functions to show."""
        text = self.source
        start = text.index('fn chunk_node as "b3l_chunk_node" {'); end = text.index("\n}\n", start)
        body = text[start:end]
        self.assertEqual(body.count(old), 1, old)
        text = text[:start] + body.replace(old, new) + text[end:]
        src, obj = os.path.join(self.dir, "changed.ode"), os.path.join(self.dir, "changed.o")
        with open(src, "w") as f: f.write(text)
        odec.build(src, "chunk_node", obj)
        return FUNCTIONS[:3] + [(obj, CHUNK)]

    def kept(self, symbols=(AVX512, SSE41, PAD, CHUNK), change=lambda symbol, text: text):
        """The kept proofs of these functions, in one file."""
        path = os.path.join(self.dir, "kept.proof")
        with open(path, "w") as out:
            for symbol in symbols: out.write(change(symbol, read(os.path.join(HERE, "proofs", symbol + ".proof"))))
        return path

    def verify(self, proof): return lean_verify.verify(spec_text(), FUNCTIONS, proof)

    def test_the_function_is_shown_with_the_functions_it_calls(self):
        self.assertEqual(self.verify(self.kept()), (True, "shown"))
        # the function built again from its source is the shipped one, and the prover finds the kept proof again
        again = self.chunk_from("  push rbx\n  push rbp\n", "  push rbx\n  push rbp\n")
        statement_path, proof_path = os.path.join(self.dir, "s"), os.path.join(self.dir, "p")
        prove.prove(spec_text(), [(obj, symbol, places(symbol)) for obj, symbol in again], statement_path, proof_path)
        self.assertEqual(read(statement_path).split("\n")[:-1], statement.statement(spec_text(), FUNCTIONS))
        found, kept = read(proof_path), read(os.path.join(HERE, "proofs", CHUNK + ".proof"))
        self.assertEqual(found[found.index("for " + CHUNK):], kept)
        self.assertEqual(kept.split("\n")[0], "for " + CHUNK)
        # controls: a function it calls is not taken as shown without its proof
        for left_out in (AVX512, SSE41, PAD):
            with self.subTest(left_out=left_out):
                shown, said = self.verify(self.kept([s for s in (AVX512, SSE41, PAD, CHUNK) if s != left_out]))
                self.assertFalse(shown)

    def test_a_changed_proof_is_refused(self):
        lines = read(os.path.join(HERE, "proofs", CHUNK + ".proof")).split("\n")[:-1]
        self.assertGreater(len(lines), 600)
        rng = random.Random(53)
        picked = sorted(rng.sample(range(1, len(lines)), 12))
        changed = [(f"line {k + 1} left out", lines[:k] + lines[k + 1:]) for k in picked] + \
                  [("a line more", lines + ["t live"]), ("the last line left out", lines[:-1]), ("another function's name", ["for " + PAD] + lines[1:])]
        for what, new in changed:
            with self.subTest(what=what):
                self.assertFalse(self.verify(self.kept(change=lambda symbol, text: "\n".join(new) + "\n" if symbol == CHUNK else text))[0])

    def test_a_wrong_contract_is_refused(self):
        for what, old, new, word in CONTRACTS:
            with self.subTest(what=what):
                self.assertEqual(last_word(FUNCTIONS, once(old, new)), word)

    def test_a_changed_contract_that_is_true_is_shown(self):
        for what, old, new in TRUE_CONTRACTS:
            with self.subTest(what=what):
                self.assertEqual(last_word(FUNCTIONS, once(old, new)), "shown")

    def test_a_wrong_function_is_refused(self):
        for what, old, new, word in SOURCES:
            with self.subTest(what=what):
                self.assertEqual(last_word(self.chunk_from(old, new)), word)

    def test_a_changed_function_that_is_right_is_shown(self):
        for what, old, new in TRUE_SOURCES:
            with self.subTest(what=what):
                self.assertEqual(last_word(self.chunk_from(old, new)), "shown")

    def test_a_jump_on_a_number_is_shown_where_the_contract_names_the_number(self):
        """The two functions that test_a_wrong_function_is_refused has refused for a jump on a number the
        contract hides: each computes what the contract says, and is shown where the contract names that number."""
        for (what, old, new), line in ((T_JUMP, "trace depends on len, t, plat"), (F_JUMP, "trace depends on len, flags, plat")):
            with self.subTest(what=what):
                self.assertEqual(last_word(self.chunk_from(old, new), once("trace depends on len, plat", line)), "shown")


if __name__ == "__main__":
    unittest.main()
