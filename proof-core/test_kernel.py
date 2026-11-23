#!/usr/bin/env python3
"""The hash's two one-block kernels in the verifier in Lean: `blake3_servil_compress_in_place_avx512` and
`blake3_servil_compress_in_place_sse41`.

    python3 test_kernel.py        (the tests of the verifier are skipped where Lean's `lake` is not installed)

Each is a function of ../kcheck/b3hashr.o (76 and 94 instructions; their source: ../wide/one.ode). A kernel's
contract gives it eight words to read and write (`h: cv`), sixteen to read (`m: block`), a counter, the
length and the flags, and promises `h = compress(h, m, t, length, flags)`: BLAKE3's compression function as
../kcheck/blake3.spec defines it. statement.py writes that in the account's terms: 32 bytes read and
written, 64 bytes read, three numbers, and the run `h` at the return being the bytes of the words `compress`
gives of the words of the bytes at entry.

The two differ in how they take the length and the flags, and in their instructions:

    AVX-512    the low byte of each register (`low byte`); a turn of a word is one instruction (vprord)
    SSE4.1     the length is a number the caller keeps below 2^32 (`word`: the statement's line
               `below length 4294967296`), the flags are the low 32 bits of their register (`low word`);
               a turn of a word is a shift to the left, a shift to the right and an or of the two, or a
               shuffle of bytes by one of two constants

The verifier shows both. It follows each of the four low words of a vector register as a term over the
words read at entry (a sum, an exclusive or, a turn to the right, a shift), goes seven times round the loop
by the count the function keeps in a byte, and at the return works the specification's `compress` out on
the same terms: each word it gives must be the term stored at its place of `h`. An or of two shifts of one
word that make up 32 bits is taken as the turn it is, and so is a shuffle of bytes by one of the two
constants; any other or, shuffle or blend of half-words is refused. The proofs are 130 and 137 bytes: two
proofs of arithmetic each, about the 64-bit number that holds the length and the flags, and for the SSE4.1
kernel the line `t wrap`: the flags' register is shifted left by 32 bits, and what is above its low 32
bits is lost (nothing says it is zero).

With the specification, the contract or the function changed in one place the verifier does not say
`shown`, and the prover finds no proof; each case names what the verifier then says. With a line of the
proof left out or changed it does not say `shown`.

The contracts have no `trace` line, as the kernels' real contracts have none (../kcheck/proofs/inner.spec):
which instructions run and which addresses are touched depend on nothing that is given: on no byte of `h` or
`m`, and not on the length, the counter or the flags. The account in Lean marks the bytes of `m` and the
registers of the three numbers (the lines `hidden m`, `hidden length`, `hidden t`, `hidden flags` of the
statement) and whatever is worked out of them or read of `h`, and the verifier refuses where something
marked could decide a jump or be part of an address: `test_the_trace` changes the kernel so that it does.
What a function leaves in a register is no part of the trace, and its caller may rely on nothing of it
(but the number returned, where the contract returns one): a word of the block left in a register is shown."""
import os, shutil, subprocess, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "lang"))
import built, lean_verify, odec, prove, statement
KCHECK = os.path.join(HERE, "..", "kcheck")
LAKE = lean_verify.LAKE
SYMBOL = "blake3_servil_compress_in_place_avx512"
SSE41 = "blake3_servil_compress_in_place_sse41"
CONTRACT = ["arg h inout 32", "arg m fixed 64", "arg length number", "arg t number", "arg flags number", "needs avx512", "hidden m",
            "hidden length", "hidden t", "hidden flags",
            "ensuresw h (call bytes_of (call compress (call words (name h)) (call words (name m)) (call counter (name t)) "
            "(bin % (name length) (num 256)) (bin % (name flags) (num 256))))", "stack 0"]
CONTRACT_SSE41 = ["arg h inout 32", "arg m fixed 64", "arg length number", "arg t number", "arg flags number", "below length 4294967296", "needs sse41", "hidden m",
                  "hidden length", "hidden t", "hidden flags",
                  "ensuresw h (call bytes_of (call compress (call words (name h)) (call words (name m)) (call counter (name t)) "
                  "(name length) (bin % (name flags) (num 4294967296))))", "stack 0"]
# what the verifier says where it does not say `shown`
FOLLOW = "the specification's words are not followed on the terms the function made"    # a word the specification gives is no term the function made
HOLD = "a word of the run is not known to hold what the specification says"            # every word is a term the function made, but not the one stored there
WORDS = "sixteen bytes that are not four words of the run"                             # a load or a store that is not of whole words inside a run
NO_RUN = "sixteen bytes written to what is no run given to write"
AGAIN = "a read of a run given to read and write after it was written to"
ENTAIL = "need entail"                                                                 # something is to be shown of numbers, and the prover has no proof of it
OR_TURN = "an or of two vector registers that is no turn of each word"                 # (SSE4.1) the two are not one word shifted left and right by 32 bits in all
SHUFFLE = "a shuffle of bytes that is no turn of each word by 8 or 16 bits"            # (SSE4.1) the constant is neither of the two
SPLIT = "a blend of halves that splits a word"                                         # (SSE4.1) a word would be half of one register and half of the other
RESULT = "[s[7][i] ^ s[7][i + 8] for i in 0..8]"
# (what is changed, the text as it is, the text changed, what the verifier then says): the specification
SPECS = [
    ("a turn by 15 for 16", ">>> 16", ">>> 15", FOLLOW),
    ("a turn by 13 for 12", ">>> 12", ">>> 13", FOLLOW),
    ("a turn by 9 for 8", ">>> 8", ">>> 9", FOLLOW),
    ("a turn by 9 for 7", ">>> 7", ">>> 9", FOLLOW),
    ("a word of the constants", "0x6A09E667", "0x6A09E668", FOLLOW),
    ("two places of the permutation exchanged", "2, 6, 3, 10", "6, 2, 3, 10", FOLLOW),
    ("the counter's halves exchanged", "lo(t), hi(t)", "hi(t), lo(t)", FOLLOW),
    ("the length and the flags exchanged", "word(length), word(flags)", "word(flags), word(length)", FOLLOW),
    ("two words of the block exchanged in a column", "g(c1, 1, 5, 9, 13, m[2], m[3])", "g(c1, 1, 5, 9, 13, m[3], m[2])", FOLLOW),
    ("a diagonal mixes another word", "g(d1, 1, 6, 11, 12,", "g(d1, 1, 6, 11, 13,", FOLLOW),
    ("six rounds", RESULT, RESULT.replace("s[7]", "s[6]"), FOLLOW),
    ("eight rounds", RESULT, RESULT.replace("s[7]", "s[8]"), FOLLOW),
    ("the block is not permuted between rounds", "let w[r + 1] = [w[r][PERMUTATION[i]] for i in 0..16]", "let w[r + 1] = w[r]", FOLLOW),
    ("the two halves of the state are not joined", RESULT, "[s[7][i] for i in 0..8]", HOLD),
    ("seven words are promised", RESULT, RESULT.replace("0..8", "0..7"), HOLD),
]
# the same of each kernel's contract
CONTRACTS = [
    ("the contract: the length and the flags exchanged", "ensures h = compress(h, m, t, length, flags)", "ensures h = compress(h, m, t, flags, length)", FOLLOW),
    ("the contract: the whole of the length's register", "length: low byte", "length: number", FOLLOW),
    ("the contract: the whole of the flags' register", "flags: low byte", "flags: number", FOLLOW),
    ("the contract: the counter is a plain number", "t: counter", "t: number", FOLLOW),
    ("the contract: the block and the value exchanged", "ensures h = compress(h, m, t, length, flags)", "ensures h = compress(m, h, t, length, flags)", FOLLOW),
]
CONTRACTS_SSE41 = [
    ("the contract: the length and the flags exchanged", "ensures h = compress(h, m, t, length, flags)", "ensures h = compress(h, m, t, flags, length)", FOLLOW),
    # the function adds the whole of the length's register to the flags shifted: a length of 2^32 or more would spoil the flags
    ("the contract: the caller need not keep the length below 2^32", "m: block, length: word, t: counter", "m: block, length: number, t: counter", ENTAIL),
    ("the contract: only the low 32 bits of the length's register are the length", "m: block, length: word, t: counter", "m: block, length: low word, t: counter", ENTAIL),
    ("the contract: the counter is a plain number", "t: counter", "t: number", FOLLOW),
    ("the contract: the block and the value exchanged", "ensures h = compress(h, m, t, length, flags)", "ensures h = compress(m, h, t, length, flags)", FOLLOW),
]
END = "  ret\n}\n\n// The same for processors with SSE4.1"            # (the end of this kernel in ../wide/one.ode: the other kernel there ends alike)
STORES = "  vmovdqu xmmword ptr [rdi], xmm0\n  vmovdqu xmmword ptr [rdi+0x10], xmm1\n" + END
# (what is changed, the source as it is, the source changed, what the verifier then says)
SOURCES = [
    ("a turn by 15 for 16", "  vprord d, d, 16\n", "  vprord d, d, 15\n", FOLLOW),
    ("a turn by 6 for 7", "  vprord b, b, 7\n", "  vprord b, b, 6\n", FOLLOW),
    ("the block's words taken the other way", "  vshufps xmm4, xmm8, xmm9, 136\n  vshufps xmm5, xmm8, xmm9, 221\n  vmovups xmm8, xmmword ptr [rsi+0x20]",
     "  vshufps xmm4, xmm8, xmm9, 221\n  vshufps xmm5, xmm8, xmm9, 136\n  vmovups xmm8, xmmword ptr [rsi+0x20]", FOLLOW),
    ("six rounds", "  vpshufd xmm7, xmm7, 0x93\n  mov al, 7\n", "  vpshufd xmm7, xmm7, 0x93\n  mov al, 6\n", FOLLOW),
    ("a row of the state turned the other way", "  g_avx512(xmm0, xmm1, xmm2, xmm3, xmm4, xmm5)\n  vpshufd xmm0, xmm0, 0x93\n", "  g_avx512(xmm0, xmm1, xmm2, xmm3, xmm4, xmm5)\n  vpshufd xmm0, xmm0, 0x39\n", FOLLOW),
    ("the block's permutation changed in one word", "  vpblendd xmm9, xmm9, xmm8, 0xAA\n", "  vpblendd xmm9, xmm9, xmm8, 0xA8\n", FOLLOW),
    ("the halves of the state joined crosswise", "  vpxor xmm0, xmm0, xmm2\n  vpxor xmm1, xmm1, xmm3\n", "  vpxor xmm0, xmm0, xmm3\n  vpxor xmm1, xmm1, xmm2\n", FOLLOW),
    ("the counter and the length exchanged", "  vmovq xmm3, rcx\n  vmovq xmm4, rdx\n", "  vmovq xmm3, rdx\n  vmovq xmm4, rcx\n", FOLLOW),
    ("a word of the constants", "data one_iv = 0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A", "data one_iv = 0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53B", FOLLOW),
    ("the flags put one bit lower", "  shl rax, 32\n  add rdx, rax\n  vmovq xmm3, rcx", "  shl rax, 31\n  add rdx, rax\n  vmovq xmm3, rcx", FOLLOW),
    ("the whole of the length's register is taken", "  movzx eax, r8b\n  movzx edx, dl\n", "  movzx eax, r8b\n", ENTAIL),
    ("the last four words are not stored", STORES, "  vmovdqu xmmword ptr [rdi], xmm0\n" + END, HOLD),
    ("the two stores exchanged", STORES, "  vmovdqu xmmword ptr [rdi], xmm1\n  vmovdqu xmmword ptr [rdi+0x10], xmm0\n" + END, HOLD),
    ("a store four bytes on, past the run's end", STORES, STORES.replace("[rdi+0x10]", "[rdi+0x14]"), WORDS),
    ("a store into the block, which is only to be read", STORES, STORES.replace(END, "  vmovdqu xmmword ptr [rsi], xmm1\n" + END), NO_RUN),
    ("what was stored is read again", STORES, STORES.replace("  vmovdqu xmmword ptr [rdi+0x10], xmm1\n", "  vmovdqu xmm0, xmmword ptr [rdi]\n  vmovdqu xmmword ptr [rdi+0x10], xmm1\n"), AGAIN),
    ("the block read sixteen bytes on, past its end", "  vmovups xmm9, xmmword ptr [rsi+0x30]\n  vshufps xmm6, xmm8, xmm9, 136", "  vmovups xmm9, xmmword ptr [rsi+0x40]\n  vshufps xmm6, xmm8, xmm9, 136", WORDS),
    ("the block read two bytes on", "  vmovups xmm8, xmmword ptr [rsi]\n  vmovups xmm9, xmmword ptr [rsi+0x10]\n", "  vmovups xmm8, xmmword ptr [rsi+2]\n  vmovups xmm9, xmmword ptr [rsi+0x10]\n", WORDS),
]


END_SSE41 = "  ret\n}\n"                                               # (the file's end)
STORES_SSE41 = "  movups xmmword ptr [rdi], xmm0\n  movups xmmword ptr [rdi+0x10], xmm1\n" + END_SSE41
SOURCES_SSE41 = [
    ("a shift to the left by 19 for 20", "  pslld b, 20\n", "  pslld b, 19\n", OR_TURN),
    ("a shift to the right by 13 for 12", "  psrld t, 12\n", "  psrld t, 13\n", OR_TURN),
    ("a turn by 8 for 7", "  pslld b, 25\n  psrld t, 7\n", "  pslld b, 24\n  psrld t, 8\n", FOLLOW),
    ("the or takes another register", "  por b, t\n  paddd a, y\n", "  por b, d\n  paddd a, y\n", OR_TURN),
    ("the shuffle for 8 bits where that for 16 is", "  pshufb d, rot16\n", "  pshufb d, rot8\n", FOLLOW),
    ("a byte of a shuffle's constant", "data one_rot8 = 0x00030201, 0x04070605, 0x080B0A09, 0x0C0F0E0D", "data one_rot8 = 0x00030201, 0x04070605, 0x080B0A09, 0x0C0F0E0C", SHUFFLE),
    ("a blend that takes half a word", "  pblendw xmm9, xmm8, 0xCC\n", "  pblendw xmm9, xmm8, 0xC4\n", SPLIT),
    ("a blend of another word", "  pblendw xmm8, xmm6, 0xC0\n", "  pblendw xmm8, xmm6, 0x30\n", FOLLOW),
    ("six rounds", "  movaps xmm15, xmmword ptr [rip + #one_rot16]\n  mov al, 7\n", "  movaps xmm15, xmmword ptr [rip + #one_rot16]\n  mov al, 6\n", FOLLOW),
    ("the flags are not shifted", "  shl r8, 32\n  add rdx, r8\n", "  add rdx, r8\n", ENTAIL),
    ("the flags put one bit lower", "  shl r8, 32\n", "  shl r8, 31\n", ENTAIL),
    ("the counter and the length exchanged", "  movq xmm3, rcx\n  movq xmm4, rdx\n", "  movq xmm3, rdx\n  movq xmm4, rcx\n", FOLLOW),
    ("the halves of the state joined crosswise", "  pxor xmm0, xmm2\n  pxor xmm1, xmm3\n  movups", "  pxor xmm0, xmm3\n  pxor xmm1, xmm2\n  movups", FOLLOW),
    ("the last four words are not stored", STORES_SSE41, "  movups xmmword ptr [rdi], xmm0\n" + END_SSE41, HOLD),
    ("the two stores exchanged", STORES_SSE41, "  movups xmmword ptr [rdi], xmm1\n  movups xmmword ptr [rdi+0x10], xmm0\n" + END_SSE41, HOLD),
    ("a store into the block, which is only to be read", STORES_SSE41, STORES_SSE41.replace(END_SSE41, "  movups xmmword ptr [rsi], xmm1\n" + END_SSE41), NO_RUN),
    ("what was stored is read again", STORES_SSE41, STORES_SSE41.replace("  movups xmmword ptr [rdi+0x10], xmm1\n", "  movups xmm0, xmmword ptr [rdi]\n  movups xmmword ptr [rdi+0x10], xmm1\n"), AGAIN),
    ("the block read sixteen bytes on, past its end", "  movups xmm7, xmmword ptr [rsi+0x30]\n", "  movups xmm7, xmmword ptr [rsi+0x40]\n", WORDS),
]


class One:
    """What differs between the two kernels."""
    def __init__(self, symbol, fn, contract, lines, instructions, contracts, sources, kinds, first, landmarks, needs):
        self.symbol, self.fn, self.contract, self.lines, self.instructions = symbol, fn, contract, lines, instructions
        self.contracts, self.sources, self.kinds, self.first, self.landmarks, self.needs = contracts, sources, kinds, first, landmarks, needs


AVX512 = One(SYMBOL, "compress1", "kernel.contract", CONTRACT, 76, CONTRACTS, SOURCES,
             {"left out": 8, "a step's multiplier": 4, "a row it starts from": 2}, "need entail",
             ["i 98 100 .mov 8 (.reg .rax) (.imm 0x7)", "i 282 284 .decb .rax"],         # the count of rounds, kept in a byte
             [("no line of what the processor must have", "    needs avx512\n", "", "holds instructions of a kind its contract does not say it needs: avx, avx512"),
              ("the processor is asked for too little", "    needs avx512\n", "    needs sse41\n", "holds instructions of a kind its contract does not say it needs: avx, avx512")])
SSE = One(SSE41, "compress1_sse41", "kernel_sse41.contract", CONTRACT_SSE41, 94, CONTRACTS_SSE41, SOURCES_SSE41,
          {"left out": 9, "a step's multiplier": 4, "a row it starts from": 2, "exact for wrap": 1}, "need shift",
          ["i 107 109 .mov 8 (.reg .rax) (.imm 0x7)", "i 327 329 .decb .rax"],
          [("no line of what the processor must have", "    stack 0\n    needs sse41\n", "    stack 0\n", "holds instructions of a kind its contract does not say it needs: sse41")])


def spec_text(change=lambda t: t, contract="kernel.contract"):
    with open(os.path.join(KCHECK, "blake3.spec")) as f: spec = f.read()
    with open(os.path.join(HERE, "examples", "kernel", contract)) as f: text = f.read()
    return change(spec + "\n" + text)


class StatementTests:
    """The contract as statement.py writes it for the verifier in Lean. `K` is the kernel (a subclass says which)."""
    def lines(self, change=lambda t: t):
        return statement.statement(spec_text(change, self.K.contract), [(os.path.join(KCHECK, "b3hashr.o"), self.K.symbol)])

    def test_the_contract_in_the_accounts_terms(self):
        lines = self.lines()
        self.assertEqual([l for l in lines if l.split()[0] not in ("fn", "i", "def")], self.K.lines)
        self.assertEqual(sum(l.startswith("i ") for l in lines), self.K.instructions)

    def test_a_contract_that_promises_more_or_other_than_is_read_is_refused(self):
        for what, old, new, why in [
                ("no line of what overlaps", "    requires no_overlap(h, m)\n", "", "does not say `requires no_overlap(h, m)`"),
                ("a part of the words", "ensures h = compress", "ensures h[0 .. 16] = compress", "of a part of a run of words"),
                ("a number returned too", "    stack 0\n", "    returns length\n    stack 0\n", "returns a number beside arguments of the kinds"),
                ("a kind not read", "m: block", "m: 16 words", "an argument of a kind the verifier in Lean does not read yet: m: 16 words"),
                # the machine of the account has every instruction; a processor has those of the kinds it has
                ] + self.K.needs:
            with self.subTest(what=what):
                with self.assertRaises(SystemExit) as e: self.lines(lambda t: (self.assertEqual(t.count(old), 1), t.replace(old, new))[1])
                self.assertIn(why, str(e.exception))


class StatementAvx512(StatementTests, unittest.TestCase): K = AVX512
class StatementSse41(StatementTests, unittest.TestCase): K = SSE


class KernelTests:
    """A kernel in the verifier. `K` is the kernel (a subclass says which)."""
    @classmethod
    def setUpClass(cls):
        built.built("odeverify")
        cls.dir = tempfile.mkdtemp(prefix="odekernel-")
        cls.obj = os.path.join(KCHECK, "b3hashr.o")
        cls.spec = spec_text(contract=cls.K.contract)
        with open(os.path.join(HERE, "..", "wide", "one.ode")) as f: cls.source = f.read()
        cls.kept = os.path.join(HERE, "proofs", cls.K.symbol + ".proof")

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.dir)

    def path(self, name): return os.path.join(self.dir, name)

    def found(self, spec, obj, name="try"):
        """The prover's numbers; or, where it finds no proof, the verifier's last word."""
        try: return prove.prove(spec, [(obj, self.K.symbol, "")], self.path(name + ".statement"), self.path(name + ".proof"))
        except SystemExit as e:
            said = str(e)
            self.assertTrue(said.startswith("prove: no proof of " + self.K.symbol), said[:200])
            return said.split("\n", 1)[1]

    def changed(self, old, new):
        self.assertEqual(self.spec.count(old), 1, old)
        return self.spec.replace(old, new)

    def test_shown_and_the_kept_proof_is_what_the_prover_finds(self):
        symbol = self.K.symbol
        numbers = self.found(self.spec, self.obj, "shown")
        self.assertEqual(list(numbers), [symbol])
        self.assertEqual(lean_verify.verify(self.spec, [(self.obj, symbol)], self.kept), (True, "shown"))
        with open(self.kept) as f, open(self.path("shown.proof")) as g: self.assertEqual(f.read(), g.read())
        self.assertLess(os.path.getsize(self.kept), 1000)
        with open(self.path("shown.statement")) as f: lines = f.read().splitlines()
        for line in self.K.landmarks: self.assertIn(line, lines)
        # the kernel made again from its source is the same instructions, and is shown by the same proof
        odec.build(os.path.join(HERE, "..", "wide", "one.ode"), self.K.fn, self.path("one.o"))
        again = statement.statement(self.spec, [(self.path("one.o"), symbol)])
        self.assertEqual([l for l in again if l.startswith("i ")], [l for l in lines if l.startswith("i ")])
        self.assertEqual(lean_verify.verify(self.spec, [(self.path("one.o"), symbol)], self.kept), (True, "shown"))

    def test_a_contract_that_promises_less_is_shown_too(self):
        # (so the cases below are not refused for being changed: `stack 8` is true of a function that uses none)
        self.assertEqual(lean_verify.verify(self.changed("    stack 0\n    needs", "    stack 8\n    needs"), [(self.obj, self.K.symbol)], self.kept), (True, "shown"))

    def test_the_specification_or_the_contract_changed_in_one_place(self):
        for what, old, new, why in SPECS + self.K.contracts:
            with self.subTest(what=what):
                spec = self.changed(old, new)
                self.assertFalse(lean_verify.verify(spec, [(self.obj, self.K.symbol)], self.kept)[0], what)
                last = self.found(spec, self.obj)
                self.assertIsInstance(last, str, what)                      # no proof is found
                self.assertIn(why, last.split("\n")[0], what)

    def test_the_function_changed_in_one_place(self):
        for what, old, new, why in self.K.sources:
            with self.subTest(what=what):
                self.assertEqual(self.source.count(old), 1)
                with open(self.path("changed.ode"), "w") as f: f.write(self.source.replace(old, new))
                odec.build(self.path("changed.ode"), self.K.fn, self.path("changed.o"))
                self.assertFalse(lean_verify.verify(self.spec, [(self.path("changed.o"), self.K.symbol)], self.kept)[0], what)
                last = self.found(self.spec, self.path("changed.o"))
                self.assertIsInstance(last, str, what)
                self.assertIn(why, last.split("\n")[0], what)

    def test_the_trace(self):
        """The kernel changed so that which instructions run depends on a word of the block, or on one of the
        three numbers given (one instruction more is run where it is 0): refused. The same function against a
        contract that says the trace may depend on that word or number: shown."""
        start = f'fn {self.K.fn} as "{self.K.symbol}" {{\n  .p2align 6\n'
        self.assertEqual(self.source.count(start), 1)
        jump = "  jne @seen\n  xor r9d, r9d\n@seen:\n  xor r9d, r9d\n"
        for what, added, name in (
                ("a jump on a word of the block", "  mov r9, qword ptr [rsi + 0]\n  test r9, r9\n" + jump, "m"),
                ("a jump on the length", "  test rdx, rdx\n" + jump, "length"),
                ("a jump on the counter", "  test rcx, rcx\n" + jump, "t"),
                ("a jump on the flags", "  test r8, r8\n" + jump, "flags")):
            with self.subTest(what=what):
                with open(self.path("trace.ode"), "w") as f: f.write(self.source.replace(start, start + added))
                odec.build(self.path("trace.ode"), self.K.fn, self.path("trace.o"))
                last = self.found(self.spec, self.path("trace.o"), "trace")
                self.assertIsInstance(last, str, what)
                self.assertIn("a jump on a flag that may depend on a secret", last.split("\n")[0], what)
                # (the function is not refused for being changed: it does what the contract says of the words)
                named = self.changed("    stack 0\n", f"    stack 0\n    trace depends on {name}\n")
                self.assertNotIsInstance(self.found(named, self.path("trace.o"), "named"), str, what)

    def test_what_is_left_in_a_register_is_no_part_of_the_trace(self):
        """The kernel changed so that it returns with a word of the block in r9, a register its caller may rely
        on nothing about: shown. (Until a function could rely only on what a contract says about a register,
        this was refused: no register that a called function need not keep could hold a secret at the return.)"""
        start = f'fn {self.K.fn} as "{self.K.symbol}" {{\n  .p2align 6\n'
        with open(self.path("left.ode"), "w") as f: f.write(self.source.replace(start, start + "  mov r9, qword ptr [rsi + 0]\n"))
        odec.build(self.path("left.ode"), self.K.fn, self.path("left.o"))
        self.assertNotIsInstance(self.found(self.spec, self.path("left.o"), "left"), str)

    def test_the_proof_changed(self):
        with open(self.kept) as f: proof = f.read().splitlines()
        with open(self.path("s.statement"), "w") as f: f.write("\n".join(statement.statement(self.spec, [(self.obj, self.K.symbol)])) + "\n")
        def said(lines):
            with open(self.path("c.proof"), "w") as f: f.write("".join(x + "\n" for x in lines))
            r = subprocess.run([lean_verify.EXE, lean_verify.TABLE, self.path("s.statement"), self.path("c.proof")], capture_output=True, text=True)
            self.assertEqual(r.returncode == 0, r.stdout == "shown\n", r.stdout[:200])
            return r.stdout
        self.assertEqual(said(proof), "shown\n")
        self.assertTrue(said(proof[:1]).startswith(self.K.first), "with no line of proof the verifier's last word names the first line it lacks")
        kinds = {}
        for k in range(1, len(proof)):                                     # (the first line names the function)
            l = proof[k]
            w = l.split()
            trials = [("left out", None)]
            if w[0] == "s": trials.append(("a step's multiplier", " ".join(w[:2] + [str(int(w[2]) + 1)] + w[3:])))
            if w[0] == "p": trials.append(("a row it starts from", " ".join(w[:1] + [str(int(w[1]) + 1)] + w[2:])))
            if l == "t wrap": trials.append(("exact for wrap", "t exact"))
            for kind, new in trials:
                lines = list(proof)
                if new is None: del lines[k]
                else: lines[k] = new
                self.assertNotEqual(said(lines), "shown\n", (k, l, kind))
                kinds[kind] = kinds.get(kind, 0) + 1
        self.assertEqual(kinds, self.K.kinds)


@unittest.skipUnless(LAKE, "Lean's lake is not installed")
class Avx512(KernelTests, unittest.TestCase): K = AVX512


@unittest.skipUnless(LAKE, "Lean's lake is not installed")
class Sse41(KernelTests, unittest.TestCase):
    K = SSE

    def test_contracts_that_ask_more_of_the_caller_or_the_processor_are_shown_too(self):
        # a processor with AVX-512 as well: the same proof
        self.assertEqual(lean_verify.verify(self.changed("    stack 0\n    needs sse41\n", "    stack 0\n    needs sse41\n    needs avx512\n"),
                                            [(self.obj, SSE41)], self.kept), (True, "shown"))
        # the caller keeps the flags below 2^32 too: then nothing is lost by the shift, and the proof has no `t wrap`
        spec = self.changed("flags: low word)", "flags: word)")
        self.assertIn("below flags 4294967296", statement.statement(spec, [(self.obj, SSE41)]))
        self.assertFalse(lean_verify.verify(spec, [(self.obj, SSE41)], self.kept)[0])
        self.assertEqual(list(self.found(spec, self.obj, "word")), [SSE41])
        with open(self.path("word.proof")) as f: self.assertNotIn("t wrap", f.read())

    def test_a_true_contract_that_is_not_shown_yet(self):
        """Not shown, of something true. With `flags: number` the specification's `word(flags)` is the low 32
        bits of the register, which is what the function takes; the verifier holds the function's word as the
        remainder it made at the shift and the specification's as the register's own word, and does not see
        that the two are one. (Kept so that it is seen when this changes.)"""
        spec = self.changed("flags: low word)", "flags: number)")
        last = self.found(spec, self.obj)
        self.assertIsInstance(last, str)
        self.assertIn(FOLLOW, last.split("\n")[0])


if __name__ == "__main__":
    unittest.main()
