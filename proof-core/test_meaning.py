#!/usr/bin/env pypy3
"""What statement.py writes for the hash's kernels and for `b3l_pad` means what their contracts say.

    pypy3 test_meaning.py        (skipped where Lean's `lake` is not installed)

The soundness theorem is about the statement: the file statement.py writes from an object file and a
contract. A verdict relies on statement.py for that file saying what the contract says: were an `ensures`
written there to say something else, the verifier would show that something else, and rightly.

So for each of these functions the statement's `ensures` line is worked out by the account in Lean
(`odespec`: `evalSpec` of Contract.lean) on inputs drawn at random, and compared with a reading of the
contract that goes through neither statement.py nor Lean: ../kcheck/ode.py works out the specification's
`compress` or `chunk` of the same inputs, each argument taken by its kind as kcheck/LANGUAGE.md says it
(`low byte`: the register's number modulo 256; `bytes flags start end length`: the four low bytes of the
register; a table of sixteen or thirty-two addresses: that many inputs of `n` blocks each).

    the two one-block kernels       ensures h = compress(h, m, t, length, flags)
    the 16-way kernel               ensures out[i] = chunk(key, t, flags, start, end, length, n, inputs[i]) for i in 0..16
    the 32-way kernel               the same for i in 0..32
    its entry the hash calls        … chunk(key, t + i, …) …
    b3l_pad                         ensures block = padded(src)

(`b3l_node_out` and `b3l_chunk_node` have the like in test_node.py and test_chunk.py; the three examples of
a part of a run handed on, in test_part.py, test_record.py and test_tail.py.)

Each case has a control: with one input changed the two still agree with each other and differ from before,
so the comparison is of values that depend on the inputs."""
import os, random, sys, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
KCHECK = os.path.join(HERE, "..", "kcheck")
sys.path.insert(0, HERE); sys.path.insert(0, KCHECK); sys.path.insert(0, os.path.join(HERE, "..", "lang"))
import ensures_meaning as meaning, lean_verify, ode, test_k32, test_kernel, test_p16, test_p32, test_pad

OBJ = os.path.join(KCHECK, "b3hashr.o")


def lanes_let(count, n, expr):
    """The expression with `inputs` bound as the account binds a table of addresses: `count` inputs, each a
    list of `n` blocks, each block the sixteen words of 64 bytes. Input i's bytes are named lane{i}."""
    lane = lambda i: f"(each (call words (slice (name lane{i}) (bin * (num 64) (name b)) (bin + (bin * (num 64) (name b)) (num 64)))) b (num 0) (num {n}))"
    return f"(let inputs (list {' '.join(lane(i) for i in range(count))}) {expr})"


@unittest.skipUnless(lean_verify.LAKE, "Lean's lake is not installed")
class Meaning(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        with open(os.path.join(KCHECK, "blake3.spec")) as f: cls.spec = ode.Spec(f.read())

    def value(self, use, env): return bytes(self.spec.eval(ode.Numbers(), ("call", "bytes_of", [use]), env))

    def compress(self, h, m, t, length, flags):
        use = ("call", "compress", [("call", "words", [("name", "h")]), ("call", "words", [("name", "m")]), ("call", "counter", [("name", "t")]), ("name", "length"), ("name", "flags")])
        return self.value(use, {"h": list(h), "m": list(m), "t": t, "length": length, "flags": flags})

    def chunk(self, key, t, plus, flags, start, end, length, blocks):
        """`chunk` of the specification: the chaining value after the blocks (each 64 bytes), as bytes. The
        chunk's number is the counter `t`, or `t + plus` as ode.py adds a number to a counter."""
        A = ode.Numbers()
        words = [self.spec.eval(A, ("call", "words", [("name", "b")]), {"b": list(b)}) for b in blocks]
        number = ("call", "counter", [("name", "t")])
        if plus is not None: number = ("bin", "+", number, ("num", plus))
        use = ("call", "chunk", [("call", "words", [("name", "key")]), number] +
               [("name", x) for x in ("flags", "start", "end", "length", "n", "input")])
        return self.value(use, {"key": list(key), "t": t, "flags": flags, "start": start, "end": end, "length": length, "n": len(blocks), "input": words})

    def test_the_one_block_kernels(self):
        rng = random.Random(81)
        for K, length_of, flags_of in ((test_kernel.AVX512, lambda x: x % 256, lambda x: x % 256), (test_kernel.SSE, lambda x: x, lambda x: x % 2 ** 32)):
            with self.subTest(kernel=K.symbol):
                functions = [(OBJ, K.symbol)]
                text = test_kernel.spec_text(contract=K.contract)
                line = meaning.ensures(text, functions, K.symbol, "h")
                cases, want = [], []
                for _ in range(8):
                    h, m = bytes(rng.randrange(256) for _ in range(32)), bytes(rng.randrange(256) for _ in range(64))
                    t = rng.choice([0, 1, 2 ** 32 - 1, 2 ** 32, rng.randrange(2 ** 64)])
                    # (the SSE4.1 kernel's contract asks a length below 2^32; of the other numbers the registers' high bytes are free)
                    length = rng.randrange(65) if K is test_kernel.SSE else rng.randrange(65) + 256 * rng.randrange(2 ** 20)
                    flags = rng.randrange(256) + rng.choice([0, 256 * rng.randrange(2 ** 40)])
                    for m_ in (m, bytes([m[0] ^ 1]) + m[1:]):                    # (the second: a control, one bit of the block changed)
                        cases.append((line, {"h": h, "m": m_, "t": t, "length": length, "flags": flags}))
                        want.append("bytes " + self.compress(h, m_, t, length_of(length), flags_of(flags)).hex())
                got = meaning.account(text, functions, cases)
                self.assertEqual(got, want)
                self.assertEqual(len(set(got)), len(got))

    def wide(self, module, symbol, count, plus):
        """The kernel of `count` lanes: lane i is given the chunk's number `t`, or `t + plus(i)`."""
        rng = random.Random(82 + count)
        functions = [(OBJ, symbol)]
        text = module.spec_text()
        line = meaning.ensures(text, functions, symbol, "out")
        cases, want = [], []
        for n in (1, 2, 3):
            key = bytes(rng.randrange(256) for _ in range(32))
            t = [0, 2 ** 64 - 5, rng.choice([2 ** 32 - 3, rng.randrange(2 ** 64)])][n - 1]      # (2^64 - 5: a lane's number wraps)
            flags, start, end, length = rng.randrange(256), rng.randrange(256), rng.randrange(256), rng.choice([64, 1, 37])
            packed = flags | start << 8 | end << 16 | length << 24 | rng.randrange(2 ** 32) << 32     # (the four bytes above them say nothing)
            lanes = [bytes(rng.randrange(256) for _ in range(64 * n)) for _ in range(count)]
            for k in (None, rng.randrange(count)):                               # (the second: a control, one bit of one lane changed)
                if k is not None: lanes[k] = bytes([lanes[k][0] ^ 1]) + lanes[k][1:]
                env = {"key": key, "t": t, "packed": packed, "n": n}
                env.update({f"lane{i}": lanes[i] for i in range(count)})
                cases.append((lanes_let(count, n, line), env))
                want.append("bytes " + b"".join(self.chunk(key, t, plus(i), flags, start, end, length, [lanes[i][64 * b:64 * b + 64] for b in range(n)])
                                                for i in range(count)).hex())
        got = meaning.account(text, functions, cases)
        self.assertEqual([len(g) for g in got], [len("bytes ") + 64 * count] * len(got))
        self.assertEqual(got, want)
        self.assertEqual(len(set(got)), len(got))

    def test_the_16_way_kernel(self): self.wide(test_p16, test_p16.NAME, 16, lambda i: None)

    def test_the_32_way_kernel(self): self.wide(test_p32, test_p32.NAME, 32, lambda i: None)

    def test_the_32_way_kernel_by_the_entry_the_hash_calls(self): self.wide(test_k32, test_k32.NAME, 32, lambda i: i)

    def test_pad(self):
        import statement
        functions = [(OBJ, test_pad.PAD)]
        (line,) = [l for l in statement.statement(test_pad.spec_text(), functions) if l.startswith("ensures block ")]
        self.assertTrue(line.startswith("ensures block (num 0) (num 64) "), line)
        rng = random.Random(83)
        cases, want = [], []
        for n in (0, 1, 2, 31, 63, 64):
            src = bytes(rng.randrange(1, 256) for _ in range(n))
            cases.append((line[len("ensures block (num 0) (num 64) "):], {"src": src, "n": n}))
            want.append("bytes " + src.ljust(64, b"\0").hex())
        self.assertEqual(meaning.account(test_pad.spec_text(), functions, cases), want)


if __name__ == "__main__":
    unittest.main()
