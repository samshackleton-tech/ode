"""BLAKE3 in Ode: the specifications against the reference, and the
checker proving W32 bytes against them -- and rejecting what it must."""
import os
import random
import struct
import sys
import tempfile
import unittest

ROOT = os.path.join(os.path.dirname(__file__), "..")
sys.path.insert(0, ROOT)

from ode import check, produce, word  # noqa: E402
from ode.blake3 import _compress, _g, blake3  # noqa: E402
from ode.canon import Bytes, Sym, assoc, canonical_bytes, field, hash_of, parse  # noqa: E402
from ode.cli import _check, check_store  # noqa: E402
from ode.store import Reject  # noqa: E402

LIB = produce.library_of(os.path.join(ROOT, "examples"))


def load(name):
    with open(os.path.join(ROOT, "examples", name), "rb") as f:
        return parse(f.read())


BLAKE3 = load("blake3.sexp")


def at_len(L):
    return {"len": L, "m": 16 * max(1, -(-L // 64))}


def words(msg, n):
    return list(struct.unpack(f"<{n}I", msg + b"\0" * (4 * n - len(msg))))


def digest(msg):
    return list(struct.unpack("<8I", blake3(msg)))


def certify(spec, binary, at=None):
    """A store holding spec, its callees, a binary, and a certificate."""
    tmp = tempfile.mkdtemp()
    for h in word.uses_of(spec).values():
        produce.put_definition(tmp, LIB[h])
    with open(os.path.join(tmp, blake3(binary).hex() + ".bin"), "wb") as f:
        f.write(binary)
    extra = (("at", [[Sym(k), v] for k, v in sorted(at.items())]),) if at else ()
    cert = assoc("certificate", ("cert", Sym("correctness")),
                 ("property", Sym("equals-spec-w32-v1")),
                 ("spec", produce.put_definition(tmp, spec)), *extra,
                 ("binary-hash", Bytes(blake3(binary))))
    return tmp, cert


class SpecsMatchReferenceTest(unittest.TestCase):
    def test_g(self):
        spec, rng = load("blake3-g.sexp"), random.Random(1)
        for _ in range(200):
            v = [rng.getrandbits(32) for _ in range(16)]
            x, y = rng.getrandbits(32), rng.getrandbits(32)
            ins = [v[0], v[4], v[8], v[12], x, y]
            _g(v, 0, 4, 8, 12, x, y)
            self.assertEqual(word.run(spec, {}, ins), [v[0], v[4], v[8], v[12]])

    def test_compress(self):
        spec, rng = load("blake3-compress.sexp"), random.Random(42)
        for _ in range(20):
            cv = [rng.getrandbits(32) for _ in range(8)]
            block = bytes(rng.getrandbits(8) for _ in range(64))
            counter, blen, flags = rng.getrandbits(40), rng.randrange(65), rng.randrange(16)
            ins = cv + words(block, 16) + [counter & 0xFFFFFFFF, counter >> 32, blen, flags]
            self.assertEqual(word.run(spec, {}, ins),
                             _compress(cv, block, counter, blen, flags))

    def test_blake3_at_every_kind_of_length(self):
        # Empty, partial and whole blocks, chunk boundaries, multi-level
        # trees, an odd chunk carried up.
        for L in (0, 1, 3, 63, 64, 65, 1023, 1024, 1025, 2048, 2049, 3072, 5000, 8193):
            msg = bytes((i * 31 + 7) & 0xFF for i in range(L))
            at = at_len(L)
            self.assertEqual(word.run(BLAKE3, at, words(msg, at["m"]), LIB.get),
                             digest(msg), L)

    def test_blake3_requires_the_padded_word_count(self):
        with self.assertRaises(ValueError):
            word.run(BLAKE3, {"len": 3, "m": 32}, [0] * 32, LIB.get)


class CheckerTest(unittest.TestCase):
    def test_proves_g_compress_and_blake3(self):
        for spec, at in ((load("blake3-g.sexp"), None),
                         (load("blake3-compress.sexp"), None),
                         (BLAKE3, at_len(65))):
            tmp = tempfile.mkdtemp()
            produce.build(spec, tmp, "w32", at, LIB)
            self.assertEqual(field(check_store(tmp), "verdict"), "accept")

    def test_rejects_mutant_rotation(self):
        spec = load("blake3-g.sexp")
        text = canonical_bytes(spec).decode().replace("(d1 (rotr (xor d a1) 16))",
                                                      "(d1 (rotr (xor d a1) 15))")
        tmp, cert = certify(spec, produce.emit_w32(produce.compile_spec(parse(text))))
        with self.assertRaises(Reject) as cm:
            check.check_certificate(tmp, cert)
        self.assertIn("differs", str(cm.exception))

    def test_rejects_dropped_root_flag_and_wrong_length(self):
        text = canonical_bytes(BLAKE3).decode()
        mutant = text.replace("(add (at root 27) 8)", "(add (at root 27) 0)")
        self.assertNotEqual(text, mutant)
        at = at_len(65)
        for program, cert_at in (
                (produce.compile_spec(parse(mutant), at, resolve=LIB.get), at),
                (produce.compile_spec(BLAKE3, at_len(64), resolve=LIB.get), at)):
            tmp, cert = certify(BLAKE3, produce.emit_w32(program), cert_at)
            with self.assertRaises(Reject):
                check.check_certificate(tmp, cert)

    def test_rejects_an_instantiation_the_spec_refuses(self):
        tmp, cert = certify(BLAKE3, produce.emit_w32(
            produce.compile_spec(BLAKE3, at_len(3), resolve=LIB.get)),
            {"len": 3, "m": 32})
        with self.assertRaises(Reject):
            check.check_certificate(tmp, cert)

    def test_rejects_tampered_binary_file(self):
        tmp = tempfile.mkdtemp()
        result = produce.build(load("blake3-g.sexp"), tmp)
        path = os.path.join(tmp, result["binary_hash"] + ".bin")
        with open(path, "rb") as stream:
            raw = bytearray(stream.read())
        raw[20] ^= 1
        with open(path, "wb") as stream:
            stream.write(bytes(raw))
        with self.assertRaises(Reject) as cm:
            check_store(tmp)
        self.assertIn("binary file", str(cm.exception))

    def test_rejects_spec_file_under_a_false_name(self):
        tmp = tempfile.mkdtemp()
        result = produce.build(load("blake3-g.sexp"), tmp)
        evil = parse("(spec (name g) (inputs (a b c d x y)) (steps ()) (outputs (a b c d)))")
        with open(os.path.join(tmp, result["spec"] + ".sexp"), "wb") as stream:
            stream.write(canonical_bytes(evil))
        with self.assertRaises(Reject):
            check_store(tmp)


class CallsByCertificateTest(unittest.TestCase):
    """A proved callee is checked once and is one opaque function after."""

    def test_composed_blake3_is_small_to_check_and_right(self):
        tmp, at = tempfile.mkdtemp(), at_len(3072)
        produce.build(BLAKE3, tmp, "w32", at, LIB)
        record, program = _check(tmp)
        self.assertLess(field(record, "dag-nodes"), 2000)  # 50 calls, not 50 bodies
        msg = bytes((i * 7 + 1) & 0xFF for i in range(3072))
        self.assertEqual(check.run(program, words(msg, at["m"])), digest(msg))

    def test_inlined_and_composed_both_prove(self):
        at = at_len(65)
        inlined = produce.compile_spec(BLAKE3, at, resolve=LIB.get)
        tmp, cert = certify(BLAKE3, produce.emit_w32(inlined), at)
        record, _ = check.check_certificate(tmp, cert)  # no calls: expanded
        self.assertGreater(field(record, "dag-nodes"), 5000)
        tmp = tempfile.mkdtemp()
        produce.build(BLAKE3, tmp, "w32", at, LIB)  # calls by certificate
        self.assertLess(field(check_store(tmp), "dag-nodes"), 200)


class NamesTest(unittest.TestCase):
    """Names in a spec never collide with names the tools mint."""

    def test_spec_names_like_minted_ones(self):
        callee = parse("(spec (name inner) (inputs (a b)) "
                       "(steps ((t0 (add a b)) (t1 (xor t0 a)))) (outputs (t1 t0)))")
        ch = hash_of(callee)
        caller = parse(f"(spec (name outer) (inputs (t0 a)) (uses ((inner #{ch.hex()}))) "
                       f"(steps (((u v) (inner a t0)) (t1 (add u v)) "
                       f"((w z) (inner t1 t0)))) (outputs (w z t1)))")
        lib = {ch: callee}
        program, rng = produce.compile_spec(caller, resolve=lib.get), random.Random(9)
        for _ in range(100):
            v = [rng.getrandbits(32), rng.getrandbits(32)]
            self.assertEqual(word.run(caller, {}, v, lib.get), word.run(program, {}, v))
        tmp = tempfile.mkdtemp()
        produce.build(caller, tmp, "w32", None, lib)
        self.assertEqual(field(check_store(tmp), "verdict"), "accept")

    def test_decoder_names_cannot_collide_with_inputs(self):
        spec = parse("(spec (name s) (inputs (s0 s1)) (steps ((r (add s0 s1)))) (outputs (r)))")
        tmp = tempfile.mkdtemp()
        produce.build(spec, tmp)
        self.assertEqual(field(check_store(tmp), "verdict"), "accept")


if __name__ == "__main__":
    unittest.main()


class EveryLengthTest(unittest.TestCase):
    """One certificate for every length: the spec, its callee bound."""

    def test_bound_spec_hashes_every_length(self):
        for isa in ("w32", "a64") if os.uname().machine == "aarch64" else ("w32",):
            tmp = tempfile.mkdtemp()
            produce.bind(BLAKE3, tmp, isa, LIB)
            record, program = _check(tmp)
            self.assertEqual(field(record, "domain"), "every-instantiation")
            for L in (0, 1, 65, 1025, 3072):
                msg = bytes((i * 11 + 3) & 0xFF for i in range(L))
                n = 16 * max(1, -(-L // 64))
                self.assertEqual(check.run(program, words(msg, n), {"len": L}),
                                 digest(msg), (isa, L))

    def bound_store(self, mutate):
        tmp = tempfile.mkdtemp()
        produce.bind(BLAKE3, tmp, "w32", LIB)
        with open(os.path.join(tmp, "certificate.sexp"), "rb") as f:
            cert = parse(f.read())
        return tmp, mutate(tmp, cert)

    def test_rejects_bad_bindings(self):
        chash = list(word.uses_of(BLAKE3).values())[0]
        g = load("blake3-g.sexp")

        def with_callees(cert, pairs):
            return [cert[0]] + [p if p[0] != "callees" else [p[0], pairs] for p in cert[1:]]

        def other_spec(tmp, cert):  # an honest certificate for another spec
            gcert, _ = produce._certify(g, tmp, "w32", {}, None)
            return with_callees(cert, [[chash, gcert]])

        def missing(tmp, cert):
            return with_callees(cert, [])

        def extra(tmp, cert):
            pair = cert[[p[0] for p in cert].index("callees")][1][0]
            return with_callees(cert, [pair, [hash_of(g), pair[1]]])

        def nested(tmp, cert):  # bind the callee to a binding, not to code
            inner = assoc("certificate", ("cert", Sym("correctness")),
                          ("property", Sym("spec-with-callees-v1")),
                          ("spec", produce.put_definition(tmp, LIB[chash])),
                          ("callees", []))
            return with_callees(cert, [[chash, produce.put_definition(tmp, inner)]])

        for mutate in (other_spec, missing, extra, nested):
            tmp, cert = self.bound_store(mutate)
            with self.assertRaises(Reject, msg=mutate.__name__):
                check.check_certificate(tmp, cert)
