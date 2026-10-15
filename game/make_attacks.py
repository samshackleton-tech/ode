#!/usr/bin/env pypy3
"""Regenerate every recorded attack under game/attacks/, deterministically.

    pypy3 game/make_attacks.py                  # rewrite all attacks
    pypy3 game/referee.py game/attacks/*        # score them

Each attack is one call below: its NOTES (the idea, and why it should
work), its store, and optionally TARGET (g, or blake3 -- BLAKE3 at the
length Bob asks for, 65 bytes), INPUTS (extra inputs, one per line),
EXPECT (accept: a control that must be accepted and right), and a tamper
step. Numbers retired with the designs they attacked stay unused: 05,
09, 17, 20.
"""
import os
import shutil
import struct
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)

from ode import produce, word  # noqa: E402
from ode.blake3 import blake3  # noqa: E402
from ode.canon import Bytes, Sym, assoc, canonical_bytes, hash_of, parse  # noqa: E402

ATTACKS = os.path.join(HERE, "attacks")
EXAMPLES = os.path.join(ROOT, "examples")
LIB = produce.library_of(EXAMPLES)


def _load(name):
    with open(os.path.join(EXAMPLES, name), "rb") as f:
        return parse(f.read())


G = _load("blake3-g.sexp")
BLAKE3 = _load("blake3.sexp")
COMPRESS = _load("blake3-compress.sexp")
AT65 = {"len": 65, "m": 32}
G_STEPS = ("((t0 (add a b)) (a1 (add t0 x)) (t1 (xor d a1)) (d1 (rotr t1 16)) "
           "(c1 (add c d1)) (t2 (xor b c1)) (b1 (rotr t2 12)) (t3 (add a1 b1)) "
           "(a2 (add t3 y)) (t4 (xor d1 a2)) (d2 (rotr t4 8)) (c2 (add c1 d2)) "
           "(t5 (xor b1 c2)) (b2 (rotr t5 7)))")


def _w32(steps, outputs="(a2 b2 c2 d2)", inputs="(a b c d x y)"):
    return parse(f"(w32 (inputs {inputs}) (steps {steps}) (outputs {outputs}))")


def _blake3_w32(spec=BLAKE3, at=AT65):
    """A W32 program for a spec at an instantiation, callees inlined."""
    return produce.compile_spec(spec, at, resolve=LIB.get)


def _put_binary(d, binary):
    with open(os.path.join(d, blake3(binary).hex() + ".bin"), "wb") as f:
        f.write(binary)


def _cert(spec, binary, prop="w32", at=None, scratch=None):
    fields = [("cert", Sym("correctness")), ("property", Sym(f"equals-spec-{prop}-v1")),
              ("spec", hash_of(spec))]
    if at:
        fields.append(("at", [[Sym(k), v] for k, v in sorted(at.items())]))
    fields.append(("binary-hash", Bytes(blake3(binary))))
    if scratch is not None:
        fields.append(("scratch", scratch))
    return assoc("certificate", *fields)


def attack(name, notes, spec, binary, prop="w32", target=None, inputs=None,
           expect=False, scratch=None, at=None, tamper=None):
    d = os.path.join(ATTACKS, name)
    shutil.rmtree(d, ignore_errors=True)
    os.makedirs(d)
    produce.put_definition(d, spec)
    for h in word.uses_of(spec).values():
        produce.put_definition(d, LIB[h])
    _put_binary(d, binary)
    if at is None and target == "blake3":
        at = AT65
    with open(os.path.join(d, "certificate.sexp"), "wb") as f:
        f.write(canonical_bytes(_cert(spec, binary, prop, at, scratch)))
    files = {"NOTES": notes.strip(), "TARGET": target,
             "INPUTS": inputs and "\n".join(inputs), "EXPECT": expect and "accept"}
    for fname, text in files.items():
        if text:
            with open(os.path.join(d, fname), "w") as f:
                f.write(text + "\n")
    if tamper:
        tamper(d)


def _words(msg):
    return " ".join(map(str, struct.unpack("<32I", msg + b"\0" * (128 - len(msg)))))


def _patch(code, at, value):
    raw = bytearray(code)
    raw[at] = value
    return bytes(raw)


def _mutant_spec(old, new):
    text = canonical_bytes(BLAKE3).decode()
    assert old in text, old
    return parse(text.replace(old, new))


def main():
    shutil.rmtree(ATTACKS, ignore_errors=True)
    g = produce.emit_w32(produce.compile_spec(G))
    mutant_g = produce.emit_w32(_w32(G_STEPS.replace("(rotr t5 7)", "(rotr t5 6)")))
    honest = _blake3_w32()
    h = produce.emit_w32(honest)

    # G, W32.
    attack("00-honest", "Control: an honest build. Bob must accept and be right.",
           G, g, expect=True)
    attack("01-flip-byte", "Flip one byte of the binary file; the certificate "
           "is untouched. Found before the game: the checkers once never opened "
           "the file that runs.", G, g,
           tamper=lambda d: open(os.path.join(d, blake3(g).hex() + ".bin"), "wb")
           .write(_patch(g, 40, g[40] ^ 7)))
    attack("02-mutant-honest-hashes", "A wrong program (b2 rotation 7 -> 6) "
           "with honest hashes. Tests that the checker reasons rather than "
           "merely binds.", G, mutant_g)
    attack("03-fewer-outputs", "A program with only 3 outputs; a pairwise "
           "comparison could ignore the missing fourth.", G,
           produce.emit_w32(_w32(G_STEPS, "(a2 b2 c2)")))

    def plant(d):
        os.makedirs(os.path.join(d, "ode"))
        open(os.path.join(d, "ode", "__init__.py"), "w").close()
        with open(os.path.join(d, "ode", "check.py"), "w") as f:
            f.write("def check_certificate(s, c):\n    return None, None\n")
        with open(os.path.join(d, "sitecustomize.py"), "w") as f:
            f.write("import builtins\nbuiltins.MALLORY = True\n")
    attack("04-shadow-ode-package", "An ode/ package and sitecustomize.py "
           "planted in the store, where Bob runs. Any import through the "
           "store would load the planted checker.", G, g, expect=True, tamper=plant)
    attack("06-huge-inputs", "Out-of-domain inputs (2^32, -1). Found: Bob "
           "printed ACCEPT and then crashed; he now rejects them first.", G, g,
           inputs=["4294967296 0 0 0 0 0", "-1 0 0 0 0 0"], expect=True)
    attack("07-malformed-byte", "One byte of an honest binary changed (once a "
           "rotr count of 39). The decoder must reject malformed bytes or the "
           "proof must catch them.", G, _patch(g, len(g) - 1, 39))
    attack("08-mallory-chosen-inputs", "Mallory's own inputs: 'wrong only "
           "where I say'. The code has no branches, so it cannot be wrong on "
           "one input only.", G, g, expect=True,
           inputs=["305419896 2596069104 4294967295 0 1 2",
                   "0 0 0 0 4294967295 4294967295"])
    fwd = (struct.pack("<H", 6) + struct.pack("<I", 2) + struct.pack("<H", 4)
           + struct.pack("<I", 7) * 4 + bytes([0, 0]) + struct.pack("<I", 7)
           + bytes([0, 0]) + struct.pack("<I", 0))
    attack("10-forward-reference-binary", "Raw W32 bytes with a step copying "
           "a later step. Found: this binary's hex was all digits, which the "
           "old canonical form read as an integer; byte strings are now #hex.",
           G, fwd)

    # BLAKE3 at 65 bytes, against the one general specification.
    attack("11-blake3-honest", "Control: BLAKE3 at 65 bytes, every compression "
           "inlined.", BLAKE3, h, target="blake3", expect=True)
    ren = {Sym(f"m.{i}"): Sym(f"m.{(i + 16) % 32}") for i in range(32)}

    def swap(e):
        if isinstance(e, Sym):
            return ren.get(e, e)
        if isinstance(e, list) and e and e[0] == "rotr":
            return [e[0], swap(e[1]), e[2]]
        return [swap(x) for x in e] if isinstance(e, list) else e

    def program(steps, outputs=None):
        return assoc("w32", ("inputs", word.inputs_of(honest)), ("steps", steps),
                     ("outputs", outputs or word.outputs_of(honest)))
    attack("12-blake3-swap-blocks", "The two 64-byte blocks swapped "
           "(m.i <-> m.i+16). Symbolically m.0 and m.16 differ.", BLAKE3,
           produce.emit_w32(program([[n, swap(e)] for n, e in word.steps_of(honest)])),
           target="blake3")
    attack("13-blake3-drop-chain", "A chunk's next block starts from the IV "
           "instead of the chaining value: compiled honestly from a mutant "
           "spec, certified against the true one.", BLAKE3,
           produce.emit_w32(_blake3_w32(_mutant_spec(
               "(chain c start blocks (n+ b 1) (cv node))",
               "(chain c start blocks (n+ b 1) (iv))"))), target="blake3")
    attack("14-blake3-truncate", "Every chunk stops after its first block: "
           "the hash ignores the 65th byte.", BLAKE3,
           produce.emit_w32(_blake3_w32(_mutant_spec(
               "(if (n= b (n- blocks 1)) node", "(if (n= b 0) node"))),
           target="blake3")
    steps = [list(s) for s in word.steps_of(honest)]
    k = next(j for j, (_, e) in enumerate(steps) if isinstance(e, list) and e[0] == "add")
    steps[k][1] = [steps[k][1][0], steps[k][1][2], steps[k][1][1]]
    attack("15-blake3-commuted-add", "An honest program with one add commuted: "
           "correct, differently written. The checker must accept.", BLAKE3,
           produce.emit_w32(program(steps)), target="blake3", expect=True)
    attack("16-blake3-chosen-messages", "Mallory's messages, including two equal "
           "blocks, where a swap would be invisible.", BLAKE3, h, target="blake3",
           expect=True, inputs=[_words(b"\0" * 65), _words(b"A" * 64 + b"\0"),
                                _words(bytes(range(64)) + b"\0")])
    raw = bytearray(h)
    for j in range(8):
        struct.pack_into("<I", raw, 8 + 4 * j, j)
    attack("18-blake3-outputs-are-inputs", "Raw bytes whose outputs index the "
           "inputs m.0..m.7: hash := message prefix.", BLAKE3, bytes(raw),
           target="blake3")
    attack("19-blake3-other-length", "An honest certificate for BLAKE3 at 3 "
           "bytes, offered when Bob asks for 65: a proof at one length says "
           "nothing about another.", BLAKE3,
           produce.emit_w32(_blake3_w32(at={"len": 3, "m": 16})), target="blake3",
           at={"len": 3, "m": 16})
    attack("37-blake3-unpadded-count", "An instantiation the spec refuses: "
           "65 bytes in 16 words. The spec's own requirement must reject it.",
           BLAKE3, produce.emit_w32(_blake3_w32(at={"len": 3, "m": 16})),
           target="blake3", at={"len": 65, "m": 16})

    # The root, a delivered ode-base, a delivered spec.
    def deliver_ode_base(d, edit):
        shutil.copytree(os.path.join(HERE, "ode-base"), os.path.join(d, "ode-base"),
                        ignore=shutil.ignore_patterns("__pycache__"))
        edit(os.path.join(d, "ode-base"))
    attack("21-forged-ode-base", "Mallory delivers an ode-base whose checker "
           "accepts everything, beside a wrong program.", G, mutant_g,
           tamper=lambda d: deliver_ode_base(d, lambda b: open(
               os.path.join(b, "ode", "check.py"), "a").write(
                   "\ndef check_certificate(s, c):\n    return None, None\n")))
    attack("22-ode-base-extra-file", "A genuine ode-base plus one added file; "
           "any change to the tree changes its hash.", G, mutant_g,
           tamper=lambda d: deliver_ode_base(d, lambda b: open(
               os.path.join(b, "ode", "sitecustomize.py"), "w").write("pass\n")))
    attack("23-noncanonical-spec-file", "The delivered spec with a trailing "
           "newline: non-canonical bytes are rejected even when they parse to "
           "the pinned spec.", G, g, tamper=lambda d: open(
               os.path.join(d, hash_of(G).hex() + ".sexp"), "ab").write(b"\n"))
    attack("24-spec-missing", "The spec withheld: Mallory can deny "
           "availability, never correctness.", G, g,
           tamper=lambda d: os.remove(os.path.join(d, hash_of(G).hex() + ".sexp")))

    # Real AArch64, run natively.
    ga, gs = produce.emit_a64(produce.compile_spec(G))
    ha, hs = produce.emit_a64(honest)
    words_ = [int.from_bytes(ga[j:j + 4], "little") for j in range(0, len(ga), 4)]
    enc = lambda ws: b"".join(w.to_bytes(4, "little") for w in ws)  # noqa: E731
    ror = next(j for j, w in enumerate(words_) if (w & 0xFFE00000) == 0x13800000)
    attack("25-a64-g-honest", "Control: G as proved AArch64, run natively.",
           G, ga, prop="a64", scratch=gs, expect=True)
    attack("26-a64-blake3-honest", "Control: BLAKE3 at 65 bytes as proved "
           "AArch64, run natively.", BLAKE3, ha, prop="a64", scratch=hs,
           target="blake3", expect=True)
    attack("27-a64-rotation-off-by-one", "One ROR count off by one in real "
           "code; honest hashes.", G,
           enc(words_[:ror] + [words_[ror] ^ (1 << 10)] + words_[ror + 1:]),
           prop="a64", scratch=gs)
    attack("28-a64-branch", "A branch spliced in: anything outside the eight "
           "modelled forms is rejected, since a jump could reach code the "
           "proof never saw.", G, enc([0x14000002] + words_), prop="a64", scratch=gs)
    attack("29-a64-scratch-too-small", "Honest code that spills, scratch "
           "declared one word short: Bob would allocate too little.", BLAKE3,
           ha, prop="a64", scratch=hs - 1, target="blake3")
    attack("30-a64-store-past-out", "An extra store far past out[]: memory "
           "safety of the bytes that run.", G,
           enc(words_[:-1] + [0xB9000000 | (4095 << 10) | (1 << 5) | 9, words_[-1]]),
           prop="a64", scratch=gs)

    # Calls by certificate: BLAKE3 as glue over a certified compression.
    chash = hash_of(COMPRESS)

    def composed(name, notes, callee_binary=None, callee_spec=None,
                 rewrite=None, expect=False, drop_callee=False, isa="w32"):
        def build(d):
            cs = callee_spec or COMPRESS
            if isa == "a64":
                cb, scr = produce.emit_a64(produce.compile_spec(cs))
            else:
                cb, scr = callee_binary or produce.emit_w32(produce.compile_spec(cs)), None
            _put_binary(d, cb)
            produce.put_definition(d, cs)
            ch = produce.put_definition(d, _cert(cs, cb, isa, scratch=scr))
            glue = produce.compile_spec(BLAKE3, AT65, {chash: (ch, 16)}, LIB.get)
            gb = produce.emit_w32(rewrite(glue) if rewrite else glue)
            _put_binary(d, gb)
            with open(os.path.join(d, "certificate.sexp"), "wb") as f:
                f.write(canonical_bytes(_cert(BLAKE3, gb, at=AT65)))
            if drop_callee:
                os.remove(os.path.join(d, ch.hex() + ".sexp"))
        attack(name, notes, BLAKE3, h, target="blake3", expect=expect, tamper=build)

    composed("31-call-honest", "Control: BLAKE3 as glue calling the compression "
             "by its certificate; the compression is proved once, and every call "
             "is one opaque function.", expect=True)
    composed("32-call-mutant-callee", "The callee certificate claims the "
             "compression spec for a wrong compression (one rotation off). "
             "Checking the callee must catch it.",
             callee_binary=produce.emit_w32(produce.compile_spec(parse(
                 canonical_bytes(COMPRESS).decode().replace(
                     "(r0c0_d (rotr (xor counter-lo r0c0_a) 16))",
                     "(r0c0_d (rotr (xor counter-lo r0c0_a) 15))")))))
    other = parse(canonical_bytes(COMPRESS).decode().replace(
        "(name blake3-compress)", "(name blake3-compress-but-different)").replace(
        "(r6d3_B (rotr (xor r6d3_b r6d3_C) 7))", "(r6d3_B (rotr (xor r6d3_b r6d3_C) 6))"))
    composed("33-call-other-spec", "The call names an honest certificate for a "
             "*different* spec of the same shape. Its opaque node is a different "
             "function, so it must not stand for the compression.",
             callee_spec=other)

    def swap_args(glue):
        steps = [list(s) for s in word.steps_of(glue)]
        for s in steps:
            if isinstance(s[0], list):
                s[1] = s[1][:2] + [s[1][3], s[1][2]] + s[1][4:]
                break
        return assoc("w32", ("inputs", word.inputs_of(glue)), ("steps", steps),
                     ("outputs", word.outputs_of(glue)))
    composed("34-call-swapped-args", "Two arguments of the first call swapped. "
             "Congruence holds only for equal arguments.", rewrite=swap_args)
    composed("35-call-callee-missing", "The callee's certificate withheld: "
             "availability lost, correctness kept.", drop_callee=True)
    composed("36-call-a64-callee", "Control: W32 glue calling the compression's "
             "proved AArch64 certificate; Bob runs the glue interpreted and each "
             "compression natively.", isa="a64", expect=True)
    # Every length at once: the spec itself, its callee bound to proved code.
    def bound(name, notes, mutate=None, isa="a64", expect=False):
        def build(d):
            for f in os.listdir(d):
                if f.endswith((".sexp", ".bin")):
                    os.remove(os.path.join(d, f))
            produce.bind(BLAKE3, d, isa, LIB)
            if mutate:
                path = os.path.join(d, "certificate.sexp")
                with open(path, "rb") as f:
                    cert = parse(f.read())
                with open(path, "wb") as f:
                    f.write(canonical_bytes(mutate(d, cert)))
        attack(name, notes, BLAKE3, h, target="blake3", expect=expect, tamper=build)

    def callees(cert, pairs):
        return [cert[0]] + [p if p[0] != "callees" else [p[0], pairs] for p in cert[1:]]

    bound("38-every-length-honest", "Control: one certificate for every length "
          "-- the BLAKE3 spec itself, its compression bound to proved AArch64. "
          "Bob asks for 65 bytes; nothing in the store mentions 65.", expect=True)

    def mutant_callee(d, cert):
        bad = parse(canonical_bytes(COMPRESS).decode().replace(
            "(r0c0_d (rotr (xor counter-lo r0c0_a) 16))",
            "(r0c0_d (rotr (xor counter-lo r0c0_a) 15))"))
        code = produce.emit_w32(produce.compile_spec(bad))
        _put_binary(d, code)
        lie = produce.put_definition(d, _cert(COMPRESS, code))
        return callees(cert, [[chash, lie]])
    bound("39-every-length-mutant-callee", "The compression bound to a "
          "certificate that claims the compression for wrong code.", mutant_callee)

    def g_callee(d, cert):
        gcert = produce.put_definition(d, _cert(G, g))
        _put_binary(d, g)
        produce.put_definition(d, G)
        return callees(cert, [[chash, gcert]])
    bound("40-every-length-other-spec", "The compression bound to an honest "
          "certificate for a different spec (G).", g_callee)
    bound("41-every-length-unbound", "No callee bound: the spec would have "
          "to be expanded by Bob -- or trusted to the store.",
          lambda d, cert: callees(cert, []))

    def lie_about_spec(d, cert):
        other = parse(canonical_bytes(BLAKE3).decode().replace(
            "(add (at root 27) 8)", "(add (at root 27) 0)"))
        produce.put_definition(d, other)
        return [cert[0]] + [p if p[0] != "spec" else [p[0], hash_of(other)]
                            for p in cert[1:]]
    bound("42-every-length-other-spec-bound", "An honest binding certificate "
          "for a mutant BLAKE3 (no ROOT flag). Bob's pin must reject it.",
          lie_about_spec)
    print(f"{len(os.listdir(ATTACKS))} attacks regenerated")


if __name__ == "__main__":
    main()
