#!/usr/bin/env pypy3
"""Regenerate every recorded attack under game/attacks/, deterministically.

    pypy3 game/make_attacks.py                  # rewrite all attacks
    pypy3 game/referee.py game/attacks/*        # score them

Each attack is one call below: its NOTES (the idea, and why it should
work), its store, and optionally TARGET (g or hash65), INPUTS (extra
inputs, one per line), EXPECT (accept: a control that must be accepted
and right), and a tamper step. Numbers retired with the designs they
attacked stay unused: 05, 09, 17, 20.
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


def _load(name):
    with open(os.path.join(ROOT, "examples", name), "rb") as f:
        return parse(f.read())


G = _load("blake3-g.sexp")
HASH65 = _load("blake3-hash-65.sexp")


def _w32(text):
    """A W32 program over G's inputs, from its steps."""
    return parse(f"(w32 (inputs (a b c d x y)) (steps {text}) (outputs (a2 b2 c2 d2)))")


G_STEPS = ("((t0 (add a b)) (a1 (add t0 x)) (t1 (xor d a1)) (d1 (rotr t1 16)) "
           "(c1 (add c d1)) (t2 (xor b c1)) (b1 (rotr t2 12)) (t3 (add a1 b1)) "
           "(a2 (add t3 y)) (t4 (xor d1 a2)) (d2 (rotr t4 8)) (c2 (add c1 d2)) "
           "(t5 (xor b1 c2)) (b2 (rotr t5 7)))")


def attack(name, notes, spec, binary, prop="w32", target=None, inputs=None,
           expect=False, scratch=None, tamper=None):
    d = os.path.join(ATTACKS, name)
    shutil.rmtree(d, ignore_errors=True)
    os.makedirs(d)
    produce.put_definition(d, spec)
    with open(os.path.join(d, "binary.bin"), "wb") as f:
        f.write(binary)
    extra = (("scratch", scratch),) if scratch is not None else ()
    cert = assoc("certificate", ("cert", Sym("correctness")),
                 ("property", Sym(f"equals-spec-{prop}-v1")),
                 ("spec", hash_of(spec)),
                 ("binary-hash", Bytes(blake3(binary))), *extra)
    with open(os.path.join(d, "certificate.sexp"), "wb") as f:
        f.write(canonical_bytes(cert))
    files = {"NOTES": notes.strip(), "TARGET": target,
             "INPUTS": inputs and "\n".join(inputs),
             "EXPECT": expect and "accept"}
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


def main():
    shutil.rmtree(ATTACKS, ignore_errors=True)
    g = produce.emit_w32(produce.compile_spec(G))
    h = produce.emit_w32(produce.compile_spec(HASH65))
    mutant_g = produce.emit_w32(_w32(G_STEPS.replace("(rotr t5 7)", "(rotr t5 6)")))

    # Round 1: G, W32.
    attack("00-honest", "Control: an honest build. Bob must accept and be right.",
           G, g, expect=True)
    attack("01-flip-byte", "Flip one byte of binary.bin; the certificate is "
           "untouched. Found before the game: the checkers once never opened "
           "binary.bin.", G, g,
           tamper=lambda d: open(os.path.join(d, "binary.bin"), "wb").write(
               _patch(g, 40, g[40] ^ 7)))
    attack("02-mutant-honest-hashes", "A wrong program (b2 rotation 7 -> 6) "
           "with honest hashes. Tests that the checker reasons rather than "
           "merely binds.", G, mutant_g)
    attack("03-fewer-outputs", "A program with only 3 outputs; a pairwise "
           "comparison could ignore the missing fourth.", G,
           produce.emit_w32(parse(f"(w32 (inputs (a b c d x y)) (steps {G_STEPS}) "
                                  "(outputs (a2 b2 c2)))")))

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

    # Round 2: the 65-byte hash.
    attack("11-hash65-honest", "Control: an honest hash65 build.", HASH65, h,
           target="hash65", expect=True)
    text = canonical_bytes(HASH65).decode()
    honest65 = produce.compile_spec(HASH65)

    def program(steps, outputs=None):
        return assoc("w32", ("inputs", word.inputs_of(honest65)), ("steps", steps),
                     ("outputs", outputs or word.outputs_of(honest65)))
    ren = {Sym(f"m{i}"): Sym(f"m{(i + 16) % 32}") for i in range(32)}

    def swap(e):
        if isinstance(e, Sym):
            return ren.get(e, e)
        if isinstance(e, list) and e[0] == "rotr":
            return [e[0], swap(e[1]), e[2]]
        return [swap(x) for x in e] if isinstance(e, list) else e
    swapped = program([[n, swap(e)] for n, e in word.steps_of(honest65)])
    attack("12-hash65-swap-blocks", "The two 64-byte blocks swapped "
           "(m_i -> m_{i+16 mod 32}). Symbolically m0 and m16 differ.",
           HASH65, produce.emit_w32(swapped), target="hash65")
    first_cv = " ".join(f"c0b0_{i}" for i in range(8))
    iv = " ".join(str(v) for v in (0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
                                   0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19))
    i = text.index(first_cv, text.index("(call"))  # the second call's cv
    dropped = text[:i] + iv + text[i + len(first_cv):]
    attack("13-hash65-drop-chain", "The second compression starts from the "
           "IV, not block 0's chaining value; compiled honestly from a mutant "
           "spec, certified against the true one.", HASH65,
           produce.emit_w32(produce.compile_spec(parse(dropped))), target="hash65")
    trunc = program(word.steps_of(honest65), [Sym(f"c0b0_{j}") for j in range(8)])
    attack("14-hash65-truncate", "Return block 0's chaining value as the "
           "hash, ignoring block 1 and the 65th byte.", HASH65,
           produce.emit_w32(trunc), target="hash65")
    steps = [list(s) for s in word.steps_of(honest65)]
    k = next(j for j, (_, e) in enumerate(steps)
             if isinstance(e, list) and e[0] == "add")
    steps[k][1] = [steps[k][1][0], steps[k][1][2], steps[k][1][1]]
    attack("15-hash65-commuted-add", "An honest program with one add "
           "commuted: correct, differently written. The checker must accept.",
           HASH65, produce.emit_w32(program(steps)),
           target="hash65", expect=True)
    attack("16-hash65-chosen-messages", "Mallory's messages, including two "
           "equal blocks, where a swap would be invisible.", HASH65, h,
           target="hash65", expect=True,
           inputs=[_words(b"\0" * 65), _words(b"A" * 64 + b"\0"),
                   _words(bytes(range(64)) + b"\0")])
    raw = bytearray(h)
    for j in range(8):
        struct.pack_into("<I", raw, 8 + 4 * j, j)
    attack("18-hash65-outputs-are-inputs", "Raw bytes whose outputs index the "
           "inputs m0..m7: hash := message prefix.", HASH65, bytes(raw),
           target="hash65")
    attack("19-hash65-wrong-length-program", "The proved 3-byte hash program "
           "certified against the hash65 spec: length confusion.", HASH65,
           produce.emit_w32(produce.compile_spec(_load("blake3-hash-3.sexp"))),
           target="hash65")

    # Round 3: the root, a delivered ode-base, a delivered spec.
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

    # Round 5: real AArch64, run natively.
    ga, gs = produce.emit_a64(produce.compile_spec(G))
    ha, hs = produce.emit_a64(produce.compile_spec(HASH65))
    words = [int.from_bytes(ga[j:j + 4], "little") for j in range(0, len(ga), 4)]
    enc = lambda ws: b"".join(w.to_bytes(4, "little") for w in ws)  # noqa: E731
    ror = next(j for j, w in enumerate(words) if (w & 0xFFE00000) == 0x13800000)
    attack("25-a64-g-honest", "Control: G as proved AArch64, run natively.",
           G, ga, prop="a64", scratch=gs, expect=True)
    attack("26-a64-hash65-honest", "Control: the 65-byte hash as proved "
           "AArch64, run natively.", HASH65, ha, prop="a64", scratch=hs,
           target="hash65", expect=True)
    attack("27-a64-rotation-off-by-one", "One ROR count off by one in real "
           "code; honest hashes.", G,
           enc(words[:ror] + [words[ror] ^ (1 << 10)] + words[ror + 1:]),
           prop="a64", scratch=gs)
    attack("28-a64-branch", "A branch spliced in: anything outside the eight "
           "modelled forms is rejected, since a jump could reach code the "
           "proof never saw.", G, enc([0x14000002] + words), prop="a64", scratch=gs)
    attack("29-a64-scratch-too-small", "Honest code, scratch declared one word "
           "short: Bob would allocate too little.", G, ga, prop="a64",
           scratch=gs - 1)
    attack("30-a64-store-past-out", "An extra store far past out[]: memory "
           "safety of the bytes that run.", G,
           enc(words[:-1] + [0xB9000000 | (4095 << 10) | (1 << 5) | 9, words[-1]]),
           prop="a64", scratch=gs)
    print(f"{len(os.listdir(ATTACKS))} attacks regenerated")


if __name__ == "__main__":
    main()
