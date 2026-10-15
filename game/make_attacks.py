#!/usr/bin/env pypy3
"""Regenerate every recorded attack under game/attacks/, deterministically.

    pypy3 game/make_attacks.py                  # rewrite attacks in place
    pypy3 game/referee.py game/attacks/*        # score them

Each attack is one function below: its idea (NOTES), its store, and any
TARGET/INPUTS. The recorded Mallory corpus is therefore data produced by
this program, not a pile of hand-made directories: change an attack, or
add one, here, regenerate, and scores change once. Proving a negative
("Bob rejected it") forever is tests/test_game.py replaying referee over
the directories this script writes.
"""
import os
import struct
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)

from ode import word, wproducer  # noqa: E402
from ode.blake3 import blake3  # noqa: E402
from ode.canon import (Bytes, Sym, assoc, canonical_bytes, hash_of,  # noqa: E402
                       parse)
from ode.producer import put_definition  # noqa: E402

EXAMPLES = os.path.join(ROOT, "examples")


def _load(name):
    with open(os.path.join(EXAMPLES, name), "rb") as f:
        return parse(f.read())


G = _load("blake3-g.sexp")
G_HASH = hash_of(G)
HASH65 = _load("blake3-hash-65.sexp")
HASH65_HASH = hash_of(HASH65)
G_STEPS = ('((t0 (add a b)) (a1 (add t0 x)) (t1 (xor d a1)) '
           '(d1 (rotr t1 16)) (c1 (add c d1)) (t2 (xor b c1)) '
           '(b1 (rotr t2 12)) (t3 (add a1 b1)) (a2 (add t3 y)) '
           '(t4 (xor d1 a2)) (d2 (rotr t4 8)) (c2 (add c1 d2)) '
           '(t5 (xor b1 c2)) (b2 (rotr t5 7)))')


def _mach(steps_text, outputs='(a2 b2 c2 d2)'):
    return parse(f'(wmachine (isa W32) (inputs (a b c d x y)) '
                 f'(steps {steps_text}) (outputs {outputs}))')


def _forge(name, notes, spec, machine_defn, target=None, binary=None,
           inputs_lines=None, tamper=None):
    d = os.path.join(HERE, "attacks", name)
    os.makedirs(d, exist_ok=True)
    for f in os.listdir(d):
        if f not in ("NOTES", "TARGET", "INPUTS") and not f.startswith("."):
            path = os.path.join(d, f)
            if os.path.isfile(path):
                os.remove(path)
            elif os.path.isdir(path):
                import shutil
                shutil.rmtree(path)
    put_definition(d, spec)
    mh = put_definition(d, machine_defn)
    if binary is None:
        binary = wproducer.emit_w32(machine_defn)
    with open(os.path.join(d, "binary.bin"), "wb") as f:
        f.write(binary)
    cert = assoc("certificate", ("cert", Sym("correctness")),
                 ("property", Sym("equals-wspec-v1")),
                 ("spec", hash_of(spec)),
                 ("binary-hash", Bytes(blake3(binary))),
                 )
    put_definition(d, cert)
    with open(os.path.join(d, "certificate.sexp"), "wb") as f:
        f.write(canonical_bytes(cert))
    with open(os.path.join(d, "NOTES"), "w") as f:
        f.write(notes.strip() + "\n")
    tpath = os.path.join(d, "TARGET")
    if target:
        with open(tpath, "w") as f:
            f.write(target + "\n")
    elif os.path.exists(tpath):
        os.remove(tpath)
    ipath = os.path.join(d, "INPUTS")
    if inputs_lines:
        with open(ipath, "w") as f:
            f.write("\n".join(inputs_lines) + "\n")
    elif os.path.exists(ipath):
        os.remove(ipath)
    epath = os.path.join(d, "EXPECT")
    if notes.startswith("Control"):
        with open(epath, "w") as f:
            f.write("accept\n")
    elif os.path.exists(epath):
        os.remove(epath)
    if tamper:
        tamper(d, machine_defn)
    return d


def _words(msg):
    return " ".join(str(w) for w in
                    struct.unpack("<32I", msg + b"\0" * (128 - len(msg))))


def attacks():
    honest_g = wproducer.compile_wspec(G)
    forge = []
    add = forge.append

    add(("00-honest", G, honest_g, {},
         "Control: an honest build. Bob must accept and be right."))
    d = ("01-flip-byte", G, honest_g, {},
         "Flip one byte of binary.bin; certificate untouched. The first finding "
         "of the pre-game review: the checkers once never opened binary.bin.")
    add(d)

    add(("02-mutant-honest-hashes", G,
         _mach(G_STEPS.replace("(rotr t5 7)", "(rotr t5 6)")), {},
         "Honest hashes for a wrong machine (b2 rotation 7->6). Tests whether "
         "the checker reasons rather than merely binds."))
    add(("03-fewer-outputs", G, _mach(G_STEPS, outputs="(a2 b2 c2)"), {},
         "Machine declares only 3 outputs; a pairwise zip comparison could "
         "ignore the missing fourth, and Bob would print 3 words."))

    def plant(dirn, _):
        os.makedirs(os.path.join(dirn, "ode"), exist_ok=True)
        with open(os.path.join(dirn, "ode", "__init__.py"), "w") as f:
            f.write("")
        with open(os.path.join(dirn, "ode", "wcheck.py"), "w") as f:
            f.write('PROPERTY="equals-wspec-v1"\n'
                    "def check_certificate(s,c):\n"
                    "    from .canon import assoc, Sym\n"
                    '    return assoc("record",("verdict",Sym("accept")))\n')
        with open(os.path.join(dirn, "sitecustomize.py"), "w") as f:
            f.write("import builtins\nbuiltins.MALLORY=True\n")
    add(("04-shadow-ode-package", G, honest_g, {"tamper": plant},
         "Plant an ode/ package and sitecustomize.py in the attack dir (Bob "
         "runs with cwd here). If any import resolves through cwd, the planted "
         "wcheck accepts everything."))

    add(("05-honest-machine-mutant-binary", G, honest_g,
         {"binary": wproducer.emit_w32(_mach(
             G_STEPS.replace("(rotr t5 7)", "(rotr t5 5)")))},
         "An honest machine definition in the store, a mutant binary, honestly "
         "hashed. Once caught by the emitter binding; now the checker proves "
         "the decoded bytes themselves and no machine definition is read."))
    add(("06-huge-inputs", G, honest_g,
         {"inputs_lines": ["4294967296 0 0 0 0 0", "-1 0 0 0 0 0"]},
         "Honest store; INPUTS names out-of-domain words (2^32, -1). Found: "
         "Bob printed ACCEPT and then crashed; fixed: Bob rejects inputs "
         "outside the domain before anything else."))
    raw = bytearray(wproducer.emit_w32(honest_g))
    raw[-1] = 39
    add(("07-rotr-39-in-binary", G, honest_g, {"binary": bytes(raw)},
         "One byte of an honest binary changed (originally a rotr count "
         "39 == 7 mod 32). The decoder must reject malformed bytes or the "
         "proof must catch them."))
    add(("08-mallory-chosen-inputs", G, honest_g,
         {"inputs_lines": ["305419896 2596069104 4294967295 0 1 2",
                           "0 0 0 0 4294967295 4294967295"]},
         "Honest store plus INPUTS chosen by Mallory (the 'wrong only where I "
         "say' probe). W32 has no branches, so there is no way to be wrong on "
         "one input only."))
    add(("09-noncanonical-store-file", G, honest_g,
         {"tamper": lambda dirn, _:
            open(os.path.join(dirn, hash_of(honest_g).hex() + ".sexp"),
                 "ab").write(b"\n")},
         "The machine definition file has a trailing newline. Once rejected "
         "by the reader; the checker no longer reads machine definitions, so "
         "it is now irrelevant and Bob is right. Attack 23 aims the same "
         "trick at the spec, which is read."))
    hdr = bytes([6]) + struct.pack("<I", 2) + bytes([4])
    # 20-name-capture has its own TARGET; the forward-ref binary comes after.

    return forge


def attacks_hash65():
    honest = wproducer.compile_wspec(HASH65)
    text = open(os.path.join(EXAMPLES, "blake3-hash-65.sexp")).read()
    out = []
    out.append(("11-hash65-honest", HASH65, honest, {"target": "hash65"},
                "Control for the hash65 target: an honest build."))

    import copy
    swapped = copy.deepcopy(honest)
    ren = {Sym(f"m{i}"): Sym(f"m{(i + 16) % 32}") for i in range(32)}

    def r(e):
        if isinstance(e, Sym):
            return ren.get(e, e)
        if isinstance(e, int):
            return e
        return [e[0]] + [x if (e[0] == "rotr" and x is e[2]) else r(x)
                         for x in e[1:]]
    swapped_steps = [[n, r(e)] for n, e in word.steps_of(swapped)]
    swapped = assoc("wmachine", ("isa", Sym("W32")),
                    ("inputs", word.inputs_of(swapped)),
                    ("steps", swapped_steps),
                    ("outputs", word.outputs_of(swapped)))
    out.append(("12-hash65-swap-blocks", HASH65, swapped, {"target": "hash65"},
                "Machine computes the hash with the two 64-byte blocks swapped. "
                "Symbolically m0 and m16 are distinct variables, so this must "
                "be caught."))

    import re
    ivs = ("1779033703 3144134277 1013904242 2773480762 1359893119 "
           "2600822924 528734635 1541459225")
    m = re.search(r"(\(call #[0-9a-f]+ )"
                  r"(c0b0_0 c0b0_1 c0b0_2 c0b0_3 c0b0_4 c0b0_5 c0b0_6 c0b0_7)",
                  text)
    mut = text[:m.start(2)] + ivs + text[m.end(2):]
    out.append(("13-hash65-drop-chain", HASH65,
                wproducer.compile_wspec(parse(mut)), {"target": "hash65"},
                "Second compression starts from the IV instead of block 0's "
                "chaining value (the chain is dropped); compiled honestly "
                "from a mutant spec, certified against the true spec."))
    mut14 = text.replace(" 0 0 64 1))", " 0 0 64 11))", 1)
    mut14 = re.sub(r"\(outputs \(c0b1_0 c0b1_1 c0b1_2 c0b1_3 c0b1_4 "
                   r"c0b1_5 c0b1_6 c0b1_7\)\)",
                   "(outputs (c0b0_0 c0b0_1 c0b0_2 c0b0_3 c0b0_4 c0b0_5 "
                   "c0b0_6 c0b0_7))", mut14)
    out.append(("14-hash65-truncate-to-one-block", HASH65,
                wproducer.compile_wspec(parse(mut14)), {"target": "hash65"},
                "Machine returns the ROOT output of block 0 alone (the hash of "
                "the first 64 bytes) and ignores the 65th byte."))
    st = [[n, e] for n, e in word.steps_of(honest)]
    for i, (n, e) in enumerate(st):
        if isinstance(e, list) and e[0] == "add":
            st[i] = [n, [e[0], e[2], e[1]]]
            break
    commuted = assoc("wmachine", ("isa", Sym("W32")),
                     ("inputs", word.inputs_of(honest)), ("steps", st),
                     ("outputs", word.outputs_of(honest)))
    out.append(("15-hash65-commuted-add", HASH65, commuted,
                {"target": "hash65"},
                "An honest machine with one add commuted: a correct, "
                "differently-written program. The checker should accept "
                "(commutativity is canonicalized) and Bob be right."))
    out.append(("16-hash65-chosen-messages", HASH65, honest,
                {"target": "hash65", "inputs_lines": [
                    _words(b"\0" * 65),
                    _words(b"\x41" * 64 + b"\0"),
                    _words(bytes(range(64)) + bytes([0]))]},
                "Honest machine; INPUTS are Mallory-chosen messages, including "
                "two equal blocks -- the inputs where a swap would be invisible."))

    cert17 = [("cert", Sym("correctness")), ("property", Sym("equals-wspec-v1")),
              ("spec", HASH65_HASH), ("machine", HASH65_HASH),
              ("binary-hash", Bytes(blake3(wproducer.emit_w32(honest)))),
              ]
    out.append(("17-hash65-machine-is-the-spec", HASH65, honest,
                {"target": "hash65", "cert_fields": cert17},
                "Certificate names the SPEC definition as the machine. Once "
                "rejected; machine fields are now ignored and the honest "
                "binary is proved, so Bob is right."))

    raw = bytearray(wproducer.emit_w32(honest))
    for k in range(8):
        struct.pack_into("<I", raw, 8 + 4 * k, k)
    out.append(("18-hash65-outputs-are-inputs", HASH65, honest,
                {"target": "hash65", "binary": bytes(raw)},
                "Raw binary whose output indices point at the inputs m0..m7 "
                "(hash := message prefix); now caught by the proof."))
    spec3 = _load("blake3-hash-3.sexp")
    m3 = wproducer.compile_wspec(spec3)

    def override19(dirn, _md=None):
        cert = assoc("certificate", ("cert", Sym("correctness")),
                     ("property", Sym("equals-wspec-v1")),
                     ("spec", HASH65_HASH), ("machine", hash_of(m3)),
                     ("binary-hash", Bytes(blake3(wproducer.emit_w32(m3)))),
                     )
        put_definition(dirn, spec3)
        put_definition(dirn, m3)
        put_definition(dirn, cert)
        with open(os.path.join(dirn, "certificate.sexp"), "wb") as f:
            f.write(canonical_bytes(cert))
        with open(os.path.join(dirn, "binary.bin"), "wb") as f:
            f.write(wproducer.emit_w32(m3))
    out.append(("19-hash65-wrong-length-machine", HASH65, honest,
                {"target": "hash65", "tamper": override19},
                "The proved hash-3 machine certified against the hash65 "
                "spec: a length-confusion attack, caught by the binary's own input count."))

    out.append(("20-name-capture-in-producer", G, wproducer.compile_wspec(G),
                {},
                "Not a store attack: a finding against the producer. A spec "
                "whose input is named t0 collided with the fresh names the "
                "inliner minted. Fixed in wproducer._Fresh; regression in "
                "tests/test_blake3_slice.py (CallTest). The store here is "
                "honest control."))
    return out


def main():
    global _forge
    all_attacks = attacks() + attacks_hash65()

    # Forward-reference binary for 10 (built from the honest G machine).
    honest_g = wproducer.compile_wspec(G)
    hdr = (bytes(0) + struct.pack("<H", 6)[:0])  # unused; header written below

    for item in all_attacks:
        name, spec, md, kw, notes = item
        kw = dict(kw)
        cert_fields = kw.pop("cert_fields", None)
        if cert_fields is not None:
            real_forge = _forge

            def make(kw, cert_fields):
                def tamper(dirn, md):
                    cert = assoc("certificate", *cert_fields)
                    put_definition(dirn, cert)
                    with open(os.path.join(dirn, "certificate.sexp"), "wb") as f:
                        f.write(canonical_bytes(cert))
                kw["tamper"] = tamper
                return kw
            kw = make(kw, cert_fields)
        _forge(name, notes, spec, md, **kw)

    # 01's byte flip (after its honest store exists).
    p = os.path.join(HERE, "attacks", "01-flip-byte", "binary.bin")
    raw = bytearray(wproducer.emit_w32(honest_g))
    raw[40] ^= 7
    with open(p, "wb") as f:
        f.write(bytes(raw))
    # Attack 10: forward-reference raw binary.
    fwd_hdr = bytes([0, 0])
    n_in = struct.pack("<H", 6)
    n_steps = struct.pack("<I", 2)
    n_out = struct.pack("<H", 4)
    outs = b"".join(struct.pack("<I", 7) for _ in range(4))
    s0 = bytes([0, 0]) + struct.pack("<I", 7)
    s1 = bytes([0, 0]) + struct.pack("<I", 0)
    fwd = n_in + n_steps + n_out + outs + s0 + s1
    _forge("10-forward-reference-binary",
           "Raw W32 bytes with a step copying a later step (forward "
           "reference). Found: this binary's hex was all digits, so under "
           "the old canonical form it could not be a symbol and parsed as "
           "an integer -- a hex/integer ambiguity. Fixed: byte strings "
           "are now #hex and symbols never start with a digit.",
           G, honest_g, binary=fwd)
    # Round 3: the root and a delivered ode-base and spec.
    forged = os.path.join(HERE, "attacks", "21-forged-ode-base")
    _forge("21-forged-ode-base",
           "Mallory delivers his own ode-base beside a wrong binary: a "
           "wcheck that accepts everything. The root admits ode-base only "
           "by the package's pinned tree hash.",
           G, _mach(G_STEPS.replace("(rotr t5 7)", "(rotr t5 6)")))
    import shutil
    shutil.copytree(os.path.join(HERE, "ode-base"), os.path.join(forged, "ode-base"),
                    ignore=shutil.ignore_patterns("__pycache__"))
    with open(os.path.join(forged, "ode-base", "ode", "wcheck.py"), "a") as f:
        f.write("\n\ndef check_certificate(store_dir, cert):\n"
                "    return None\n")
    extra = os.path.join(HERE, "attacks", "22-ode-base-extra-file")
    _forge("22-ode-base-extra-file",
           "An otherwise genuine ode-base delivered with one added file, "
           "ode/sitecustomize.py. Any added, removed, or changed file "
           "changes the tree hash.", G, _mach(G_STEPS.replace("(rotr t5 7)", "(rotr t5 6)")))
    shutil.copytree(os.path.join(HERE, "ode-base"), os.path.join(extra, "ode-base"),
                    ignore=shutil.ignore_patterns("__pycache__"))
    with open(os.path.join(extra, "ode-base", "ode", "sitecustomize.py"), "w") as f:
        f.write("pass\n")
    _forge("23-noncanonical-spec-file",
           "The spec is now delivered by Mallory and fetched by its pinned "
           "hash. Here its file has a trailing newline: the reader must "
           "reject non-canonical bytes even though they parse to the "
           "pinned spec.", G, honest_g,
           tamper=lambda dirn, _: open(os.path.join(dirn, G_HASH.hex() + ".sexp"),
                                       "ab").write(b"\n"))
    _forge("24-spec-missing",
           "The store omits the spec entirely. Bob holds only its hash, so "
           "Mallory can deny availability -- Bob rejects -- but cannot "
           "change correctness.", G, honest_g,
           tamper=lambda dirn, _: os.remove(os.path.join(dirn, G_HASH.hex() + ".sexp")))
    print(f"{len(all_attacks) + 5} attacks regenerated")


if __name__ == "__main__":
    main()
