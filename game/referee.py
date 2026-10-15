#!/usr/bin/env pypy3
"""The referee: runs Bob against one or more attack directories, scores.

    pypy3 game/referee.py game/attacks/*          # score every attack
    pypy3 game/referee.py DIR [DIR ...]

For each attack directory, Bob is run through the root in a fresh
subprocess (cwd = the attack directory, so anything planted there is in
effect) on the game's public inputs and on any inputs the attack
declares in INPUTS, one line each. The truth is the pinned
specification, run directly: the referee refuses to start unless its
copies in examples/ hash to the pins.

A run fails when Bob prints ACCEPT and then a wrong output (Mallory
wins), or when a control (EXPECT: accept) is not accepted and right.
Exit status: 0 when nothing failed, 1 otherwise.
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, "bootstrap", "root")
RELIANCE = os.path.join(HERE, "bootstrap", "game-targets", "RELIANCE")
PUBLIC_ODE_BASE = os.path.join(HERE, "ode-base")
EXAMPLES = os.path.join(os.path.dirname(HERE), "examples")
sys.path.insert(0, os.path.dirname(HERE))  # the referee uses the toolchain, not ode-base
from ode import produce, word  # noqa: E402
from ode.canon import field, hash_of, parse  # noqa: E402

import struct  # noqa: E402

PUBLIC_INPUTS = {
    "g": [
        [1, 2, 3, 4, 5, 6],
        [0, 0, 0, 0, 0, 0],
        [0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x61626300, 0],
        [0xFFFFFFFF] * 6,
        [0xDEADBEEF, 0xCAFEBABE, 0x01234567, 0x89ABCDEF, 0x13579BDF, 0x2468ACE0],
    ],
    "blake3": [
        list(struct.unpack("<32I", msg + b"\0" * (128 - len(msg))))
        for msg in (b"a" * 65, bytes(range(65)), b"\xff" * 65,
                    b"The quick brown fox jumps over the lazy dog, said BLAKE3." + b"!" * 8)
    ],
}
SPEC_FILE = {"g": "blake3-g.sexp", "blake3": "blake3.sexp"}
# The game's blake3 attacks are about 65-byte messages: Bob asks for len=65.
NAMED = {"g": {}, "blake3": {"len": 65}}
AT = {"g": {}, "blake3": {"len": 65, "m": 32}}
LIBRARY = produce.library_of(EXAMPLES)


def target_of(attack_dir):
    path = os.path.join(attack_dir, "TARGET")
    if os.path.isfile(path):
        with open(path) as f:
            return f.read().strip()
    return "g"


def _pinned_specs():
    with open(RELIANCE, "rb") as f:
        pins = dict((str(p[0]), p[1]) for p in field(parse(f.read()), "targets"))
    specs = {}
    for target, name in SPEC_FILE.items():
        with open(os.path.join(EXAMPLES, name), "rb") as f:
            specs[target] = parse(f.read())
        if hash_of(specs[target]) != pins[target]:
            raise SystemExit(f"referee: examples/{name} is not the pinned {target}")
    return specs


SPECS = _pinned_specs()


def truth(values, target):
    return word.run(SPECS[target], AT[target], values, LIBRARY.get)


def run_bob(attack_dir, values, target="g"):
    # An attack may deliver its own ode-base; otherwise Bob fetches the
    # public one. Either way the root admits it only by its pinned hash.
    base = os.path.join(attack_dir, "ode-base")
    if not os.path.isdir(base):
        base = PUBLIC_ODE_BASE
    cmd = ["pypy3", os.path.join(ROOT, "launch.py"), RELIANCE, base,
           attack_dir, target] + \
          [f"{k}={v}" for k, v in NAMED[target].items()] + [str(v) for v in values]
    p = subprocess.run(cmd, cwd=attack_dir, capture_output=True, text=True,
                       timeout=120)
    lines = (p.stdout or "").splitlines()
    return p.returncode, lines, p.stderr


def score(attack_dir):
    result = _score(attack_dir)
    # A control (an EXPECT file saying accept) must be accepted and right:
    # a Bob who rejects honest work is broken too, just not in Mallory's favour.
    expect = os.path.join(attack_dir, "EXPECT")
    if os.path.isfile(expect) and open(expect).read().strip() == "accept" \
            and result[1] != "accepted and correct on every input":
        return ("CONTROL FAILED", result[1])
    return result


def _score(attack_dir):
    target = target_of(attack_dir)
    n_in = {"g": 6, "blake3": 32}[target]
    inputs = list(PUBLIC_INPUTS[target])
    extra = os.path.join(attack_dir, "INPUTS")
    if os.path.isfile(extra):
        with open(extra) as f:
            for line in f:
                if line.strip():
                    inputs.append([int(x, 0) for x in line.split()])
    for values in inputs:
        if len(values) != n_in or any(not (0 <= v < 2 ** 32) for v in values):
            # Outside the domain: no true answer exists, so no wrong one.
            # Bob must still reject rather than print ACCEPT and crash.
            code, lines, err = run_bob(attack_dir, values, target)
            if lines and lines[0] == "ACCEPT":
                return ("MALLORY WINS", f"inputs {values}: outside the "
                        "domain, yet Bob accepted")
            continue
        code, lines, err = run_bob(attack_dir, values, target)
        verdict = lines[0] if lines else f"(no output; exit {code})"
        if verdict == "ACCEPT":
            got = lines[1] if len(lines) > 1 else ""
            want = " ".join(str(v) for v in truth(values, target))
            if got != want:
                return ("MALLORY WINS", f"inputs {values}: Bob accepted and "
                        f"output {got!r}; true G is {want!r}")
        elif not verdict.startswith("REJECT"):
            return ("mallory loses", f"Bob did not accept ({verdict})")
        else:
            return ("mallory loses", verdict)
    return ("mallory loses", "accepted and correct on every input")


def main(dirs):
    if not dirs:
        print(__doc__)
        return 2
    wins = 0
    for d in sorted(dirs):
        if not os.path.isdir(d):
            continue
        result, why = score(os.path.abspath(d))
        wins += result in ("MALLORY WINS", "CONTROL FAILED")
        print(f"{os.path.basename(d.rstrip('/')):40s} {result:14s} {why}")
    print(f"\n{wins} failure(s) (Mallory wins or rejected controls) in "
          f"{len(dirs)} attack(s)")
    return 1 if wins else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
