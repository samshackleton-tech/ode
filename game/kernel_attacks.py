#!/usr/bin/env pypy3
"""Replay attacks on the proof-object kernel. No native execution involved.

pypy3 game/kernel_attacks.py

The owner supplies the batching theory and goal. Mallory supplies the
proof, or attempts to substitute a theory or goal. Honest rehashing is
also tried: identity is necessary, but never sufficient, for acceptance.
Every variant is constructed here; generated directories are unnecessary.
"""
import copy
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from ode.canon import Sym, hash_of, parse
from ode.kernel import Reject, verify


def cases():
    directory = ROOT / 'examples' / 'proofs'
    original = [parse((directory / f'batching.{k}.sexp').read_bytes())
                for k in ('theory', 'goal', 'proof')]
    yield 'honest-induction', original, True
    names = ('no-base', 'no-step', 'use-hypothesis-in-base', 'capture-predecessor',
             'generalize-predecessor', 'self-reference', 'oracle', 'different-goal',
             'honestly-rehashed-wrong-goal', 'different-theory',
             'honestly-rehashed-wrong-stride', 'nondecreasing-definition')
    for name in names:
        theory, goal, proof = copy.deepcopy(original)
        if name == 'no-base':
            proof[3][3] = [parse('(refl s)')]
        elif name == 'no-step':
            proof[3][4] = [parse('(refl s)')]
        elif name == 'use-hypothesis-in-base':
            proof[3][3] = [parse('(ih s m i)')]
        elif name == 'capture-predecessor':
            proof[3][2] = Sym('i')
        elif name == 'generalize-predecessor':
            proof[3][4][9] = parse('(ih (succ k) s m i)')
        elif name == 'self-reference':
            proof[3][4][-1] = parse('(trans 13 12)')
        elif name == 'oracle':
            proof[3][4][-1] = [Sym('oracle'), goal[4]]
        elif 'wrong-goal' in name or name == 'different-goal':
            goal[4][2][1] = parse('(succ n)')
        elif 'wrong-stride' in name or name == 'different-theory':
            theory[4][2][4][1][-1] = parse('(succ i)')
        elif name == 'nondecreasing-definition':
            theory[4][0][4][1] = parse('(double (succ k))')
        if name.startswith('honestly-rehashed') or name == 'nondecreasing-definition':
            goal[2] = hash_of(theory)
            proof[2] = hash_of(goal)
        yield name, (theory, goal, proof), False


def main():
    failures = 0
    for name, args, expect in cases():
        try:
            result = verify(*args)
            accepted, reason = True, f"{result['rules']} rules"
        except Reject as e:
            accepted, reason = False, str(e)
        ok = accepted == expect
        failures += not ok
        print(f"{'PASS' if ok else 'FAIL'} {name}: {'ACCEPT' if accepted else 'REJECT'} {reason}")
    return int(failures != 0)


if __name__ == '__main__':
    raise SystemExit(main())
