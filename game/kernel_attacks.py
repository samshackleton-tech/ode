#!/usr/bin/env pypy3
"""Replay attacks on the proof-object kernel. No native execution involved.

pypy3 game/kernel_attacks.py

The owner supplies each example's theory and goal. Mallory supplies the
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
            proof[4][2][0][2] = [parse('(refl s)')]
        elif name == 'no-step':
            proof[4][2][1][2] = [parse('(refl s)')]
        elif name == 'use-hypothesis-in-base':
            proof[4][2][0][2] = [parse('(ih s m i)')]
        elif name == 'capture-predecessor':
            proof[4][2][1][1][0] = Sym('i')
        elif name == 'generalize-predecessor':
            proof[4][2][1][2][9] = parse('(ih (succ k) s m i)')
        elif name == 'self-reference':
            proof[4][2][1][2][-1] = parse('(trans 13 12)')
        elif name == 'oracle':
            proof[4][2][1][2][-1] = [Sym('oracle'), goal[4]]
        elif 'wrong-goal' in name or name == 'different-goal':
            goal[4][2][1] = parse('(succ n)')
        elif 'wrong-stride' in name or name == 'different-theory':
            theory[4][2][3][1][2][-1] = parse('(succ i)')
        elif name == 'nondecreasing-definition':
            theory[4][0][3][1][2] = parse('(double (succ k))')
        if name.startswith('honestly-rehashed') or name == 'nondecreasing-definition':
            goal[2] = hash_of(theory)
            proof[2] = hash_of(goal)
        yield name, (theory, goal, proof), False

    reuse = [parse((directory / f'nat-add.{k}.sexp').read_bytes())
             for k in ('theory', 'goal', 'proof')]
    yield 'honest-lemma-reuse', reuse, True
    for name in ('circular-lemma', 'forward-lemma', 'leaked-lemma-hypothesis',
                 'unchecked-unused-lemma', 'wrong-lemma-instantiation'):
        theory, goal, proof = copy.deepcopy(reuse)
        if name in ('circular-lemma', 'forward-lemma'):
            index = 0 if name == 'circular-lemma' else 1
            proof[3][0][3] = parse(f'(derive ((lemma {index} a)))')
        elif name == 'leaked-lemma-hypothesis':
            proof[4] = parse('(derive ((ih a b c d)))')
        elif name == 'unchecked-unused-lemma':
            proof[3].append(parse('(lemma () (eq (zero) (succ (zero))) (derive ((refl (zero)))))'))
        else:
            proof[4] = parse('(derive ((lemma 0 a b)))')
        yield name, (theory, goal, proof), False

    bits = [parse((directory / 'bits.theory.sexp').read_bytes()),
            parse((directory / 'xor-cancel.goal.sexp').read_bytes()),
            parse((directory / 'xor-cancel.proof.sexp').read_bytes())]
    yield 'honest-bitstring-induction', bits, True
    for name in ('omitted-constructor-case', 'hypothesis-for-a-nonrecursive-field',
                 'wrong-bit-xor-definition', 'recursion-on-parent'):
        theory, goal, proof = copy.deepcopy(bits)
        if name == 'omitted-constructor-case':
            del proof[4][2][0]
        elif name == 'hypothesis-for-a-nonrecursive-field':
            proof[4][2][1][2][9] = parse('(ih h)')
        elif name == 'wrong-bit-xor-definition':
            theory[4][1][3][1][2] = Sym('b')
        else:
            theory[4][5][3][1][2] = parse('(xor-bits (bit h t) ys)')
        goal[2] = hash_of(theory)
        proof[2] = hash_of(goal)
        yield name, (theory, goal, proof), False

    word = [parse((directory / f'xor32.{k}.sexp').read_bytes())
            for k in ('theory', 'goal', 'proof')]
    yield 'honest-word32-normalization', word, True
    for name in ('word32-wrong-selector', 'word32-lying-result', 'word32-normalizer-oracle'):
        theory, goal, proof = copy.deepcopy(word)
        if name == 'word32-wrong-selector':
            theory[4][33][3][0][2] = Sym('b0')
            goal[2] = hash_of(theory)
        elif name == 'word32-lying-result':
            goal[4][2] = [Sym('word32')] + [[Sym('bit0')] for _ in range(32)]
        else:
            proof[4] = [Sym('derive'), [[Sym('normalize'), goal[4]]]]
        proof[2] = hash_of(goal)
        yield name, (theory, goal, proof), False

    rotate = [parse((directory / f'rotate32.{k}.sexp').read_bytes())
              for k in ('theory', 'goal', 'proof')]
    yield 'honest-rotation-export', rotate, True
    for name in ('rotation-wrong-field', 'rotation-wrong-count', 'rotation-oracle'):
        theory, goal, proof = copy.deepcopy(rotate)
        if name == 'rotation-wrong-field':
            definition = next(d for d in theory[4] if d[0] == 'ror-8')
            definition[3][0][2][1] = Sym('b24')
            goal[2] = hash_of(theory)
        elif name == 'rotation-wrong-count':
            goal[4][1][2][1][1][0] = Sym('ror-7')
        else:
            proof[4] = [Sym('derive'), [[Sym('rotate-congruence'), goal[4]]]]
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
