#!/usr/bin/env pypy3
"""Prove XOR cancellation and width preservation from bit definitions.

No kernel import, evaluator shortcut, or word-operation axiom.
"""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from ode.canon import Sym, canonical_bytes, hash_of, parse


def artifacts(theory):
    bit_cancel = parse('''(lemma ((b Bit)) (eq (xor-bit b b) (bit0))
      (induct b
        ((bit0 () ((unfold xor-bit (bit0) (bit0))))
         (bit1 () ((unfold xor-bit (bit1) (bit1))
                   (unfold not-bit (bit1)) (trans 0 1))))))''')
    word_equation = parse('(eq (xor-bits x x) (zeros x))')
    word_derivation = parse('''(induct x
      ((empty ()
         ((unfold xor-bits (empty) (empty))
          (unfold zeros (empty)) (sym 1) (trans 0 2)))
       (bit (h t)
         ((unfold xor-bits (bit h t) (bit h t))
          (refl h) (unfold head (bit h t)) (cong xor-bit 1 2)
          (lemma 0 h) (trans 3 4)
          (refl t) (unfold tail (bit h t)) (cong xor-bits 6 7)
          (ih t) (trans 8 9)
          (cong bit 5 10) (trans 0 11)
          (unfold zeros (bit h t)) (sym 13) (trans 12 14)))))''')
    zero_width = parse('''(lemma ((x Bits)) (eq (width (zeros x)) (width x))
      (induct x
        ((empty () ((unfold zeros (empty)) (cong width 0)))
         (bit (h t)
           ((unfold zeros (bit h t)) (cong width 0)
            (unfold width (bit (bit0) (zeros t))) (trans 1 2)
            (ih t) (cong succ 4) (trans 3 5)
            (unfold width (bit h t)) (sym 7) (trans 6 8))))))''')
    parameters = parse('((x Bits))')
    result = {}
    for name, equation, lemmas, derivation in (
        ('xor-cancel', word_equation, [bit_cancel], word_derivation),
        ('xor-width', parse('(eq (width (xor-bits x x)) (width x))'),
         [bit_cancel, [Sym('lemma'), parameters, word_equation, word_derivation], zero_width],
         parse('(derive ((lemma 1 x) (cong width 0) (lemma 2 x) (trans 1 2)))')),
    ):
        goal = [Sym('goal'), 3, hash_of(theory, 'theory'), parameters, equation]
        proof = [Sym('proof'), 3, hash_of(goal, 'goal'), lemmas, derivation]
        result[name] = (goal, proof)
    return result


def main():
    directory = ROOT / 'examples' / 'proofs'
    theory = parse((directory / 'bits.theory.sexp').read_bytes())
    for name, (goal, proof) in artifacts(theory).items():
        for kind, value in (('goal', goal), ('proof', proof)):
            (directory / f'{name}.{kind}.sexp').write_bytes(canonical_bytes(value))


if __name__ == '__main__':
    main()
