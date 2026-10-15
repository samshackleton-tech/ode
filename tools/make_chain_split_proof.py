#!/usr/bin/env pypy3
"""Produce the all-counts chain-splitting theorem using proved arithmetic."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from ode.canon import Sym, canonical_bytes, hash_of, parse
from ode.nat_proof import arithmetic_lemmas


def artifacts(theory):
    goal = parse(f'''(goal 3 #{hash_of(theory).hex()}
      ((n Nat) (k Nat) (s State) (m Blocks) (i Nat))
      (eq (chain (add n k) s m i)
          (chain k (chain n s m i) m (add n i))))''')
    first = '(compress s (block-at m i))'
    base = '''((unfold add (zero) k)
      (refl s) (refl m) (refl i)
      (cong chain 0 1 2 3)
      (refl k)
      (unfold chain (zero) s m i)
      (unfold add (zero) i)
      (cong chain 5 6 2 7)
      (sym 8) (trans 4 9))'''
    step = f'''((unfold add (succ p) k)
      (refl s) (refl m) (refl i)
      (cong chain 0 1 2 3)
      (unfold chain (succ (add p k)) s m i)
      (trans 4 5)
      (ih p k {first} m (succ i))
      (trans 6 7)
      (refl k)
      (refl (chain p {first} m (succ i)))
      (lemma 1 p i)
      (cong chain 9 10 2 11)
      (trans 8 12)
      (unfold chain (succ p) s m i)
      (unfold add (succ p) i)
      (cong chain 9 14 2 15)
      (sym 16) (trans 13 17))'''
    # Both arithmetic lemmas are proved anew in this theory. Equality of
    # textual function names alone grants no import permission.
    proof = [Sym('proof'), 3, hash_of(goal), arithmetic_lemmas()[:2],
             parse(f'(induct n ((zero () {base}) (succ (p) {step})))')]
    return goal, proof


def main():
    directory = ROOT / 'examples' / 'proofs'
    theory = parse((directory / 'chain-split.theory.sexp').read_bytes())
    goal, proof = artifacts(theory)
    for kind, value in (('goal', goal), ('proof', proof)):
        (directory / f'chain-split.{kind}.sexp').write_bytes(canonical_bytes(value))


if __name__ == '__main__':
    main()
