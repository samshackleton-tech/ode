"""Proof-producing normalization and kernel-checked lemma reuse."""
import copy
from pathlib import Path
import random
import unittest

from ode.canon import Sym, canonical_bytes, hash_of, parse
from ode.kernel import Reject, verify
from ode.nat_proof import arithmetic_lemmas, prove

EXAMPLES = Path(__file__).resolve().parent.parent / 'examples' / 'proofs'


def theory():
    return parse((EXAMPLES / 'nat-add.theory.sexp').read_bytes())


def bundle():
    return [parse((EXAMPLES / f'nat-add.{kind}.sexp').read_bytes())
            for kind in ('theory', 'goal', 'proof')]


class LemmaTest(unittest.TestCase):
    def test_the_example_and_producer_reproduce(self):
        t, g, p = bundle()
        result = verify(t, g, p)
        self.assertEqual(result['lemmas'], 5)
        self.assertLessEqual(result['work'],1976)
        self.assertLessEqual(len(canonical_bytes(p)),2085)
        made_g, made_p = prove(t, g[3], *g[4][1:])
        self.assertEqual(canonical_bytes(g), canonical_bytes(made_g))
        self.assertEqual(canonical_bytes(p), canonical_bytes(made_p))

    def test_each_lemma_is_proved_in_its_own_right(self):
        t = theory()
        lemmas = arithmetic_lemmas()
        for i, lemma in enumerate(lemmas):
            g = [Sym('goal'), 3, hash_of(t, 'theory'), lemma[1], lemma[2]]
            p = [Sym('proof'), 3, hash_of(g, 'goal'), lemmas[:i], lemma[3]]
            with self.subTest(index=i):
                verify(t, g, p)

    def test_false_unused_lemma_rejected(self):
        t, g, p = bundle()
        p[3].append(parse('''(lemma () (eq (zero) (succ (zero)))
                             (derive ((refl (zero)))))'''))
        with self.assertRaisesRegex(Reject, 'different equation'):
            verify(t, g, p)

    def test_self_and_forward_reference_rejected(self):
        for i in (0, 1, 100):
            t, g, p = bundle()
            p[3][0][3] = parse(f'(derive ((lemma {i} a)))')
            with self.subTest(index=i), self.assertRaisesRegex(Reject, 'earlier proved lemma'):
                verify(t, g, p)

    def test_lemma_hypothesis_does_not_escape(self):
        t, g, p = bundle()
        # No IH in the final proof, even after checking inductive lemmas.
        p[4] = parse('(derive ((ih a b c d)))')
        with self.assertRaisesRegex(Reject, 'outside step'):
            verify(t, g, p)

    def test_bad_lemma_instantiations_rejected(self):
        for instruction in ('(lemma 0)', '(lemma 0 a b)', '(lemma 5 a)',
                            '(lemma 0 outsider)'):
            t, g, p = bundle()
            p[4] = [Sym('derive'), [parse(instruction)]]
            with self.subTest(instruction=instruction), self.assertRaises(Reject):
                verify(t, g, p)
        t, g, p = bundle()
        t[2].append(Sym('State'))
        g[2] = hash_of(t, 'theory')
        g[3].append(parse('(s State)'))
        p[2] = hash_of(g, 'goal')
        p[4] = parse('(derive ((lemma 0 s)))')
        with self.assertRaisesRegex(Reject, 'sort mismatch'):
            verify(t, g, p)

    def test_changed_definition_with_honest_rehashing(self):
        t, g, p = bundle()
        t[4][0][3][0][2] = parse('(succ b)')  # false zero equation for ordinary addition
        g[2] = hash_of(t, 'theory')
        p[2] = hash_of(g, 'goal')
        with self.assertRaises(Reject):
            verify(t, g, p)

    def test_version_one_objects_are_rejected(self):
        for i in range(3):
            args = bundle()
            args[i][1] = 1
            with self.subTest(object=i), self.assertRaisesRegex(Reject, 'version'):
                verify(*args)

    def test_producer_cannot_smuggle_in_a_wrong_result(self):
        t, g, p = bundle()
        g[4][2] = parse('(succ (add (add d c) (add b a)))')
        p[2] = hash_of(g, 'goal')
        with self.assertRaisesRegex(Reject, 'different equation'):
            verify(t, g, p)


class ChainSplitTest(unittest.TestCase):
    def test_unbounded_chain_composition(self):
        from tools.make_chain_split_proof import artifacts
        args = [parse((EXAMPLES / f'chain-split.{kind}.sexp').read_bytes())
                for kind in ('theory', 'goal', 'proof')]
        result = verify(*args)
        self.assertEqual(result['lemmas'], 2)
        self.assertEqual(result['rules'], 48)
        goal, proof = artifacts(args[0])
        self.assertEqual(canonical_bytes(goal), canonical_bytes(args[1]))
        self.assertEqual(canonical_bytes(proof), canonical_bytes(args[2]))

    def test_wrong_second_batch_offset_rejected(self):
        args = [parse((EXAMPLES / f'chain-split.{kind}.sexp').read_bytes())
                for kind in ('theory', 'goal', 'proof')]
        args[1][4][2][-1] = Sym('i')  # forget to advance the block index
        args[2][2] = hash_of(args[1], 'goal')
        with self.assertRaises(Reject):
            verify(*args)


class NormalizerTest(unittest.TestCase):
    def test_generated_sum_proofs(self):
        rng = random.Random(17)
        t = theory()
        params = parse('((a Nat) (b Nat) (c Nat) (d Nat))')
        variables = [Sym(x) for x in 'abcd']

        def tree(atoms):
            if not atoms:
                return [Sym('zero')]
            if len(atoms) == 1:
                return atoms[0]
            k = rng.randrange(1, len(atoms))
            return [Sym('add'), tree(atoms[:k]), tree(atoms[k:])]

        for _ in range(50):
            atoms = [rng.choice(variables) for _ in range(rng.randrange(1, 9))]
            left = tree(atoms + [[Sym('zero')]])
            rng.shuffle(atoms)
            right = tree([[Sym('zero')]] + atoms)
            goal, proof = prove(t, params, left, right)
            verify(t, goal, proof)
            # Preserve multiplicity: changing an atom gives a false target.
            bad_goal = copy.deepcopy(goal)
            bad_goal[4][2] = [Sym('succ'), right]
            proof[2] = hash_of(bad_goal, 'goal')
            with self.assertRaises(Reject):
                verify(t, bad_goal, proof)

    def test_atoms_need_not_be_variables(self):
        t = theory()
        params = parse('((a Nat) (b Nat))')
        left = parse('(add (succ a) (add (zero) b))')
        right = parse('(add b (succ a))')
        g, p = prove(t, params, left, right)
        verify(t, g, p)

    def test_empty_and_singleton_sums(self):
        for term in ('(zero)', 'a', '(add (zero) a)', '(add a (zero))'):
            t = theory()
            goal, proof = prove(t, parse('((a Nat))'), parse(term), parse(term))
            verify(t, goal, proof)

    def test_unequal_multisets_fail_at_the_producer(self):
        with self.assertRaisesRegex(ValueError, 'different multisets'):
            prove(theory(), parse('((a Nat) (b Nat))'), parse('(add a a)'), parse('(add a b)'))


if __name__ == '__main__':
    unittest.main()
