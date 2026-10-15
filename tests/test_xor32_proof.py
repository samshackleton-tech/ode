"""Word32 XOR laws and normalization: all derived from constructor semantics."""
from pathlib import Path
import random
import subprocess
import sys
import unittest
from unittest.mock import patch

from ode.canon import Sym, canonical_bytes, hash_of, parse
from ode.kernel import Reject, verify
from ode.xor32_proof import artifacts, law_library, prove, theory as make_theory
from ode.equational_proof import app, var
from ode.word_literal import ZERO
from ode.arx_proof import export_normalizer

EXAMPLES = Path(__file__).resolve().parent.parent / 'examples' / 'proofs'


def theory():
    return make_theory(parse((EXAMPLES / 'bits.theory.sexp').read_bytes()))


def bundle():
    return [parse((EXAMPLES / f'xor32.{kind}.sexp').read_bytes())
            for kind in ('theory', 'goal', 'proof')]


class Word32ProofTest(unittest.TestCase):
    def test_theory_and_proof_reproduce(self):
        t, g, p = bundle()
        self.assertEqual(canonical_bytes(t), canonical_bytes(theory()))
        for expected, actual in zip((g,p), export_normalizer(t, parse('(xor32 x (xor32 y x))'))):
            self.assertEqual(canonical_bytes(expected), canonical_bytes(actual))
        own_goal,own_proof=artifacts(t)
        self.assertEqual(own_goal,g)
        verify(t,own_goal,own_proof)
        result = verify(t, g, p)
        self.assertLess(result['work'], 150000)

    def test_verification_needs_no_producer_or_old_checker(self):
        # A fresh process refuses imports of the old verifier, evaluator,
        # and both proof producers. The already-produced proof still checks.
        script = """
import importlib.abc
import sys
class Block(importlib.abc.MetaPathFinder):
    def find_spec(self, name, path=None, target=None):
        if name in {'ode.check', 'ode.word', 'ode.native',
                    'ode.nat_proof', 'ode.xor32_proof'}:
            raise ImportError('outside the proof reliance set: ' + name)
sys.meta_path.insert(0, Block())
from ode.proof_cli import main
raise SystemExit(main(sys.argv[1:]))
"""
        paths = [str(EXAMPLES / f'xor32.{k}.sexp') for k in ('theory', 'goal', 'proof')]
        p = subprocess.run([sys.executable, '-c', script, *paths],
                           cwd=EXAMPLES.parent.parent, capture_output=True,
                           text=True, timeout=30)
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertIn('ACCEPT', p.stdout)

    def test_core_word_laws_as_independent_goals(self):
        t, _, p = bundle()
        library=law_library()
        # Identity, commutativity, associativity, cancellation. Each becomes
        # the main goal and only its prior proved lemmas are available.
        for i in (40, 41, 42, 43):
            with self.subTest(lemma=i):
                _, params, eq, deriv = library[i]
                g = [Sym('goal'),3,hash_of(t),params,eq]
                proof = [Sym('proof'),3,hash_of(g),library[:i],deriv]
                verify(t,g,proof)

    def test_explicit_word_constructor_has_exactly_32_bits(self):
        for bits in (31, 33):
            t, g, p = bundle()
            g[4][2] = app('word32', *[app('bit0') for _ in range(bits)])
            p[2] = hash_of(g)
            with self.subTest(bits=bits), self.assertRaises(Reject):
                verify(t,g,p)

    def test_wrong_selector_breaks_its_extensionality_proof(self):
        t,g,p = bundle()
        t[4][33][3][0][2] = var('b0')  # bit-at-31 returns bit 0
        g[2] = hash_of(t)
        p[2] = hash_of(g)
        with self.assertRaises(Reject):
            verify(t,g,p)

    def test_wrong_xor_semantics_are_not_hidden_by_a_normalizer(self):
        t,g,p = bundle()
        # Define xor32(x,y)=x, which preserves width but breaks cancellation.
        t[4][-1][3][0][2] = app('word32', *[var(f'b{i}') for i in range(32)])
        g[2] = hash_of(t)
        p[2] = hash_of(g)
        with self.assertRaises(Reject):
            verify(t,g,p)

    def test_a_lying_normalizer_cannot_choose_the_result(self):
        t,g,p = bundle()
        g[4][2] = ZERO  # x XOR (y XOR x) = 0 is false for nonzero y
        p[2] = hash_of(g)
        with self.assertRaisesRegex(Reject, 'different equation'):
            verify(t,g,p)

    def test_random_expression_certificates(self):
        rng = random.Random(32)
        t = theory()
        variables = [var(x) for x in 'abcd']
        params = [[x,var('Word32')] for x in variables]

        def tree(atoms):
            if not atoms:
                return ZERO
            if len(atoms)==1:
                return atoms[0]
            k = rng.randrange(1,len(atoms))
            return app('xor32',tree(atoms[:k]),tree(atoms[k:]))

        for _ in range(20):
            atoms = [rng.choice(variables) for _ in range(rng.randrange(1,8))]
            parity = [x for x in variables if atoms.count(x) % 2]
            left = tree(atoms)
            rng.shuffle(parity)
            right = tree(parity)
            g,p = prove(t,params,left,right)
            verify(t,g,p)

    def test_mixed_nonzero_constant_folding(self):
        from ode.word_literal import literal
        t=theory();x=var('x')
        for a,b in ((1,2),(0xffffffff,1),(9,9),(0xaaaaaaaa,0x55555555)):
            expression=app('xor32',app('xor32',x,literal(a)),literal(b))
            g,p=export_normalizer(t,expression)
            expected=x if a==b else app('xor32',x,literal(a^b))
            self.assertEqual(g[4][2],expected)
            verify(t,g,p)

    def test_concrete_words_can_cancel_without_being_evaluated(self):
        ones = app('word32', *[app('bit1') for _ in range(32)])
        t = theory()
        g,p = prove(t,[],app('xor32',ones,ones),ZERO)
        verify(t,g,p)

    def test_existing_normalizer_exports_a_kernel_proof(self):
        expression = parse('(xor32 x (xor32 y x))')
        t = theory()
        g,p = export_normalizer(t, expression)
        self.assertEqual(g[4], parse('(eq (xor32 x (xor32 y x)) y)'))
        verify(t,g,p)

    def test_a_broken_existing_normalizer_cannot_supply_a_proof(self):
        from ode.check import Dag
        with patch.object(Dag, 'xor', lambda self, a, b: a):
            with self.assertRaisesRegex(ValueError, 'different parity'):
                export_normalizer(theory(), parse('(xor32 x (xor32 y x))'))

    def test_suffix_cancellation_emits_the_remaining_zero_elimination(self):
        # Found while building the producer: after b cancels a tail b,
        # the proof reaches a XOR zero, and still needs right identity.
        t = theory()
        g,p = prove(t,parse('((a Word32) (b Word32))'),
                    parse('(xor32 b (xor32 a b))'),var('a'))
        verify(t,g,p)

    def test_unequal_parities_stop_the_producer(self):
        with self.assertRaisesRegex(ValueError, 'different parity'):
            prove(theory(),parse('((x Word32) (y Word32))'),var('x'),var('y'))


if __name__ == '__main__':
    unittest.main()
