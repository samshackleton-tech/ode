"""Kernel-certified rotation/XOR results and independently checked bit direction."""
from pathlib import Path
import random
import subprocess
import sys
import unittest
from unittest.mock import patch

from ode.canon import canonical_bytes, hash_of, parse
from ode.kernel import Reject, verify
from ode.rotate32_proof import export_normalizer, theory as make_theory
from ode.xor32_proof import ZERO, app, var

EXAMPLES = Path(__file__).resolve().parent.parent / 'examples' / 'proofs'


def theory():
    return make_theory(parse((EXAMPLES / 'bits.theory.sexp').read_bytes()))


def bundle():
    return [parse((EXAMPLES / f'rotate32.{kind}.sexp').read_bytes())
            for kind in ('theory','goal','proof')]


def literal(value):
    # Field zero is the least significant bit. This interpretation is
    # checked against independently computed integer rotations below.
    return app('word32', *[app('bit1' if value & (1 << i) else 'bit0') for i in range(32)])


class RotateProofTest(unittest.TestCase):
    def test_artifacts_reproduce(self):
        t,g,p = bundle()
        self.assertEqual(canonical_bytes(t),canonical_bytes(theory()))
        made_g,made_p = export_normalizer(t,g[4][1])
        self.assertEqual(canonical_bytes(g),canonical_bytes(made_g))
        self.assertEqual(canonical_bytes(p),canonical_bytes(made_p))
        result = verify(t,g,p)
        self.assertLess(result['work'],200000)
        self.assertEqual(result['lemmas'],107)

    def test_every_basis_bit_and_immediate_matches_integer_right_rotation(self):
        # A right-rotation model accidentally implemented as a left rotation
        # also satisfies composition/distribution. Ground statements pin the
        # direction independently, across all 32 basis bits and all counts.
        t = theory()
        h = hash_of(t)
        for n in range(32):
            for i in range(32):
                value = 1 << i
                expected = ((value >> n) | (value << ((32-n) % 32))) & 0xffffffff
                left = app(f'ror-{n}',literal(value))
                right = literal(expected)
                g = [var('goal'),3,h,[],app('eq',left,right)]
                p = [var('proof'),3,hash_of(g),[],
                     app('derive', [app('unfold',var(f'ror-{n}'),literal(value))])]
                with self.subTest(count=n,bit=i):
                    verify(t,g,p)

    def test_composition_for_every_immediate_including_wraparound(self):
        t = theory()
        x = var('x')
        for n in range(32):
            m = (n+7) % 32
            expression = app(f'ror-{n}',app(f'ror-{m}',x))
            g,p = export_normalizer(t,expression)
            expected = x if (n+m)%32==0 else app(f'ror-{(n+m)%32}',x)
            self.assertEqual(g[4][2],expected)
            verify(t,g,p)

    def test_distribution_and_cancellation_on_generated_expressions(self):
        rng = random.Random(7)
        t = theory()
        variables = [var('x'),var('y'),var('z')]
        def expr(depth):
            if depth==0:
                return rng.choice(variables + [ZERO])
            if rng.randrange(2):
                return app('xor32',expr(depth-1),expr(depth-1))
            return app(f'ror-{rng.randrange(32)}',expr(depth-1))
        for _ in range(12):
            g,p = export_normalizer(t,expr(2))
            verify(t,g,p)

    def test_rotation_of_symbolic_xor_with_nonzero_constants(self):
        from ode.constant_proof import literal
        t=theory();x=var('x')
        for n in (0,7,8,12,16,31):
            expression=app('xor32',app(f'ror-{n}',app('xor32',x,literal(0xdeadbeef))),
                           app(f'ror-{n}',x))
            g,p=export_normalizer(t,expression)
            expected=((0xdeadbeef>>n)|(0xdeadbeef<<((32-n)%32)))&0xffffffff
            self.assertEqual(g[4][2],literal(expected))
            verify(t,g,p)

    def test_wrong_definition_rejected_after_honest_rehashing(self):
        t = theory()
        g,p = export_normalizer(t,app('ror-7',var('x')))
        rotate = next(d for d in t[4] if d[0]=='ror-7')
        rotate[3][0][2][1] = var('b6')  # output bit 0 reads wrong input bit
        g[2] = hash_of(t)
        p[2] = hash_of(g)
        with self.assertRaises(Reject):
            verify(t,g,p)

    def test_lying_conclusion_rejected(self):
        t,g,p = bundle()
        g[4][2] = literal(1)
        p[2] = hash_of(g)
        with self.assertRaises(Reject):
            verify(t,g,p)

    def test_a_left_rotation_normalizer_cannot_supply_a_proof(self):
        from ode.check import Dag
        original = Dag.rotr
        with patch.object(Dag,'rotr',lambda self,a,n: original(self,a,(-n)%32)):
            with self.assertRaisesRegex(ValueError,'different parity'):
                export_normalizer(theory(),app('ror-7',var('x')))

    def test_bad_counts_and_other_operations_stop_at_the_producer(self):
        for bad in ('(ror-32 x)','(ror-07 x)','(ror--1 x)','(ror-x x)','(add32 x y)'):
            with self.subTest(expression=bad), self.assertRaises(ValueError):
                export_normalizer(theory(),parse(bad))

    def test_independent_file_verification(self):
        script = """
import importlib.abc
import sys
class Block(importlib.abc.MetaPathFinder):
    def find_spec(self,name,path=None,target=None):
        if name in {'ode.check','ode.word','ode.native','ode.xor32_proof','ode.rotate32_proof'}:
            raise ImportError(name)
sys.meta_path.insert(0,Block())
from ode.proof_cli import main
raise SystemExit(main(sys.argv[1:]))
"""
        paths=[str(EXAMPLES/f'rotate32.{k}.sexp') for k in ('theory','goal','proof')]
        p=subprocess.run([sys.executable,'-c',script,*paths],cwd=EXAMPLES.parent.parent,
                         capture_output=True,text=True,timeout=30)
        self.assertEqual(p.returncode,0,p.stdout+p.stderr)
        self.assertIn('ACCEPT',p.stdout)


if __name__ == '__main__':
    unittest.main()
