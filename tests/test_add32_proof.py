"""Ripple-carry commutativity and ground semantic checks through the kernel."""
from pathlib import Path
import random
import unittest

from ode.canon import canonical_bytes, hash_of, parse
from ode.kernel import Reject, verify
from ode.add32_proof import artifacts, identity_artifacts, theory as make_theory
from ode.xor32_proof import app, var
from ode.ground_proof import prove as ground_proof
from ode.word_literal import literal

EXAMPLES = Path(__file__).resolve().parent.parent / 'examples' / 'proofs'


def bundle():
    return [parse((EXAMPLES/f'add32.{k}.sexp').read_bytes()) for k in ('theory','goal','proof')]




class AdditionProofTest(unittest.TestCase):
    def test_artifacts_reproduce(self):
        t,g,p=bundle()
        self.assertEqual(canonical_bytes(t),canonical_bytes(make_theory(
            parse((EXAMPLES/'bits.theory.sexp').read_bytes()))))
        for expected,actual in zip((g,p),artifacts(t)):
            self.assertEqual(canonical_bytes(expected),canonical_bytes(actual))
        result=verify(t,g,p)
        self.assertEqual(result['lemmas'],104)
        self.assertLess(result['work'],300000)

    def test_universal_zero_identity_reproduces(self):
        t,_,_=bundle()
        g,p=[parse((EXAMPLES/f'add32-zero.{k}.sexp').read_bytes()) for k in ('goal','proof')]
        for expected,actual in zip((g,p),identity_artifacts(t)):
            self.assertEqual(canonical_bytes(expected),canonical_bytes(actual))
        verify(t,g,p)

    def test_zero_identity_rejects_nonzero_initial_carry(self):
        t,_,_=bundle()
        g,p=identity_artifacts(t)
        definition=next(d for d in t[4] if d[0]=='carry-0')
        definition[3][0][2]=app('bit1')
        g[2]=hash_of(t)
        p[2]=hash_of(g)
        with self.assertRaises(Reject):
            verify(t,g,p)

    def test_zero_identity_cannot_claim_x_plus_one_equals_x(self):
        t,_,_=bundle()
        g,p=identity_artifacts(t)
        g[4][1][2]=literal(1)
        p[2]=hash_of(g)
        with self.assertRaises(Reject):
            verify(t,g,p)

    def test_ground_sums_pin_carry_direction_and_modular_overflow(self):
        t,_,_=bundle()
        rng=random.Random(32)
        pairs=[(0,0),(0,0xffffffff),(0xffffffff,1),(0xffffffff,0xffffffff),
               (0x7fffffff,1),(0x80000000,0x80000000),(0xaaaaaaaa,0x55555555)]
        pairs += [((1<<i)-1,1) for i in range(1,32)]
        pairs += [(rng.getrandbits(32),rng.getrandbits(32)) for _ in range(8)]
        for a,b in pairs:
            with self.subTest(a=a,b=b):
                g,p=ground_proof(t,app('add32',literal(a),literal(b)),literal((a+b)&0xffffffff))
                verify(t,g,p)

    def test_every_boolean_carry_input(self):
        t,_,_=bundle()
        for a in range(2):
            for b in range(2):
                for c in range(2):
                    bit=lambda n: app('bit1' if n else 'bit0')
                    g,p=ground_proof(t,app('carry-bit',bit(a),bit(b),bit(c)),bit(a+b+c>=2))
                    verify(t,g,p)

    def test_asymmetric_carry_definition_rejected(self):
        t,g,p=bundle()
        carry=next(d for d in t[4] if d[0]=='carry-bit')
        carry[3][0][2]=var('b')
        g[2]=hash_of(t)
        p[2]=hash_of(g)
        with self.assertRaises(Reject):
            verify(t,g,p)

    def test_wrong_carry_stage_rejected(self):
        t,g,p=bundle()
        carry=next(d for d in t[4] if d[0]=='carry-16')
        carry[3][0][2][3][0]=var('carry-14')
        g[2]=hash_of(t)
        p[2]=hash_of(g)
        with self.assertRaises(Reject):
            verify(t,g,p)

    def test_wrong_sum_bit_rejected(self):
        t,g,p=bundle()
        add=next(d for d in t[4] if d[0]=='add32')
        add[3][0][2][17]=app('bit0')
        g[2]=hash_of(t)
        p[2]=hash_of(g)
        with self.assertRaises(Reject):
            verify(t,g,p)

    def test_lying_goal_rejected(self):
        t,g,p=bundle()
        g[4][2]=var('x')
        p[2]=hash_of(g)
        with self.assertRaises(Reject):
            verify(t,g,p)


if __name__=='__main__':
    unittest.main()
