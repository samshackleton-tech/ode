"""Unbounded ripple-carry numeric correctness and independent small sums."""
from pathlib import Path
import random
import unittest
from ode.canon import canonical_bytes,hash_of,parse
from ode.kernel import Reject,verify
from ode.bit_sum_value_proof import theory as make_theory,artifacts
from ode.ground_proof import prove as prove_ground
from ode.equational_proof import app,var

EXAMPLES=Path(__file__).resolve().parent.parent/'examples'/'proofs'


def bundle():
    return [parse((EXAMPLES/f'bit-sum-value.{k}.sexp').read_bytes()) for k in ('theory','goal','proof')]


def natural(n):
    value=app('zero')
    for _ in range(n):value=app('succ',value)
    return value


def columns(a,b,width):
    result=app('no-columns')
    for i in reversed(range(width)):
        result=app('column',app('bit1' if a&(1<<i) else 'bit0'),
                   app('bit1' if b&(1<<i) else 'bit0'),result)
    return result


class BitSumValueTest(unittest.TestCase):
    def test_theory_and_proof_reproduce(self):
        t,g,p=bundle()
        made=make_theory(parse((EXAMPLES/'bits.theory.sexp').read_bytes()),
                         parse((EXAMPLES/'nat-add.theory.sexp').read_bytes()))
        self.assertEqual(canonical_bytes(t),canonical_bytes(made))
        for expected,actual in zip((g,p),artifacts(t)):
            self.assertEqual(canonical_bytes(expected),canonical_bytes(actual))
        self.assertLess(verify(t,g,p)['work'],20000)

    def test_small_ground_sums_against_independent_integer_addition(self):
        t,_,_=bundle();rng=random.Random(3)
        for width in range(5):
            for _ in range(8):
                a,b,c=rng.randrange(1<<width),rng.randrange(1<<width),rng.randrange(2)
                expression=app('bits-value',app('add-columns',columns(a,b,width),app('bit1' if c else 'bit0')))
                g,p=prove_ground(t,expression,natural(a+b+c))
                verify(t,g,p)

    def reject_definition_change(self,name,change):
        t,g,p=bundle();definition=next(d for d in t[4] if d[0]==name)
        change(definition)
        g[2]=hash_of(t,'theory');p[2]=hash_of(g,'goal')
        with self.assertRaises(Reject):verify(t,g,p)

    def test_final_carry_cannot_be_dropped(self):
        self.reject_definition_change('add-columns',lambda d:d[3][0].__setitem__(2,app('empty')))

    def test_next_column_must_receive_computed_carry(self):
        def change(d):d[3][1][2][2][2]=var('c')
        self.reject_definition_change('add-columns',change)

    def test_numeric_bit_positions_must_double_the_tail_value(self):
        def change(d):d[3][1][2][2]=app('bits-value',var('tail'))
        self.reject_definition_change('bits-value',change)

    def test_second_input_cannot_be_replaced_by_the_first(self):
        def change(d):d[3][1][2][1]=var('a')
        self.reject_definition_change('right-bits',change)

    def test_false_goal_with_current_domain_identity_is_rejected(self):
        t,g,p=bundle()
        g[4][2]=app('bits-value',app('left-bits',var('columns')))
        p[2]=hash_of(g,'goal')
        with self.assertRaises(Reject):verify(t,g,p)


if __name__=='__main__':
    unittest.main()
