"""Finite Boolean identities become explicit, independently checked proofs."""
from pathlib import Path
import unittest
from ode.canon import canonical_bytes, hash_of, parse
from ode.kernel import Reject, verify
from ode.boolean_proof import prove
from ode.equational_proof import app, var

EXAMPLES=Path(__file__).resolve().parent.parent/'examples'/'proofs'


class BooleanProofTest(unittest.TestCase):
    def setUp(self):
        self.t=parse((EXAMPLES/'add32.theory.sexp').read_bytes())

    def test_carry_is_symmetric_in_all_three_inputs(self):
        a,b,c=map(var,'abc')
        left=app('carry-bit',a,b,c)
        right=app('carry-bit',c,a,b)
        g,p=prove(self.t,[a,b,c],left,right)
        result=verify(self.t,g,p)
        self.assertEqual(result['lemmas'],22)
        self.assertEqual(canonical_bytes(p),canonical_bytes(prove(self.t,[a,b,c],left,right)[1]))

    def test_full_adder_sum_parity_associativity(self):
        a,b,c,d,e=map(var,'abcde')
        xor=lambda x,y:app('xor-bit',x,y)
        left=xor(xor(xor(a,b),c),xor(d,e))
        right=xor(a,xor(b,xor(c,xor(d,e))))
        g,p=prove(self.t,[a,b,c,d,e],left,right)
        verify(self.t,g,p)

    def test_false_identity_stops_producer(self):
        a,b=map(var,'ab')
        with self.assertRaisesRegex(ValueError,'false constructor'):
            prove(self.t,[a,b],app('xor-bit',a,b),a)

    def test_missing_case_rejected(self):
        a=var('a')
        g,p=prove(self.t,[a],a,a)
        p[4][2].pop()
        with self.assertRaises(Reject):
            verify(self.t,g,p)

    def test_changed_goal_rejected(self):
        a,b=map(var,'ab')
        g,p=prove(self.t,[a,b],app('xor-bit',a,b),app('xor-bit',b,a))
        g[4][2]=a
        p[2]=hash_of(g)
        with self.assertRaises(Reject):
            verify(self.t,g,p)

    def test_a_lying_reduction_table_cannot_change_a_proved_value(self):
        from ode.ground_proof import Evaluation,prove as prove_ground
        term=app('xor-bit',app('bit0'),app('bit0'))
        g,p=prove_ground(self.t,term,app('bit0'))
        lemma=[var('lemma'),g[3],g[4],p[4]]
        reduction=Evaluation(self.t,{canonical_bytes(term):(app('bit1'),0)})
        value,last=reduction.evaluate(term)
        reduction.trans(last,reduction.refl(value))
        goal=[var('goal'),3,hash_of(self.t),[],app('eq',term,value)]
        proof=[var('proof'),3,hash_of(goal),[lemma],[var('derive'),reduction.steps]]
        with self.assertRaises(Reject):
            verify(self.t,goal,proof)

    def test_enumeration_bound_and_duplicate_parameters(self):
        with self.assertRaises(AssertionError):
            prove(self.t,[var(f'b{i}') for i in range(9)],app('bit0'),app('bit0'))
        with self.assertRaises(AssertionError):
            prove(self.t,[var('a'),var('a')],var('a'),var('a'))


if __name__=='__main__':
    unittest.main()
