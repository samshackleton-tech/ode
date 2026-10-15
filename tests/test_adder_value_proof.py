"""The full-adder column's numeric meaning, from shared definitions."""
from pathlib import Path
import unittest
from ode.canon import canonical_bytes,hash_of,parse
from ode.kernel import Reject,verify
from ode.adder_value_proof import artifacts,theory as make_theory
from ode.add32_proof import theory as word_theory
from ode.ground_proof import prove as prove_ground
from ode.equational_proof import app,var

EXAMPLES=Path(__file__).resolve().parent.parent/'examples'/'proofs'


def bundle():
    return [parse((EXAMPLES/f'adder-value.{k}.sexp').read_bytes()) for k in ('theory','goal','proof')]


class AdderValueTest(unittest.TestCase):
    def test_artifacts_reproduce(self):
        t,g,p=bundle()
        made=make_theory(parse((EXAMPLES/'bits.theory.sexp').read_bytes()),
                         parse((EXAMPLES/'nat-add.theory.sexp').read_bytes()))
        self.assertEqual(canonical_bytes(t),canonical_bytes(made))
        for expected,actual in zip((g,p),artifacts(t)):
            self.assertEqual(canonical_bytes(expected),canonical_bytes(actual))
        self.assertLess(verify(t,g,p)['work'],12000)

    def test_exact_shared_word_and_natural_definitions(self):
        t,_,_=bundle()
        word=word_theory(parse((EXAMPLES/'bits.theory.sexp').read_bytes()))
        naturals=parse((EXAMPLES/'nat-add.theory.sexp').read_bytes())
        source={d[0]:d for d in word[4]+naturals[4]}
        for definition in t[4]:
            if definition[0]!='bit-value':
                self.assertEqual(definition,source[definition[0]])

    def test_bit_values_are_exactly_zero_and_one(self):
        t,_,_=bundle()
        for bit,value in (('bit0',app('zero')),('bit1',app('succ',app('zero')))):
            g,p=prove_ground(t,app('bit-value',app(bit)),value)
            verify(t,g,p)

    def test_wrong_carry_definition_rejected(self):
        t,g,p=bundle()
        carry=next(d for d in t[4] if d[0]=='carry-bit')
        carry[3][1][2]=app('bit0')
        g[2]=hash_of(t, 'theory');p[2]=hash_of(g, 'goal')
        with self.assertRaises(Reject):
            verify(t,g,p)

    def test_carry_weight_cannot_drop_from_two_to_one(self):
        t,g,p=bundle()
        g[4][1][2]=g[4][1][2][1]
        p[2]=hash_of(g, 'goal')
        with self.assertRaises(Reject):
            verify(t,g,p)

    def test_missing_input_is_rejected(self):
        t,g,p=bundle()
        g[4][2]=app('add',app('bit-value',var('a')),app('bit-value',var('b')))
        p[2]=hash_of(g, 'goal')
        with self.assertRaises(Reject):
            verify(t,g,p)


if __name__=='__main__':
    unittest.main()
