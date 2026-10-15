"""Unbounded register-program loops and their explicit instruction semantics."""
from pathlib import Path
import unittest
from ode.canon import canonical_bytes,hash_of,parse
from ode.kernel import Reject,verify
from ode.register_loop_proof import theory as make_theory,iteration_artifacts,batching_artifacts
from ode.register_proof import g_instructions,program,initial_state,REGISTERS
from ode.equational_proof import app, var

EXAMPLES=Path(__file__).resolve().parent.parent/'examples'/'proofs'


def bundle(name):
    t=parse((EXAMPLES/'register-loop.theory.sexp').read_bytes())
    g,p=[parse((EXAMPLES/f'{name}.{k}.sexp').read_bytes()) for k in ('goal','proof')]
    return t,g,p


class RegisterLoopTest(unittest.TestCase):
    def test_artifacts_reproduce(self):
        for name,maker,rules in (('register-iterate',iteration_artifacts,38),('register-batch',batching_artifacts,47)):
            t,g,p=bundle(name)
            self.assertEqual(canonical_bytes(t),canonical_bytes(make_theory(
                parse((EXAMPLES/'bits.theory.sexp').read_bytes()))))
            for expected,actual in zip((g,p),maker(t)):
                self.assertEqual(canonical_bytes(expected),canonical_bytes(actual))
            result=verify(t,g,p)
            self.assertEqual(result['rules'],rules)

    def test_general_batching_instantiates_to_g(self):
        from ode.proof_library import Library
        from ode.ground_proof import substitute
        t,g,p=bundle('register-batch');lib=Library(hash_of(t, 'theory'));index=lib.include(g,p)
        inputs=initial_state();code=program(g_instructions())
        count=app('succ',app('succ',app('zero')))
        eq=substitute(g[4],{var('n'):count,var('p'):code,var('s'):inputs})
        goal=[var('goal'),3,hash_of(t, 'theory'),[[var(r),var('Word32')] for r in REGISTERS],eq]
        proof=[var('proof'),3,hash_of(goal, 'goal'),lib.lemmas,
               app('derive',[app('lemma',index,count,code,inputs)])]
        verify(t,goal,proof)

    def test_count_doubling_cannot_be_replaced_by_incrementing(self):
        t,g,p=bundle('register-batch')
        definition=next(d for d in t[4] if d[0]=='double')
        definition[3][1][2]=app('succ',app('double',var('k')))
        g[2]=hash_of(t, 'theory');p[2]=hash_of(g, 'goal')
        with self.assertRaises(Reject):
            verify(t,g,p)

    def test_wrong_batch_count_rejected(self):
        t,g,p=bundle('register-batch')
        g[4][1][1]=var('n');p[2]=hash_of(g, 'goal')
        with self.assertRaises(Reject):
            verify(t,g,p)

    def test_omitted_repetition_rejected(self):
        t,g,p=bundle('register-iterate')
        definition=next(d for d in t[4] if d[0]=='repeat-program')
        definition[3][1][2]=app('repeat-program',var('k'),var('p'))
        g[2]=hash_of(t, 'theory');p[2]=hash_of(g, 'goal')
        with self.assertRaises(Reject):
            verify(t,g,p)

    def test_missing_base_case_rejected(self):
        t,g,p=bundle('register-batch')
        p[4][2].pop(0)
        with self.assertRaises(Reject):
            verify(t,g,p)


if __name__=='__main__':
    unittest.main()
