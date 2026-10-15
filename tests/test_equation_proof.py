"""Author assistance uses ordinary residual goals and fully checked hints."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
from ode.canon import canonical_bytes,hash_of,parse
from ode.kernel import Reject,verify
from ode.equation_proof import NeedProof,produce
from ode.xor32_proof import ZERO,app,prove as prove_xor,var
from ode.word_literal import literal

ROOT=Path(__file__).resolve().parent.parent
EXAMPLES=ROOT/'examples'/'proofs'


def theory():
    return parse((EXAMPLES/'arx.theory.sexp').read_bytes())


def goal(t,left,right,names=('x','y')):
    return [var('goal'),3,hash_of(t),[[var(n),var('Word32')] for n in names],app('eq',left,right)]


class EquationProofTest(unittest.TestCase):
    def test_proves_a_requested_equation(self):
        t=theory()
        g=goal(t,parse('(add32 (add32 x y) x)'),parse('(add32 x (add32 x y))'))
        verify(t,g,produce(t,g))

    def test_both_sides_share_compound_operand_identities(self):
        t=theory()
        g=goal(t,parse('(add32 (ror-8 x) (ror-8 y))'),parse('(add32 (ror-8 y) (ror-8 x))'))
        verify(t,g,produce(t,g))

    def test_parameter_order_and_unused_parameters_are_preserved(self):
        t=theory()
        g=goal(t,parse('(xor32 x y)'),parse('(xor32 y x)'),('y','unused','x'))
        proof=produce(t,g)
        self.assertEqual(proof[2],hash_of(g))
        verify(t,g,proof)

    def test_author_receives_the_simplified_direct_equation(self):
        from ode.complement_proof import artifacts
        t=theory();x=var('x');ones=literal(0xffffffff)
        total=app('add32',x,app('xor32',x,ones))
        g=goal(t,app('add32',ZERO,total),ones,('x',))
        with self.assertRaises(NeedProof) as context:
            produce(t,g)
        hint_goal,hint=artifacts(t)
        self.assertEqual(context.exception.goal,hint_goal)
        self.assertEqual(hint_goal[4],app('eq',total,ones))
        verify(t,g,produce(t,g,hint))

    def test_unresolved_true_identity_requests_a_goal_without_claiming_falsehood(self):
        t=theory();x=var('x');ones=literal(0xffffffff)
        g=goal(t,app('add32',x,app('xor32',x,ones)),ones,('x',))
        with self.assertRaises(NeedProof) as context:
            produce(t,g)
        residual=context.exception.goal
        self.assertEqual(residual[:4],g[:4])
        self.assertEqual(residual,g)

    def test_checked_author_hint_finishes_a_missed_rewrite(self):
        from ode.check import Dag
        # A semantically correct but weaker producer keeps XOR syntax.
        # The author supplies the missing cancellation proof independently.
        def unsimplified(dag,a,b):
            return dag._intern(('xor',(a,b),0))
        t=theory();g=goal(t,parse('(xor32 x y)'),parse('(xor32 y x)'))
        with patch.object(Dag,'xor',unsimplified):
            with self.assertRaises(NeedProof) as context:
                produce(t,g)
            residual=context.exception.goal
            hint_goal,hint=prove_xor(t,residual[3],*residual[4][1:])
            self.assertEqual(hint_goal,residual)
            proof=produce(t,g,hint)
        verify(t,g,proof)

    def test_false_hint_is_not_an_axiom(self):
        t=theory();g=goal(t,var('x'),var('y'))
        with self.assertRaises(NeedProof) as context:
            produce(t,g)
        residual=context.exception.goal
        hint=[var('proof'),3,hash_of(residual),[],app('derive',[app('refl',ZERO)])]
        proof=produce(t,g,hint)
        with self.assertRaises(Reject):
            verify(t,g,proof)

    def test_hint_for_a_different_goal_stops(self):
        t=theory();g=goal(t,var('x'),var('y'))
        hint=[var('proof'),3,hash_of(t),[],app('derive',[app('refl',var('x'))])]
        with self.assertRaisesRegex(AssertionError,'different goal'):
            produce(t,g,hint)

    def test_cli_request_and_false_hint_have_distinct_statuses(self):
        t=theory();g=goal(t,var('x'),var('y'))
        with tempfile.TemporaryDirectory() as tmp:
            d=Path(tmp)
            (d/'theory').write_bytes(canonical_bytes(t));(d/'goal').write_bytes(canonical_bytes(g))
            command=[sys.executable,'-m','ode.equation_cli',str(d/'theory'),str(d/'goal')]
            request=subprocess.run(command,cwd=ROOT,capture_output=True,text=True,timeout=30)
            self.assertEqual(request.returncode,2,request.stderr)
            residual=parse(request.stdout)
            self.assertEqual(residual[0],'goal')
            self.assertIn('NEEDS PROOF',request.stderr)
            hint=[var('proof'),3,hash_of(residual),[],app('derive',[app('refl',ZERO)])]
            (d/'hint').write_bytes(canonical_bytes(hint))
            rejected=subprocess.run(command+[str(d/'hint')],cwd=ROOT,capture_output=True,text=True,timeout=30)
            self.assertEqual(rejected.returncode,1)
            self.assertEqual(rejected.stdout,'')
            self.assertIn('REJECT',rejected.stderr)

    def test_cli_checks_before_emitting_a_successful_proof(self):
        t=theory();g=goal(t,parse('(xor32 x y)'),parse('(xor32 y x)'))
        with tempfile.TemporaryDirectory() as tmp:
            d=Path(tmp)
            (d/'theory').write_bytes(canonical_bytes(t));(d/'goal').write_bytes(canonical_bytes(g))
            result=subprocess.run([sys.executable,'-m','ode.equation_cli',str(d/'theory'),str(d/'goal')],
                cwd=ROOT,capture_output=True,text=True,timeout=30)
            self.assertEqual(result.returncode,0,result.stderr)
            verify(t,g,parse(result.stdout))
            self.assertIn('PROVED',result.stderr)


if __name__=='__main__':
    unittest.main()
