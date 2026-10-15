"""A real author-supplied carry argument completes a requested arithmetic proof."""
from pathlib import Path
import subprocess
import sys
import unittest
from ode.canon import canonical_bytes,hash_of,parse
from ode.kernel import Reject,verify
from ode.complement_proof import artifacts,residual_artifacts
from ode.equation_proof import NeedProof,produce
from ode.xor32_proof import app,var

ROOT=Path(__file__).resolve().parent.parent
EXAMPLES=ROOT/'examples'/'proofs'


def read(name,kind):
    return parse((EXAMPLES/f'{name}.{kind}.sexp').read_bytes())


class ComplementProofTest(unittest.TestCase):
    def setUp(self):
        self.t=read('arx','theory')

    def test_complement_lemma_is_independently_checked(self):
        g,p=artifacts(self.t)
        self.assertEqual(g,read('complement','goal'))
        verify(self.t,g,p)

    def test_exact_request_answer_and_final_proof_reproduce(self):
        g,p=read('complement','goal'),read('complement','proof')
        with self.assertRaises(NeedProof) as context:
            produce(self.t,g)
        rg,rp=residual_artifacts(self.t)
        self.assertEqual(rg,context.exception.goal)
        self.assertEqual(canonical_bytes(rg),canonical_bytes(read('complement-residual','goal')))
        self.assertEqual(canonical_bytes(rp),canonical_bytes(read('complement-residual','proof')))
        self.assertEqual(canonical_bytes(p),canonical_bytes(produce(self.t,g,rp)))
        result=verify(self.t,g,p)
        self.assertLess(result['work'],400000)
        self.assertLess(len(canonical_bytes(p)),450000)

    def test_real_cli_handoff(self):
        command=[sys.executable,'-m','ode.equation_cli',str(EXAMPLES/'arx.theory.sexp'),
                 str(EXAMPLES/'complement.goal.sexp')]
        request=subprocess.run(command,cwd=ROOT,capture_output=True,text=True,timeout=30)
        self.assertEqual(request.returncode,2,request.stderr)
        self.assertEqual(parse(request.stdout),read('complement-residual','goal'))
        completed=subprocess.run(command+[str(EXAMPLES/'complement-residual.proof.sexp')],
            cwd=ROOT,capture_output=True,text=True,timeout=30)
        self.assertEqual(completed.returncode,0,completed.stderr)
        verify(self.t,read('complement','goal'),parse(completed.stdout))

    def test_changed_boolean_carry_semantics_rejects_the_author_proof(self):
        g,p=artifacts(self.t)
        carry=next(d for d in self.t[4] if d[0]=='carry-bit')
        carry[3][0][2]=app('bit1')
        g[2]=hash_of(self.t);p[2]=hash_of(g)
        with self.assertRaises(Reject):
            verify(self.t,g,p)

    def test_corrupted_author_answer_is_rejected_after_composition(self):
        g=read('complement','goal');hint=read('complement-residual','proof')
        hint[4][1][-1][0]=var('invented-rule')
        proof=produce(self.t,g,hint)
        with self.assertRaises(Reject):
            verify(self.t,g,proof)


if __name__=='__main__':
    unittest.main()
