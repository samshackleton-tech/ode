"""Actual Dag addition exports: multiplicity, reassociation, and zero."""
from pathlib import Path
import random
import subprocess
import sys
import unittest
from unittest.mock import patch
from ode.canon import canonical_bytes,hash_of,parse
from ode.kernel import Reject,verify
from ode.add_normalizer_proof import export_normalizer,prove
from ode.constant_proof import literal
from ode.xor32_proof import ZERO,app,var

EXAMPLES=Path(__file__).resolve().parent.parent/'examples'/'proofs'


def theory():
    return parse((EXAMPLES/'add32.theory.sexp').read_bytes())


class AdditionNormalizerTest(unittest.TestCase):
    def test_artifact_reproduces(self):
        t=theory()
        g,p=[parse((EXAMPLES/f'add32-normalize.{k}.sexp').read_bytes()) for k in ('goal','proof')]
        for expected,actual in zip((g,p),export_normalizer(t,g[4][1])):
            self.assertEqual(canonical_bytes(expected),canonical_bytes(actual))
        verify(t,g,p)

    def test_repeated_operands_remain(self):
        x=var('x');t=theory()
        term=app('add32',x,x)
        g,p=export_normalizer(t,term)
        self.assertEqual(g[4][2],term)
        verify(t,g,p)
        with self.assertRaisesRegex(ValueError,'multisets'):
            prove(t,[[x,var('Word32')]],term,ZERO)

    def test_zero_elimination_and_random_trees(self):
        rng=random.Random(64);t=theory()
        def tree(depth):
            if depth==0:
                return rng.choice([ZERO,var('x'),var('y'),var('z')])
            return app('add32',tree(depth-1),tree(depth-1))
        for term in [app('add32',ZERO,var('x')),app('add32',var('x'),ZERO),
                     app('add32',ZERO,ZERO)]+[tree(2) for _ in range(8)]:
            g,p=export_normalizer(t,term)
            verify(t,g,p)

    def test_wrong_old_normalizer_cannot_get_proof(self):
        from ode.check import Dag
        with patch.object(Dag,'add',lambda self,a,b:a):
            with self.assertRaisesRegex(ValueError,'multisets'):
                export_normalizer(theory(),app('add32',var('x'),var('y')))

    def test_changed_output_rejected(self):
        t=theory()
        g,p=export_normalizer(t,parse('(add32 (add32 x y) (add32 z x))'))
        g[4][2]=var('x');p[2]=hash_of(g)
        with self.assertRaises(Reject):
            verify(t,g,p)

    def test_mixed_constant_folding_including_overflow_to_zero(self):
        t=theory();x=var('x');y=var('y')
        for a,b in ((1,2),(0xffffffff,1),(0xffffffff,2),(0x80000000,0x80000000)):
            with self.subTest(a=a,b=b):
                expression=app('add32',app('add32',x,literal(a)),app('add32',y,literal(b)))
                g,p=export_normalizer(t,expression)
                verify(t,g,p)
                total=(a+b)&0xffffffff
                tail=app('add32',y,literal(total)) if total else y
                self.assertEqual(g[4][2],app('add32',x,tail))

    def test_wrong_constant_component_cannot_obtain_proof(self):
        from ode.check import Dag
        original=Dag.add
        def broken(dag,a,b):
            result=original(dag,a,b)
            node=dag.nodes[result]
            if node[0]=='add' and node[2]:
                return dag._intern(('add',node[1],node[2]^1))
            return result
        with patch.object(Dag,'add',broken):
            with self.assertRaisesRegex(ValueError,'multisets'):
                export_normalizer(theory(),app('add32',var('x'),literal(9)))

    def test_fresh_process_verifies_without_producers(self):
        script='''
import importlib.abc
import sys
class Block(importlib.abc.MetaPathFinder):
    def find_spec(self,name,path=None,target=None):
        if name.startswith('ode.') and (name.endswith('_proof') or name in
                {'ode.check','ode.word','ode.native','ode.proof_library','ode.proof_slice'}):
            raise ImportError(name)
sys.meta_path.insert(0,Block())
from ode.proof_cli import main
raise SystemExit(main(sys.argv[1:]))
'''
        paths=[str(EXAMPLES/'add32.theory.sexp')]+[
            str(EXAMPLES/f'add32-normalize.{k}.sexp') for k in ('goal','proof')]
        result=subprocess.run([sys.executable,'-c',script,*paths],cwd=EXAMPLES.parent.parent,
            capture_output=True,text=True,timeout=30)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        self.assertIn('ACCEPT',result.stdout)


if __name__=='__main__':
    unittest.main()
