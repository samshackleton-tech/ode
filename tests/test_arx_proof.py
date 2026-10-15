"""Composed arithmetic proofs; G expressions still have an explicit extraction boundary."""
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch
from ode.canon import canonical_bytes,hash_of,parse
from ode.kernel import Reject,verify
from ode.arx_proof import abstract,export_normalizer,theory as make_theory
from ode.word_literal import literal
from ode.equational_proof import app, var

EXAMPLES=Path(__file__).resolve().parent.parent/'examples'/'proofs'


def bundle():
    return [parse((EXAMPLES/f'arx.{k}.sexp').read_bytes()) for k in ('theory','goal','proof')]


class ExpressionAlgebra:
    """Test-side extraction through the existing evaluator; integers name terms.

    This is a producer of theorem statements, not a proof that those
    statements match the source spec. The kernel checks the statements.
    """
    def __init__(self): self.nodes=[]
    def node(self,t):
        self.nodes.append(t)
        return len(self.nodes)-1
    def const(self,v): return self.node(literal(v))
    def add(self,a,b): return self.node(app('add32',self.nodes[a],self.nodes[b]))
    def xor(self,a,b): return self.node(app('xor32',self.nodes[a],self.nodes[b]))
    def rotr(self,a,n): return self.node(app(f'ror-{n}',self.nodes[a]))


class ArithmeticProofTest(unittest.TestCase):
    def test_artifacts_reproduce(self):
        t,g,p=bundle()
        self.assertEqual(canonical_bytes(t),canonical_bytes(make_theory(
            parse((EXAMPLES/'bits.theory.sexp').read_bytes()))))
        for expected,actual in zip((g,p),export_normalizer(t,g[4][1])):
            self.assertEqual(canonical_bytes(expected),canonical_bytes(actual))
        verify(t,g,p)

    def test_abstraction_shares_opaque_operands(self):
        term=parse('(add32 (ror-8 x) (ror-8 x))')
        params,left,right,args=abstract(term,term,'add32')
        self.assertEqual(len(params),1)
        self.assertEqual(args,[parse('(ror-8 x)')])
        self.assertEqual(left,right)
        self.assertEqual(left,parse('(add32 v0 v0)'))

    def test_all_four_g_output_expressions_fit_existing_kernel_limits(self):
        from ode.word import Evaluator
        t,_,_=bundle()
        spec=parse((EXAMPLES.parent/'blake3-g.sexp').read_bytes())
        algebra=ExpressionAlgebra()
        outputs=Evaluator(algebra).run_spec(spec,{v:algebra.node(var(v)) for v in 'abcdxy'})
        self.assertEqual(len(outputs),4)
        for i in outputs:
            with self.subTest(output=i):
                g,p=export_normalizer(t,algebra.nodes[i])
                self.assertLess(len(canonical_bytes(p)),1000000)
                verify(t,g,p)

    def test_constants_flow_through_all_three_operations(self):
        t,_,_=bundle()
        term=app('xor32',app('ror-7',app('add32',literal(0xffffffff),literal(2))),var('x'))
        g,p=export_normalizer(t,term)
        self.assertEqual(g[4][2],app('xor32',var('x'),literal(1<<25)))
        verify(t,g,p)

    def test_repeated_subexpressions_and_variable_names(self):
        t,_,_=bundle()
        term=parse('(xor32 (ror-8 (add32 v0 x)) (ror-8 (add32 v0 x)))')
        g,p=export_normalizer(t,term)
        self.assertEqual(g[4][2],literal(0))
        verify(t,g,p)

    def test_wrong_normalizer_is_detected(self):
        from ode.check import Dag
        t,_,_=bundle()
        with patch.object(Dag,'add',lambda self,a,b:a):
            with self.assertRaises(ValueError):
                export_normalizer(t,parse('(ror-8 (add32 x y))'))

    def test_changed_outer_goal_is_rejected(self):
        t,g,p=bundle()
        g[4][2]=var('w');p[2]=hash_of(g, 'goal')
        with self.assertRaises(Reject):
            verify(t,g,p)

    def test_unsupported_source_operation_stops(self):
        t,_,_=bundle()
        with self.assertRaisesRegex(AssertionError,'unsupported'):
            export_normalizer(t,parse('(multiply x y)'))

    def test_file_verification_without_arithmetic_producers(self):
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
        paths=[str(EXAMPLES/f'arx.{k}.sexp') for k in ('theory','goal','proof')]
        result=subprocess.run([sys.executable,'-c',script,*paths],cwd=EXAMPLES.parent.parent,
            capture_output=True,text=True,timeout=30)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        self.assertIn('ACCEPT',result.stdout)


if __name__=='__main__':
    unittest.main()
