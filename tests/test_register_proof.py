"""Abstract register execution proofs and source/algebra cross-checks."""
from itertools import product
from pathlib import Path
import subprocess
import sys
import unittest
from ode.canon import canonical_bytes,hash_of,parse
from ode.kernel import Reject,verify
from ode.register_proof import (REGISTERS,theory as make_theory,prove_execution,
                                g_instructions,g_state,initial_state)
from ode.xor32_proof import app,var

EXAMPLES=Path(__file__).resolve().parent.parent/'examples'/'proofs'


def bundle():
    t=parse((EXAMPLES/'register.theory.sexp').read_bytes())
    g,p=[parse((EXAMPLES/f'register-g.{k}.sexp').read_bytes()) for k in ('goal','proof')]
    return t,g,p


class RegisterProofTest(unittest.TestCase):
    def test_artifacts_reproduce(self):
        t,g,p=bundle()
        self.assertEqual(canonical_bytes(t),canonical_bytes(make_theory(
            parse((EXAMPLES/'bits.theory.sexp').read_bytes()))))
        for expected,actual in zip((g,p),prove_execution(t,g_instructions(),g_state())):
            self.assertEqual(canonical_bytes(expected),canonical_bytes(actual))
        result=verify(t,g,p)
        self.assertLess(result['work'],100000)
        self.assertEqual(result['lemmas'],0)

    def test_every_binary_register_alias_pattern(self):
        t,_,_=bundle()
        for op in ('add','xor'):
            for d,a,b in product(REGISTERS,repeat=3):
                instruction=app(op+'-register',app('reg-'+d),app('reg-'+a),app('reg-'+b))
                values=[app(op+'32',var(a),var(b)) if r==d else var(r) for r in REGISTERS]
                g,p=prove_execution(t,[instruction],app('state',*values))
                verify(t,g,p)

    def test_rotation_aliasing_and_all_counts(self):
        t,_,_=bundle()
        for n in range(32):
            for source in ('a','b'):
                instruction=app(f'rotate-register-{n}',app('reg-a'),app('reg-'+source))
                expected=app('state',app(f'ror-{n}',var(source)),*[var(r) for r in REGISTERS[1:]])
                g,p=prove_execution(t,[instruction],expected)
                verify(t,g,p)

    def test_empty_program_preserves_state(self):
        t,_,_=bundle()
        g,p=prove_execution(t,[],initial_state())
        verify(t,g,p)

    def test_expected_g_equations_match_existing_spec_extraction(self):
        from tests.test_arx_proof import ExpressionAlgebra
        from ode.word import Evaluator
        algebra=ExpressionAlgebra()
        spec=parse((EXAMPLES.parent/'blake3-g.sexp').read_bytes())
        outputs=Evaluator(algebra).run_spec(spec,{r:algebra.node(var(r)) for r in REGISTERS})
        self.assertEqual([algebra.nodes[i] for i in outputs],g_state()[1:5])

    def test_wrong_destination_semantics_rejected(self):
        t,g,p=bundle()
        step=next(d for d in t[4] if d[0]=='step')
        step[3][0][2][1]=var('b')
        g[2]=hash_of(t);p[2]=hash_of(g)
        with self.assertRaises(Reject):
            verify(t,g,p)

    def test_skipping_instruction_semantics_rejected(self):
        t,g,p=bundle()
        run=next(d for d in t[4] if d[0]=='run')
        run[3][1][2]=app('run',var('tail'),var('s'))
        g[2]=hash_of(t);p[2]=hash_of(g)
        with self.assertRaises(Reject):
            verify(t,g,p)

    def test_changed_instruction_order_rejected(self):
        t,g,p=bundle()
        program=g[4][1][1]
        program[1],program[2][1]=program[2][1],program[1]
        p[2]=hash_of(g)
        with self.assertRaises(Reject):
            verify(t,g,p)

    def test_changed_preserved_register_rejected(self):
        t,g,p=bundle()
        g[4][2][5]=var('a')
        p[2]=hash_of(g)
        with self.assertRaises(Reject):
            verify(t,g,p)

    def test_file_verification_without_producers_or_old_executor(self):
        script='''
import importlib.abc
import sys
class Block(importlib.abc.MetaPathFinder):
    def find_spec(self,name,path=None,target=None):
        if name.startswith('ode.') and (name.endswith('_proof') or name in
                {'ode.check','ode.word','ode.a64','ode.native','ode.proof_library','ode.proof_slice'}):
            raise ImportError(name)
sys.meta_path.insert(0,Block())
from ode.proof_cli import main
raise SystemExit(main(sys.argv[1:]))
'''
        paths=[str(EXAMPLES/'register.theory.sexp')]+[
            str(EXAMPLES/f'register-g.{k}.sexp') for k in ('goal','proof')]
        result=subprocess.run([sys.executable,'-c',script,*paths],cwd=EXAMPLES.parent.parent,
            capture_output=True,text=True,timeout=30)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        self.assertIn('ACCEPT',result.stdout)


if __name__=='__main__':
    unittest.main()
