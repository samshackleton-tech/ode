"""Word32 associativity and the finite carry invariants it depends on."""
from pathlib import Path
import subprocess
import sys
import unittest

from ode.canon import canonical_bytes,hash_of,parse
from ode.kernel import Reject,verify
from ode.add_associativity_proof import artifacts
from ode.carry_proof import artifacts as carry_artifacts
from ode.equational_proof import app, var

EXAMPLES=Path(__file__).resolve().parent.parent/'examples'/'proofs'


def bundle():
    t=parse((EXAMPLES/'add32.theory.sexp').read_bytes())
    g,p=[parse((EXAMPLES/f'add32-assoc.{k}.sexp').read_bytes()) for k in ('goal','proof')]
    return t,g,p


class AssociativityTest(unittest.TestCase):
    def test_reproducible_and_within_existing_limits(self):
        t,g,p=bundle()
        for expected,actual in zip((g,p),artifacts(t)):
            self.assertEqual(canonical_bytes(expected),canonical_bytes(actual))
        result=verify(t,g,p)
        self.assertLess(result['work'],465000)
        self.assertLess(len(canonical_bytes(p)),520000)

    def test_all_six_boolean_carry_relations_check_independently(self):
        t,_,_=bundle()
        for name,g,p in carry_artifacts(t):
            with self.subTest(relation=name):
                verify(t,g,p)

    def test_mutated_carry_semantics_rejected(self):
        t,g,p=bundle()
        carry=next(d for d in t[4] if d[0]=='carry-bit')
        carry[3][1][2]=app('and-bit',var('b'),var('c'))
        g[2]=hash_of(t, 'theory')
        p[2]=hash_of(g, 'goal')
        with self.assertRaises(Reject):
            verify(t,g,p)

    def test_missing_boolean_case_rejected(self):
        t,g,p=bundle()
        lemma=next(l for l in p[3] if l[3][0]=='induct' and len(l[1])==5)
        lemma[3][2].pop()
        with self.assertRaises(Reject):
            verify(t,g,p)

    def test_dropped_operand_rejected(self):
        t,g,p=bundle()
        g[4][2]=app('add32',var('x'),var('y'))
        p[2]=hash_of(g, 'goal')
        with self.assertRaises(Reject):
            verify(t,g,p)

    def test_low_work_budget_stops(self):
        t,g,p=bundle()
        with self.assertRaisesRegex(Reject,'work budget'):
            verify(t,g,p,work=100000)

    def test_fresh_process_checks_without_producers(self):
        script='''
import importlib.abc
import sys
class Block(importlib.abc.MetaPathFinder):
    def find_spec(self,name,path=None,target=None):
        if name in {'ode.check','ode.word','ode.native','ode.add32_proof',
                    'ode.add_associativity_proof','ode.boolean_proof','ode.ground_proof',
                    'ode.carry_proof','ode.xor32_proof','ode.proof_slice'}:
            raise ImportError(name)
sys.meta_path.insert(0,Block())
from ode.proof_cli import main
raise SystemExit(main(sys.argv[1:]))
'''
        paths=[str(EXAMPLES/'add32.theory.sexp')]+[
            str(EXAMPLES/f'add32-assoc.{k}.sexp') for k in ('goal','proof')]
        result=subprocess.run([sys.executable,'-c',script,*paths],
            cwd=EXAMPLES.parent.parent,capture_output=True,text=True,timeout=30)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        self.assertIn('ACCEPT',result.stdout)


if __name__=='__main__':
    unittest.main()
