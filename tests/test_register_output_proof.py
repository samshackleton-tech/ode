"""Execution-to-normalized-output proofs, including the largest G output."""
from pathlib import Path
import subprocess
import sys
import unittest
from ode.canon import canonical_bytes,hash_of,parse
from ode.kernel import Reject,verify
from ode.register_proof import normalized_output,REGISTERS
from ode.equational_proof import var

EXAMPLES=Path(__file__).resolve().parent.parent/'examples'/'proofs'


def execution():
    t=parse((EXAMPLES/'register.theory.sexp').read_bytes())
    g,p=[parse((EXAMPLES/f'register-g.{k}.sexp').read_bytes()) for k in ('goal','proof')]
    return t,g,p


class RegisterOutputTest(unittest.TestCase):
    def test_every_output_fits_existing_limits(self):
        t,g,p=execution()
        for register in REGISTERS:
            with self.subTest(register=register):
                goal,proof=normalized_output(t,g,p,register)
                self.assertLess(len(canonical_bytes(proof)),1000000)
                result=verify(t,goal,proof)
                if register=='b':
                    self.assertLess(len(canonical_bytes(proof)),850000)
                    self.assertLess(result['work'],740000)
                self.assertEqual(goal[4][1][0],'state-'+register)
                if register in ('x','y'):
                    self.assertEqual(goal[4][2],var(register))

    def test_largest_artifact_reproduces_and_file_verifies(self):
        t,g,p=execution()
        expected=[parse((EXAMPLES/f'register-g-normalized-b.{k}.sexp').read_bytes()) for k in ('goal','proof')]
        for before,after in zip(expected,normalized_output(t,g,p,'b')):
            self.assertEqual(canonical_bytes(before),canonical_bytes(after))
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
            str(EXAMPLES/f'register-g-normalized-b.{k}.sexp') for k in ('goal','proof')]
        result=subprocess.run([sys.executable,'-c',script,*paths],cwd=EXAMPLES.parent.parent,
            capture_output=True,text=True,timeout=30)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        self.assertIn('ACCEPT',result.stdout)

    def test_invalid_execution_proof_cannot_be_laundered(self):
        t,g,p=execution()
        p[4][1][-1][0]=var('invented-rule')
        goal,proof=normalized_output(t,g,p,'x')
        with self.assertRaises(Reject):
            verify(t,goal,proof)

    def test_claiming_different_output_rejected(self):
        t,g,p=execution()
        goal,proof=normalized_output(t,g,p,'a')
        goal[4][1][0]=var('state-b')
        proof[2]=hash_of(goal)
        with self.assertRaises(Reject):
            verify(t,goal,proof)

    def test_unknown_register_stops(self):
        t,g,p=execution()
        with self.assertRaisesRegex(AssertionError,'unknown output'):
            normalized_output(t,g,p,'w0')


if __name__=='__main__':
    unittest.main()
