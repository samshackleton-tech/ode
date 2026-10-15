"""Concrete folding exports, independently checked from bit definitions."""
from pathlib import Path
import random
import subprocess
import sys
import unittest
from unittest.mock import patch

from ode.canon import canonical_bytes, hash_of, parse
from ode.kernel import Reject, verify
from ode.constant_proof import export_normalizer, literal
from ode.ground_proof import prove
from ode.xor32_proof import app, var

EXAMPLES = Path(__file__).resolve().parent.parent / 'examples' / 'proofs'


def theory(name='add32'):
    return parse((EXAMPLES/f'{name}.theory.sexp').read_bytes())


class ConstantProofTest(unittest.TestCase):
    def test_artifact_reproduces_and_verifies_without_producers(self):
        t=theory()
        g,p=[parse((EXAMPLES/f'constant.{k}.sexp').read_bytes()) for k in ('goal','proof')]
        for expected,actual in zip((g,p),export_normalizer(t,g[4][1])):
            self.assertEqual(canonical_bytes(expected),canonical_bytes(actual))
        verify(t,g,p)
        script = """
import importlib.abc
import sys
class Block(importlib.abc.MetaPathFinder):
    def find_spec(self,name,path=None,target=None):
        if name in {'ode.check','ode.word','ode.native','ode.constant_proof',
                    'ode.ground_proof','ode.xor32_proof','ode.rotate32_proof'}:
            raise ImportError(name)
sys.meta_path.insert(0,Block())
from ode.proof_cli import main
raise SystemExit(main(sys.argv[1:]))
"""
        paths=[str(EXAMPLES/'add32.theory.sexp')]+[
            str(EXAMPLES/f'constant.{k}.sexp') for k in ('goal','proof')]
        result=subprocess.run([sys.executable,'-c',script,*paths],
            cwd=EXAMPLES.parent.parent,capture_output=True,text=True,timeout=30)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        self.assertIn('ACCEPT',result.stdout)

    def test_addition_and_xor_exports(self):
        t=theory()
        rng=random.Random(41)
        for a,b in [(0xffffffff,1),(0x80000000,0x80000000),(0,0)]+[
                (rng.getrandbits(32),rng.getrandbits(32)) for _ in range(12)]:
            expression=app('xor32',app('add32',literal(a),literal(b)),literal(a))
            g,p=export_normalizer(t,expression)
            self.assertEqual(g[4][2],literal(((a+b)&0xffffffff)^a))
            verify(t,g,p)

    def test_rotation_exports_every_count(self):
        t=theory('rotate32')
        for n in range(32):
            g,p=export_normalizer(t,app(f'ror-{n}',literal(0xdeadbeef)))
            expected=((0xdeadbeef>>n)|(0xdeadbeef<<((32-n)%32)))&0xffffffff
            self.assertEqual(g[4][2],literal(expected))
            verify(t,g,p)

    def test_broken_old_addition_cannot_obtain_proof(self):
        from ode.check import Dag
        with patch.object(Dag,'add',lambda self,a,b:self.const(7)):
            with self.assertRaisesRegex(AssertionError,'proposed result'):
                export_normalizer(theory(),app('add32',literal(1),literal(2)))

    def test_changed_conclusion_rejected(self):
        t=theory()
        g,p=export_normalizer(t,app('add32',literal(0xffffffff),literal(1)))
        g[4][2]=literal(1)
        p[2]=hash_of(g)
        with self.assertRaises(Reject):
            verify(t,g,p)

    def test_changed_carry_definition_rejected(self):
        t=theory()
        g,p=export_normalizer(t,app('add32',literal(0xffffffff),literal(1)))
        definition=next(d for d in t[4] if d[0]=='carry-bit')
        definition[3][1][2]=app('bit0')
        g[2]=hash_of(t)
        p[2]=hash_of(g)
        with self.assertRaises(Reject):
            verify(t,g,p)

    def test_shared_term_evaluation_reuses_derivations(self):
        t=theory()
        term=app('add32',literal(0xffffffff),literal(1))
        _,single=export_normalizer(t,term)
        g,doubled=export_normalizer(t,app('xor32',term,term))
        self.assertLess(len(doubled[4][1]),2*len(single[4][1]))
        verify(t,g,doubled)

    def test_reproducible(self):
        t=theory()
        term=app('add32',literal(7),literal(19))
        self.assertEqual(canonical_bytes(export_normalizer(t,term)[1]),
                         canonical_bytes(export_normalizer(t,term)[1]))

    def test_contracts_stop_bad_inputs(self):
        for n in (-1,2**32,True):
            with self.assertRaises(AssertionError):
                literal(n)
        for term in (var('x'),app('word32'),app('word32',*[var('b')]*32)):
            with self.assertRaises(AssertionError):
                export_normalizer(theory(),term)
        with self.assertRaisesRegex(AssertionError,'constructor'):
            prove(theory(),app('opaque'),app('opaque'))


if __name__=='__main__':
    unittest.main()
