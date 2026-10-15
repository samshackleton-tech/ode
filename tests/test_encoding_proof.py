"""Declared instruction encodings, byte binding, and separate CPU cross-checks."""
from itertools import product
from pathlib import Path
import random
import subprocess
import sys
import unittest
from ode.canon import canonical_bytes,hash_of,parse
from ode.kernel import Reject,verify
from ode.encoding_cli import check,code_bytes
from ode.encoding_proof import artifacts,theory as make_theory,execution_artifacts
from ode.register_proof import REGISTERS,g_instructions
from ode.equational_proof import app, var
from tests.test_a64 import ADD,EOR,ROR,LDR,STR,RET,enc,ON_A64

EXAMPLES=Path(__file__).resolve().parent.parent/'examples'/'proofs'


def bundle():
    t=parse((EXAMPLES/'encoding.theory.sexp').read_bytes())
    g,p=[parse((EXAMPLES/f'encoding-g.{k}.sexp').read_bytes()) for k in ('goal','proof')]
    return t,g,p


def execution():
    return [parse((EXAMPLES/f'encoding-g-execution.{k}.sexp').read_bytes()) for k in ('goal','proof')]


class EncodingProofTest(unittest.TestCase):
    def test_artifacts_reproduce_and_bind_code(self):
        t,g,p=bundle()
        self.assertEqual(canonical_bytes(t),canonical_bytes(make_theory(
            parse((EXAMPLES/'bits.theory.sexp').read_bytes()),
            parse((EXAMPLES/'g-definition.sexp').read_bytes()))))
        code=(EXAMPLES/'encoding-g.bin').read_bytes()
        words=[int.from_bytes(code[i:i+4],'little') for i in range(0,len(code),4)]
        for expected,actual in zip((g,p),artifacts(t,g_instructions(),words)):
            self.assertEqual(canonical_bytes(expected),canonical_bytes(actual))
        check(t,g,p,*execution(),code)
        self.assertEqual(len(code),56)

    def test_execution_and_encoding_name_the_same_instruction_list(self):
        t,g,p=bundle()
        eg,ep=[parse((EXAMPLES/f'encoding-g-execution.{k}.sexp').read_bytes()) for k in ('goal','proof')]
        for expected,actual in zip((eg,ep),execution_artifacts(t)):
            self.assertEqual(canonical_bytes(expected),canonical_bytes(actual))
        self.assertEqual(g[4][1][1],eg[4][1][1])
        verify(t,eg,ep)

    def test_execution_goal_names_g_for_every_initial_state(self):
        t,_,_=bundle();g,p=execution()
        self.assertEqual(g[3],parse('((s State))'))
        self.assertEqual(g[4][2],parse('(g s)'))
        verify(t,g,p)

    def test_changed_owner_g_definition_cannot_reuse_execution_proof(self):
        t,_,_=bundle();g,p=execution()
        definition=next(d for d in t[4] if d[0]=='g-second')
        definition[3][0][2][2][0]=var('ror-8')  # b's final rotation should be 7
        g[2]=hash_of(t, 'theory');p[2]=hash_of(g, 'goal')
        with self.assertRaises(Reject):
            verify(t,g,p)

    def test_binary_instruction_fields_against_existing_encoders(self):
        t,_,_=bundle()
        for name,encoder in (('add',ADD),('xor',EOR)):
            for d,a,b in product(range(6),repeat=3):
                instruction=app(name+'-register',*[app('reg-'+REGISTERS[i]) for i in (d,a,b)])
                g,p=artifacts(t,[instruction],[encoder(d+3,a+3,b+3)])
                verify(t,g,p)

    def test_all_rotation_counts_and_aliasing(self):
        t,_,_=bundle()
        for n in range(32):
            for source in (0,1):
                instruction=app(f'rotate-register-{n}',app('reg-a'),app('reg-'+REGISTERS[source]))
                g,p=artifacts(t,[instruction],[ROR(3,source+3,n)])
                verify(t,g,p)

    def test_each_changed_code_byte_is_rejected(self):
        t,g,p=bundle();code=(EXAMPLES/'encoding-g.bin').read_bytes()
        for i in range(len(code)):
            mutant=bytearray(code);mutant[i]^=1
            with self.assertRaisesRegex(Reject,'code bytes differ'):
                check(t,g,p,*execution(),bytes(mutant))
        for mutant in (code[:-1],code+b'\0'):
            with self.assertRaises(Reject):
                check(t,g,p,*execution(),mutant)

    def test_changed_register_encoding_rejected(self):
        t,g,p=bundle()
        bit=next(d for d in t[4] if d[0]=='register-bit-0')
        bit[3][0][2]=app('bit0')
        g[2]=hash_of(t, 'theory');p[2]=hash_of(g, 'goal')
        with self.assertRaises(Reject):
            verify(t,g,p)

    def test_valid_proofs_for_different_programs_are_rejected(self):
        from ode.register_proof import prove_execution,initial_state
        t,g,p=bundle()
        eg,ep=prove_execution(t,[],initial_state())
        verify(t,eg,ep)  # A valid theorem, for the wrong instruction list.
        with self.assertRaisesRegex(Reject,'different programs'):
            check(t,g,p,eg,ep,(EXAMPLES/'encoding-g.bin').read_bytes())

    def test_invalid_execution_proof_is_rejected_by_byte_binding(self):
        t,g,p=bundle();eg,ep=execution()
        ep[4][2][0][2][-1][0]=var('invented-rule')
        with self.assertRaises(Reject):
            check(t,g,p,eg,ep,(EXAMPLES/'encoding-g.bin').read_bytes())

    def test_nonliteral_word_lists_are_rejected(self):
        for value in (var('words'),app('instruction-word'),app('instruction-word',var('x'),app('no-words'))):
            with self.assertRaises(ValueError):
                code_bytes(value)

    def test_file_binding_needs_no_encoding_producer(self):
        script='''
import importlib.abc
import sys
class Block(importlib.abc.MetaPathFinder):
    def find_spec(self,name,path=None,target=None):
        if name.startswith('ode.') and (name.endswith('_proof') or name in
                {'ode.check','ode.word','ode.a64','ode.native','ode.proof_library','ode.proof_slice'}):
            raise ImportError(name)
sys.meta_path.insert(0,Block())
from ode.encoding_cli import main
raise SystemExit(main(sys.argv[1:]))
'''
        paths=[str(EXAMPLES/'encoding.theory.sexp')]+[
            str(EXAMPLES/f'encoding-g.{k}') for k in ('goal.sexp','proof.sexp')]+[
            str(EXAMPLES/f'encoding-g-execution.{k}.sexp') for k in ('goal','proof')]+[str(EXAMPLES/'encoding-g.bin')]
        result=subprocess.run([sys.executable,'-c',script,*paths],cwd=EXAMPLES.parent.parent,
            capture_output=True,text=True,timeout=30)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        self.assertIn('ACCEPT',result.stdout)

    @unittest.skipUnless(ON_A64,'requires aarch64 Linux CPU')
    def test_fragment_matches_existing_g_spec_on_cpu(self):
        from ode.native import Function
        from ode.word import Concrete,Evaluator
        code=(EXAMPLES/'encoding-g.bin').read_bytes()
        wrapper=enc([LDR(i+3,0,i) for i in range(6)])+code+enc([STR(i+3,1,i) for i in range(6)]+[RET])
        function=Function(wrapper,6,6,0)
        spec=parse((EXAMPLES.parent/'blake3-g.sexp').read_bytes())
        rng=random.Random(56)
        samples=[[0]*6,[0xffffffff]*6]+[[rng.getrandbits(32) for _ in range(6)] for _ in range(100)]
        for values in samples:
            expected=Evaluator(Concrete()).run_spec(spec,dict(zip(REGISTERS,values)))+values[4:]
            self.assertEqual(function(values),expected)


if __name__=='__main__':
    unittest.main()
