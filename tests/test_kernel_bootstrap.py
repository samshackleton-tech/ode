"""An adversarial delivery package for the small-kernel fragment checker."""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from ode.canon import canonical_bytes,field,hash_of,parse
from tests.test_game import read_tree,tree_hash

ROOT=Path(__file__).resolve().parent.parent
GAME=ROOT/'game'
EXAMPLES=ROOT/'examples'/'proofs'
BASE=GAME/'kernel-base'
PINS=GAME/'bootstrap'/'kernel-targets'/'RELIANCE'
LAUNCHER=GAME/'bootstrap'/'root'/'launch.py'
FILES=('encoding.theory.sexp','encoding-g.goal.sexp','encoding-g.proof.sexp',
       'encoding-g-execution.goal.sexp','encoding-g-execution.proof.sexp','encoding-g.bin')


class KernelBootstrapTest(unittest.TestCase):
    def run_bob(self,store,base=BASE):
        return subprocess.run([sys.executable,str(LAUNCHER),str(PINS),str(base),str(store),'g-fragment'],
            cwd=store,capture_output=True,text=True,timeout=30)

    def populate(self,store):
        for name in FILES:
            shutil.copy(EXAMPLES/name,store/name)

    def test_package_copies_pins_and_dependency_boundary(self):
        modules=sorted(p.name for p in (BASE/'ode').glob('*.py'))
        self.assertEqual(modules,['__init__.py','canon.py','encoding_cli.py','kernel.py','proof_cli.py','word_literal.py'])
        for name in modules:
            self.assertEqual((BASE/'ode'/name).read_bytes(),(ROOT/'ode'/name).read_bytes())
        pins=parse(PINS.read_bytes())
        self.assertEqual(field(pins,'ode-base'),tree_hash(read_tree(str(BASE))))
        for key,name in (('theory','encoding.theory.sexp'),('encoding-goal','encoding-g.goal.sexp'),
                         ('execution-goal','encoding-g-execution.goal.sexp')):
            self.assertEqual(field(pins,key),hash_of(parse((EXAMPLES/name).read_bytes())))

    def test_honest_control_from_an_unrelated_working_directory(self):
        with tempfile.TemporaryDirectory() as tmp:
            store=Path(tmp);self.populate(store)
            result=self.run_bob(store)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            self.assertTrue(result.stdout.startswith('ACCEPT'),result.stdout)

    def test_alternative_valid_proof_is_accepted(self):
        with tempfile.TemporaryDirectory() as tmp:
            store=Path(tmp);self.populate(store)
            path=store/'encoding-g.proof.sexp';proof=parse(path.read_bytes())
            steps=proof[4][1];n=len(steps)
            steps+=parse(f'((sym {n-1}) (sym {n}))')
            path.write_bytes(canonical_bytes(proof))
            result=self.run_bob(store)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_changed_delivered_checker_is_rejected_before_loading(self):
        with tempfile.TemporaryDirectory() as tmp:
            store=Path(tmp)/'store';store.mkdir();self.populate(store)
            base=Path(tmp)/'base';shutil.copytree(BASE,base)
            with (base/'ode'/'kernel.py').open('a') as stream:
                stream.write('\nraise RuntimeError("MALLORY CODE RAN")\n')
            result=self.run_bob(store,base)
            self.assertEqual(result.returncode,1)
            self.assertIn('REJECT ode-base',result.stdout)
            self.assertNotIn('MALLORY CODE RAN',result.stdout+result.stderr)

    def test_changed_owner_claims_are_rejected_by_pin(self):
        for name,key in (('encoding.theory.sexp','theory'),('encoding-g.goal.sexp','encoding-goal'),
                         ('encoding-g-execution.goal.sexp','execution-goal')):
            with self.subTest(file=name),tempfile.TemporaryDirectory() as tmp:
                store=Path(tmp);self.populate(store)
                value=parse((store/name).read_bytes());value[1]=4
                (store/name).write_bytes(canonical_bytes(value))
                result=self.run_bob(store)
                self.assertEqual(result.returncode,1)
                self.assertIn(f'{key} differs from the owner pin',result.stdout)

    def test_mutated_proof_and_bytes_are_rejected(self):
        for name in ('encoding-g.proof.sexp','encoding-g-execution.proof.sexp','encoding-g.bin'):
            with self.subTest(file=name),tempfile.TemporaryDirectory() as tmp:
                store=Path(tmp);self.populate(store)
                path=store/name
                if name.endswith('.bin'):
                    data=bytearray(path.read_bytes());data[0]^=1;path.write_bytes(data)
                else:
                    proof=parse(path.read_bytes())
                    proof[4][1][-1][0]=parse('invented-rule')
                    path.write_bytes(canonical_bytes(proof))
                result=self.run_bob(store)
                self.assertEqual(result.returncode,1,result.stdout+result.stderr)
                self.assertTrue(result.stdout.startswith('REJECT'),result.stdout)

    def test_missing_artifact_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            store=Path(tmp);self.populate(store)
            (store/'encoding-g.bin').unlink()
            result=self.run_bob(store)
            self.assertEqual(result.returncode,1)
            self.assertTrue(result.stdout.startswith('REJECT'),result.stdout)


if __name__=='__main__':
    unittest.main()
