"""Dependency slicing preserves checked statements and bounds references."""
from copy import deepcopy
from pathlib import Path
import unittest
from ode.canon import canonical_bytes, parse
from ode.kernel import verify
from ode.proof_slice import slice_proof,compact_block

EXAMPLES=Path(__file__).resolve().parent.parent/'examples'/'proofs'


class SliceTest(unittest.TestCase):
    def test_all_artifacts_recheck_and_slicing_is_idempotent(self):
        theories={}
        from ode.canon import hash_of
        for path in EXAMPLES.glob('*.theory.sexp'):
            t=parse(path.read_bytes())
            theories[hash_of(t)]=t
        for path in EXAMPLES.glob('*.proof.sexp'):
            with self.subTest(proof=path.name):
                p=parse(path.read_bytes())
                g=parse(path.with_name(path.name.replace('.proof.','.goal.')).read_bytes())
                original=deepcopy(p)
                q=slice_proof(p)
                before=verify(theories[g[2]],g,p)
                after=verify(theories[g[2]],g,q)
                self.assertLessEqual(after['rules'],before['rules'])
                self.assertLessEqual(after['work'],before['work'])
                self.assertEqual(p,original)
                self.assertEqual(q,slice_proof(q))
                self.assertLessEqual(len(canonical_bytes(q)),len(canonical_bytes(p)))

    def test_bad_references_stop_even_in_unused_lemmas(self):
        for index in (-1,0,1,True):
            p=parse('''(proof 3 #00 ((lemma () (eq (zero) (zero))
                (derive ((lemma 0))))) (derive ((refl (zero)))))''')
            p[3][0][3][1][0][1]=index
            with self.assertRaises(AssertionError):
                slice_proof(p)

    def test_duplicate_final_step_retains_its_conclusion(self):
        steps=parse('((refl x) (refl y) (sym 0) (sym 2) (refl x))')
        self.assertEqual(compact_block(steps),parse('((refl x))'))

    def test_unused_local_lemma_call_drops_its_library_dependency(self):
        p=parse('''(proof 3 #00 ((lemma () (eq (zero) (zero))
            (derive ((refl (zero))))))
            (derive ((lemma 0) (refl (succ (zero))))))''')
        q=slice_proof(p)
        self.assertEqual(q[3],[])
        self.assertEqual(q[4],parse('(derive ((refl (succ (zero)))))'))

    def test_forward_local_references_stop_even_in_dead_steps(self):
        for value in (-1,0,1,True):
            steps=parse('((sym 0) (refl (zero)))')
            steps[0][1]=value
            with self.assertRaises(AssertionError):
                compact_block(steps)

    def test_case_blocks_keep_separate_reference_scopes(self):
        p=parse('''(proof 3 #00 () (induct n (
          (zero () ((refl (zero)) (refl (zero))))
          (succ (k) ((refl k) (cong succ 0) (refl k) (cong succ 2))))))''')
        q=slice_proof(p)
        self.assertEqual(q[4][2][0][2],parse('((refl (zero)))'))
        self.assertEqual(q[4][2][1][2],parse('((refl k) (cong succ 0))'))

    def test_unused_lemmas_are_removed(self):
        p=parse('''(proof 3 #00 ((lemma () (eq (zero) (zero))
            (derive ((refl (zero)))))) (derive ((refl (zero)))))''')
        self.assertEqual(slice_proof(p)[3],[])


if __name__=='__main__':
    unittest.main()
