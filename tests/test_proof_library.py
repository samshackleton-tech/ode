"""Producer library composition shares statements, leaving checking to the kernel."""
from copy import deepcopy
from pathlib import Path
import unittest
from ode.canon import hash_of,parse
from ode.kernel import verify
from ode.proof_library import Library
from ode.equational_proof import app, var

EXAMPLES=Path(__file__).resolve().parent.parent/'examples'/'proofs'


class LibraryTest(unittest.TestCase):
    def test_import_twice_shares_and_rechecks(self):
        t=parse((EXAMPLES/'add32.theory.sexp').read_bytes())
        g,p=[parse((EXAMPLES/f'add32.{k}.sexp').read_bytes()) for k in ('goal','proof')]
        original=deepcopy(p)
        library=Library(hash_of(t, 'theory'))
        index=library.include(g,p)
        count=len(library.lemmas)
        self.assertEqual(index,library.include(g,p))
        self.assertEqual(len(library.lemmas),count)
        proof=[var('proof'),3,hash_of(g, 'goal'),library.lemmas,
               app('derive',[app('lemma',index,var('x'),var('y'))])]
        verify(t,g,proof)
        self.assertEqual(p,original)

    def test_wrong_identity_stops(self):
        t=parse((EXAMPLES/'add32.theory.sexp').read_bytes())
        g,p=[parse((EXAMPLES/f'add32.{k}.sexp').read_bytes()) for k in ('goal','proof')]
        p[2]=hash_of(t, 'theory')
        with self.assertRaisesRegex(AssertionError,'different goal'):
            Library(hash_of(t, 'theory')).include(g,p)


if __name__=='__main__':
    unittest.main()
