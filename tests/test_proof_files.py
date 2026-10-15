from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
from ode.canon import canonical_bytes,parse
from tools.proof_files import write_theory


class ProofFilesTest(unittest.TestCase):
    def test_preserves_opaque_declarations_and_canonical_identity(self):
        theory=parse('(theory 3 (State) ((f (Nat) State)) ())')
        with TemporaryDirectory() as directory:
            path=Path(directory)/'theory.sexp'
            write_theory(path,theory,['; Owner-facing theory.'])
            self.assertEqual(canonical_bytes(parse(path.read_bytes())),canonical_bytes(theory))
            self.assertIn('; Owner-facing theory.',path.read_text())
