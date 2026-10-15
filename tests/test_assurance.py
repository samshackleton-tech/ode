"""Assurance reports describe freshly checked stores and their actual scope."""
from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
from ode import produce
from ode.canon import parse
from ode.cli import cmd_assure

EXAMPLES=Path(__file__).resolve().parent.parent/'examples'


class AssuranceTest(unittest.TestCase):
    def test_binary_and_binding_reports(self):
        spec=parse((EXAMPLES/'blake3-g.sexp').read_bytes())
        for binding in (False,True):
            with self.subTest(binding=binding),TemporaryDirectory() as directory:
                if binding:
                    produce.bind(spec,directory,'w32',{})
                else:
                    produce.build(spec,directory,'w32')
                with redirect_stdout(StringIO()):
                    self.assertEqual(cmd_assure([directory]),0)
                text=(Path(directory)/'assurance.md').read_text()
                self.assertEqual('every valid instantiation' in text,binding)
                self.assertEqual('- binary `' in text,not binding)
                self.assertNotIn('0'*64,text)

    def test_saved_record_cannot_mask_a_changed_binary(self):
        spec=parse((EXAMPLES/'blake3-g.sexp').read_bytes())
        with TemporaryDirectory() as directory:
            result=produce.build(spec,directory,'w32')
            (Path(directory)/'checker-record.sexp').write_text('(record (verdict accept))')
            (Path(directory)/(result['binary_hash']+'.bin')).write_bytes(b'wrong bytes')
            with redirect_stdout(StringIO()):
                self.assertEqual(cmd_assure([directory]),1)
            self.assertFalse((Path(directory)/'assurance.md').exists())
