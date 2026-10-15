"""Exercise the release workflow in disposable repositories, never this checkout."""
from contextlib import redirect_stdout
from importlib.util import module_from_spec,spec_from_file_location
from io import StringIO
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory
import unittest
from ode.cli import main

ROOT=Path(__file__).resolve().parent.parent
spec=spec_from_file_location('gen_ver',ROOT/'tools'/'gen-ver.py')
release=module_from_spec(spec);spec.loader.exec_module(release)


class ReleaseTest(unittest.TestCase):
    def setUp(self):
        self.directory=TemporaryDirectory();self.addCleanup(self.directory.cleanup)
        self.root=Path(self.directory.name)
        self.git('init','-q')
        self.git('config','user.name','Release test')
        self.git('config','user.email','test@example.invalid')
        (self.root/'VERSION').write_text('0.0.0\n')
        self.git('add','VERSION');self.git('commit','-qm','Initial')

    def git(self,*args):
        return subprocess.check_output(['git',*args],cwd=self.root,text=True).strip()

    def test_release_is_one_commit_and_annotated_tag(self):
        old=self.git('rev-parse','HEAD')
        self.assertEqual(release.release(self.root,'0.1'),'v0.1.0')
        self.assertEqual((self.root/'VERSION').read_text(),'0.1.0\n')
        self.assertEqual(self.git('rev-parse','HEAD^'),old)
        self.assertEqual(self.git('cat-file','-t','v0.1.0'),'tag')
        self.assertEqual(self.git('rev-parse','v0.1.0^{commit}'),self.git('rev-parse','HEAD'))
        self.assertEqual(self.git('status','--porcelain'),'')
        with self.assertRaises(release.ReleaseError):release.release(self.root,'0.1')

    def test_dirty_staged_and_untracked_files_stop_before_writes(self):
        for staged in (False,True):
            (self.root/'pending').write_text('work')
            if staged:self.git('add','pending')
            with self.assertRaises(release.ReleaseError):release.release(self.root,'0.1')
            self.assertEqual((self.root/'VERSION').read_text(),'0.0.0\n')

    def test_duplicate_tag_and_detached_head_stop(self):
        self.git('tag','v0.1.0')
        with self.assertRaises(release.ReleaseError):release.release(self.root,'0.1')
        self.git('checkout','--detach','-q')
        with self.assertRaises(subprocess.CalledProcessError):release.release(self.root,'0.2')
        self.assertEqual((self.root/'VERSION').read_text(),'0.0.0\n')

    def test_version_contract(self):
        self.assertEqual(release.version('0.1'),(0,1,0))
        for text in ('v0.1','0.01','1','1.2.3.4','1.2-rc1','1.2+abc','١.2','1.2\n'):
            with self.subTest(text=text),self.assertRaises(release.ReleaseError):release.version(text)

    def test_cli_reads_the_single_version_file(self):
        out=StringIO()
        with redirect_stdout(out):self.assertEqual(main(['--version']),0)
        self.assertEqual(out.getvalue(),'Ode '+(ROOT/'VERSION').read_text())
