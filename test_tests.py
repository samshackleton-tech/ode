#!/usr/bin/env python3
"""tests.sh keeps a passing test and runs it again only when a file it can read has changed.

tests.sh and tests_key.py are copied beside stand-ins for every test file tests.sh names; a stand-in writes
its name down and passes (or fails, where told to). Then tests.sh is run with ODE_TEST_CACHE and what ran
is read:
- the first time everything runs; the second time nothing does, and every line says `kept`;
- after a change in proof-core only proof-core's tests run; after a change outside it, all of them;
- a page changes nothing, at the top or in a folder (and no program names a page, so none can read one);
- with ODE_TESTS=proof-core only proof-core's tests run;
- a failing test fails the run, is not kept, and runs again;
- without ODE_TEST_CACHE everything runs every time."""
import os, re, shlex, shutil, subprocess, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
STAND_IN = '''import os, sys
name = os.path.basename(os.getcwd()) + "/" + " ".join(sys.argv)
with open(os.environ["RAN"], "a") as f: f.write(name + "\\n")
if os.path.exists(os.path.join(os.path.dirname(os.path.abspath(__file__)), "fail-" + os.path.basename(sys.argv[0]))):
    print("FAILED (failures=1)"); sys.exit(1)
print("Ran 1 test in 0.000s\\n\\nOK")
'''


class Kept(unittest.TestCase):
    def setUp(self):
        self.d = tempfile.mkdtemp()
        for f in ("tests.sh", "tests_key.py"): shutil.copy(os.path.join(HERE, f), self.d)
        with open(os.path.join(HERE, "tests.sh")) as f: text = f.read()
        text = text.replace("\\\n", " ")
        names = set()
        for m in re.finditer(r"for t in ([^;]+); do\s+(?:\( .*?; )?one (\S+) ", text):
            if "$" not in m.group(1): names |= {(m.group(2), t) for t in m.group(1).split()}
        names |= {("proof-core", t) for t in re.search(r'^pc="([^"]+)"', text, re.M).group(1).split()}
        names |= {(m.group(1), m.group(2)) for m in re.finditer(r"^one (\S+) (\S+\.py) ", text, re.M)}
        names.add(("kcheck", "test_kbyte.py"))
        self.assertGreater(len(names), 30)
        for folder, t in names:
            if folder == ".": continue                              # this very test: not run inside itself
            path = os.path.join(self.d, folder, t)
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w") as f: f.write(STAND_IN)
        for rel in ("README.md", "kcheck/VERIFY.md", "proof-core/Core.lean", "kcheck/kfn.py"):
            with open(os.path.join(self.d, rel), "w") as f: f.write("as it was\n")
        self.ran = os.path.join(tempfile.mkdtemp(), "ran")
        self.cache = tempfile.mkdtemp()

    def run_all(self, cache=True, only=None, python=sys.executable):
        """(exit status, the tests that ran, the lines of the output)"""
        if os.path.exists(self.ran): os.remove(self.ran)
        env = {"PATH": "/usr/bin:/bin", "HOME": self.d, "RAN": self.ran, "IN_TEST_TESTS": "1", "PYTHON": python}
        if cache: env["ODE_TEST_CACHE"] = self.cache
        if only: env["ODE_TESTS"] = only
        out = os.path.join(os.path.dirname(self.ran), "out")
        r = subprocess.run(["sh", os.path.join(self.d, "tests.sh"), out], env=env, capture_output=True, text=True)
        ran = []
        if os.path.exists(self.ran):
            with open(self.ran) as f: ran = sorted(f.read().split("\n")[:-1])
        with open(out) as f: lines = f.read().split("\n")[:-1]
        return r.returncode, ran, lines

    def test_a_passing_test_runs_again_only_when_its_files_change(self):
        status, first, lines = self.run_all()
        self.assertEqual(status, 0)
        self.assertEqual(len(first), len(lines))
        self.assertGreater(len(first), 45)
        status, ran, lines = self.run_all()
        self.assertEqual((status, ran), (0, []))
        self.assertTrue(all("| kept (" in l and l.rstrip().endswith("OK") for l in lines), lines[:3])
        self.assertEqual(len(lines), len(first))
        with open(os.path.join(self.d, "proof-core", "Core.lean"), "w") as f: f.write("as it is.\n")                # (a change of content only: no new file, the same length)
        status, ran, lines = self.run_all()
        self.assertEqual(status, 0)
        self.assertEqual(ran, [t for t in first if t.startswith("proof-core/")])
        self.assertGreater(len(ran), 10)
        with open(os.path.join(self.d, "kcheck", "kfn.py"), "w") as f: f.write("as it is.\n")
        status, ran, lines = self.run_all()
        self.assertEqual((status, ran), (0, first))
        for page in ("README.md", os.path.join("kcheck", "VERIFY.md")):
            with open(os.path.join(self.d, page), "w") as f: f.write("as it is.\n")
            self.assertEqual(self.run_all()[:2], (0, []), page)

    def test_no_program_names_a_page(self):
        """The pages are left out of the keys because no test reads one. A program that names a page in a
        string might read it: if one must, the pages belong in tests_key.py's keys again."""
        found = []
        for where, dirs, names in os.walk(HERE):
            dirs[:] = [d for d in dirs if d not in (".lake", ".git", "__pycache__", "reference")]
            for n in names:
                if not n.endswith((".py", ".sh", ".lean")) or n in ("test_tests.py", "tests_key.py"): continue
                with open(os.path.join(where, n), errors="replace") as f: text = f.read()
                if re.search(r"\.md[\"']", text): found.append(os.path.relpath(os.path.join(where, n), HERE))
        self.assertEqual(found, [])

    def test_only_the_tests_of_proof_core_where_asked(self):
        status, ran, lines = self.run_all(only="proof-core")
        self.assertEqual(status, 0)
        self.assertGreater(len(ran), 10)
        self.assertTrue(all(t.startswith("proof-core/") for t in ran), ran[:3])
        self.assertEqual(len(ran), len(lines))

    def test_the_requested_python_runs_the_tests_and_computes_the_keys(self):
        log = os.path.join(self.cache, "python.calls")
        python = os.path.join(self.cache, "chosen python")
        with open(python, "w") as f:
            f.write(f'#!/bin/sh\nprintf "%s\\n" "$1" >> {shlex.quote(log)}\nexec {shlex.quote(sys.executable)} "$@"\n')
        os.chmod(python, 0o755)
        self.assertEqual(self.run_all(only="proof-core", python=python)[0], 0)
        with open(log) as f: calls = f.read().splitlines()
        self.assertEqual(calls[:2], [os.path.join(self.d, "tests_key.py")] * 2)
        self.assertIn("test_sound.py", calls[2:])

    def test_a_failure_is_never_kept(self):
        self.assertEqual(self.run_all()[0], 0)
        with open(os.path.join(self.d, "core", "fail-test_core.py"), "w") as f: f.write("")
        status, ran, lines = self.run_all()
        self.assertEqual(status, 1)
        self.assertEqual(len(ran), len(lines))                       # a file outside proof-core changed: all of them
        status, ran, lines = self.run_all()
        self.assertEqual((status, ran), (1, ["core/test_core.py"]))  # only the failed one, again
        os.remove(os.path.join(self.d, "core", "fail-test_core.py"))
        status, ran, lines = self.run_all()                          # the files are as at the first run: all kept from then
        self.assertEqual((status, ran), (0, []))

    def test_without_the_folder_everything_runs(self):
        status, first, _ = self.run_all(cache=False)
        status2, again, lines = self.run_all(cache=False)
        self.assertEqual((status, status2), (0, 0))
        self.assertEqual(first, again)
        self.assertFalse(any("kept" in l for l in lines))
        self.assertEqual(os.listdir(self.cache), [])


if __name__ == "__main__":
    unittest.main()
