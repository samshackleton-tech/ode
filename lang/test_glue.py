#!/usr/bin/env python3
"""The assembly kept in kcheck/glue/ for hash.ode's nine functions is what the compiler prints today.

    python3 lang/test_glue.py

hash.ode is compiled again (odec.py, then Lang.lean: lang/build.sh) and each function's assembly is compared,
character for character, with the file kept in kcheck/glue/, from which the shipped b3hashr.o was linked.
Skipped where there is no Lean (`lake`) or no clang."""
import os, shutil, subprocess, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
KCHECK = os.path.join(HERE, "..", "kcheck")
HASH = ["pad", "chunk_node", "node_out", "wide32", "wide128", "take", "part32", "subtree", "hashr"]


@unittest.skipUnless(shutil.which("lake") and shutil.which("clang"), "no lake or no clang: hash.ode is not compiled again")
class Glue(unittest.TestCase):
    def test_hash_ode_compiles_to_the_assembly_kept(self):
        with tempfile.TemporaryDirectory() as d:
            r = subprocess.run(["sh", os.path.join(HERE, "build.sh"), os.path.join(KCHECK, "hash.ode"), "b3l_", d] + HASH, capture_output=True, text=True)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            for name in HASH:
                with open(os.path.join(d, name + ".S")) as f: made = f.read()
                with open(os.path.join(KCHECK, "glue", name + ".S")) as f: kept = f.read()
                self.assertEqual(made, kept, name)


if __name__ == "__main__":
    unittest.main()
