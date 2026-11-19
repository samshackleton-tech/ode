#!/usr/bin/env python3
"""What a test of this repository can read, as one number: tests.sh keeps a test's passing under it.

    python3 tests_key.py GROUP        GROUP: `rest` (the tests outside proof-core) or `proof-core` (those of
                                      proof-core, and the test of tests.sh itself)

A test that passed on some files passes on the same files. So where ODE_TEST_CACHE names a folder, tests.sh
writes down each passing test under the key printed here, and does not run that test again while its key
stands: a change to proof-core alone leaves the keys of the forty tests outside it as they were. No
failure is ever kept. Without ODE_TEST_CACHE every test runs, as before.

The key is a hash of every file under this folder that the group's tests can read, with each file's path,
and of what runs them (Python's implementation and version, the processor, the system). A test outside proof-core reads
nothing in proof-core, and not tests.sh (which only starts it); a test of proof-core may read anything (the
table, the Python verifier it is compared with, the shipped files). Left out of both: every page (`.md`:
no test reads one, and test_tests.py sees to it that no program names one), the licences at the top, and
what a run itself writes (.lake, __pycache__, tests.out).

The hash is BLAKE2 because Python has it everywhere. It names nothing for anybody: it is a key in our own
machine's folder, and a wrong match could only come from a collision in 512 bits."""
import hashlib, os, platform, sys

HERE = os.path.dirname(os.path.abspath(__file__))
WRITTEN = {".lake", "__pycache__", ".git", "tests.out", "tests.log", "tests.exit"}


def files(group):
    for top in sorted(os.listdir(HERE)):
        path = os.path.join(HERE, top)
        if top in WRITTEN: continue
        if os.path.isfile(path):
            if top in ("tests.sh", "tests_key.py", "test_tests.py") and group != "rest": yield top
            continue
        if top == "proof-core" and group != "proof-core": continue
        for where, dirs, names in os.walk(path):
            dirs[:] = sorted(d for d in dirs if d not in WRITTEN)
            for n in sorted(names):
                rel = os.path.relpath(os.path.join(where, n), HERE)
                if n.endswith((".pyc", ".md")): continue
                yield rel


def key(group):
    h = hashlib.blake2b()
    # (the Lean that builds proof-core is named by a file of that folder, lean-toolchain)
    impl = sys.implementation
    h.update(repr((group, impl.name, tuple(impl.version), platform.python_version(), platform.machine(), platform.system())).encode())
    for rel in files(group):
        with open(os.path.join(HERE, rel), "rb") as f: data = f.read()
        h.update(repr((rel, len(data))).encode()); h.update(data)
    return h.hexdigest()


if __name__ == "__main__":
    if len(sys.argv) != 2 or sys.argv[1] not in ("rest", "proof-core"): sys.exit(__doc__)
    print(key(sys.argv[1]))
