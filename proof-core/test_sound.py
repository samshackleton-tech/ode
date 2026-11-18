#!/usr/bin/env python3
"""The theorems of proof-core are checked by Lean, and rest on nothing but Lean's own three axioms.

    python3 test_sound.py        (skipped where Lean's `lake` is not installed)

`lake build Sound` checks every proof. Then Lean is asked what each theorem depends on: an unfinished proof
would show there as `sorryAx`, an assumption of ours as an axiom's name."""
import os, shutil, subprocess, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
LAKE = shutil.which("lake") or (os.path.expanduser("~/.elan/bin/lake") if os.path.exists(os.path.expanduser("~/.elan/bin/lake")) else None)
THEOREMS = {"Ode.verify_sound": "[propext, Classical.choice, Quot.sound]",
            "Ode.Arithmetic.refutes_sound": "[propext, Quot.sound]"}
STATEMENT = ("Ode.verify_sound : ∀ (ctx : Ode.Ctx) (p : Ode.Program) (proof : List Ode.Item), "
             "p.code = ctx.code → Ode.verdict ctx proof = none → Ode.Meets ctx.contract ctx.defs p")


@unittest.skipUnless(LAKE, "Lean's lake is not installed")
class Sound(unittest.TestCase):
    def test_the_theorems_are_proved_from_leans_axioms_alone(self):
        env = dict(os.environ, PATH=os.path.dirname(LAKE) + os.pathsep + os.environ["PATH"])
        r = subprocess.run([LAKE, "build", "Sound"], cwd=HERE, capture_output=True, text=True, env=env)
        self.assertEqual(r.returncode, 0, r.stdout[-3000:] + r.stderr[-3000:])
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "Ask.lean")
            with open(path, "w") as f:
                f.write("import SoundTop\n" + "".join(f"#print axioms {name}\n" for name in THEOREMS) + "#check @Ode.verify_sound\n")
            r = subprocess.run([LAKE, "env", "lean", path], cwd=HERE, capture_output=True, text=True, env=env)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        said = " ".join(r.stdout.split())
        for name, axioms in THEOREMS.items(): self.assertIn(f"'{name}' depends on axioms: {axioms}", said)
        self.assertNotIn("sorry", said)
        self.assertIn(STATEMENT, said.replace("@", ""))

    def test_no_proof_is_left_open_in_the_text(self):
        for name in sorted(os.listdir(HERE)):
            if name.endswith(".lean"):
                with open(os.path.join(HERE, name)) as f: text = f.read()
                self.assertNotIn("sorry", text, name)
                self.assertNotIn("axiom ", text, name)


if __name__ == "__main__":
    unittest.main()
