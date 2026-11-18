#!/usr/bin/env python3
"""The theorems of proof-core are checked by Lean, and rest on nothing but Lean's own three axioms.

    python3 test_sound.py        (skipped where Lean's `lake` is not installed)

`lake build Sound` checks every proof. Then Lean is asked what each theorem depends on: an unfinished proof
would show there as `sorryAx`, an assumption of ours as an axiom's name."""
import os, shutil, subprocess, tempfile, unittest
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import built
HERE = os.path.dirname(os.path.abspath(__file__))
LAKE = shutil.which("lake") or (os.path.expanduser("~/.elan/bin/lake") if os.path.exists(os.path.expanduser("~/.elan/bin/lake")) else None)
THEOREMS = {"Ode.verify_all_sound": "[propext, Classical.choice, Quot.sound]",
            "Ode.verify_sound": "[propext, Classical.choice, Quot.sound]",
            "Ode.Arithmetic.refutes_sound": "[propext, Quot.sound]"}
STATEMENTS = [
    # of the functions of a statement together: what `odeverify` says yes of
    ("Ode.verify_all_sound : ∀ (world : List Ode.Program) (defs : List Ode.Def) (fns : List Ode.Fn), "
     "Ode.Linked world fns → Ode.verdictAll defs fns = none → "
     "∀ (f : Ode.Fn), f ∈ fns → ∃ p, Ode.findProgram world f.name = some p ∧ Ode.Meets world f.contract defs p"),
    # of one function, given that those it calls meet their contracts
    ("Ode.verify_sound : ∀ (world : List Ode.Program) (ctx : Ode.Ctx) (p : Ode.Program) (proof : List Ode.Item), "
     "p.code = ctx.code → Ode.CalleesMeet world ctx → Ode.verdict ctx proof = none → "
     "Ode.Meets world ctx.contract ctx.defs p"),
    # what is asked of the functions there are: under each name, the instructions the statement gives, lying in memory
    ("def Ode.Linked : List Ode.Program → List Ode.Fn → Prop := fun world fns => "
     "∀ (f : Ode.Fn), f ∈ fns → ∃ p, Ode.findProgram world f.name = some p ∧ p.code = f.code ∧ p.fits"),
]


@unittest.skipUnless(LAKE, "Lean's lake is not installed")
class Sound(unittest.TestCase):
    def test_the_theorems_are_proved_from_leans_axioms_alone(self):
        env = dict(os.environ, PATH=os.path.dirname(LAKE) + os.pathsep + os.environ["PATH"])
        built.built("Sound")
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "Ask.lean")
            with open(path, "w") as f:
                f.write("import SoundTop\n" + "".join(f"#print axioms {name}\n" for name in THEOREMS) +
                        "#check @Ode.verify_all_sound\n#check @Ode.verify_sound\n#print Ode.Linked\n")
            r = subprocess.run([LAKE, "env", "lean", path], cwd=HERE, capture_output=True, text=True, env=env)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        said = " ".join(r.stdout.split())
        for name, axioms in THEOREMS.items(): self.assertIn(f"'{name}' depends on axioms: {axioms}", said)
        self.assertNotIn("sorry", said)
        for statement in STATEMENTS: self.assertIn(statement, said.replace("@", ""))

    def test_no_proof_is_left_open_in_the_text(self):
        for name in sorted(os.listdir(HERE)):
            if name.endswith(".lean"):
                with open(os.path.join(HERE, name)) as f: text = f.read()
                self.assertNotIn("sorry", text, name)
                self.assertNotIn("axiom ", text, name)


if __name__ == "__main__":
    unittest.main()
