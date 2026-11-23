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
            "Ode.Arithmetic.refutes_sound": "[propext, Quot.sound]",
            "Ode.ends_trace": "[propext, Classical.choice, Quot.sound]",
            "Ode.execQ_exec": "[propext, Classical.choice, Quot.sound]",
            "Ode.runs_plain": "[propext, Classical.choice, Quot.sound]",
            "Ode.runs_free": "[propext, Classical.choice, Quot.sound]",
            "Ode.runs_trace": "[propext, Classical.choice, Quot.sound]",
            "Ode.verify_all_trace": "[propext, Classical.choice, Quot.sound]",
            "Ode.verify_all_result": "[propext, Classical.choice, Quot.sound]"}
STATEMENTS = [
    # of the functions of a statement together: what `odeverify` says yes of (`pieces`: the read-only data of
    # the object files, as the statement gives it; `Meets` is of every state in which the program is loaded)
    ("Ode.verify_all_sound : ∀ (world : List Ode.Program) (pieces : List Ode.Piece) (defs : List Ode.Def) (fns : List Ode.Fn), "
     "Ode.Linked world fns → Ode.verdictAll pieces defs fns = none → "
     "∀ (f : Ode.Fn), f ∈ fns → ∃ p, Ode.findProgram world f.name = some p ∧ Ode.Meets world pieces f.contract defs p"),
    # of one function, given that those it calls meet their contracts
    ("Ode.verify_sound : ∀ (world : List Ode.Program) (ctx : Ode.Ctx) (p : Ode.Program) (proof : List Ode.Item), "
     "p.code = ctx.code → Ode.CalleesMeet world ctx → Ode.verdict ctx proof = none → "
     "Ode.Meets world ctx.pieces ctx.contract ctx.defs p"),
    # what is asked of the functions there are: under each name, the instructions the statement gives, lying in memory
    ("def Ode.Linked : List Ode.Program → List Ode.Fn → Prop := fun world fns => "
     "∀ (f : Ode.Fn), f ∈ fns → ∃ p, Ode.findProgram world f.name = some p ∧ p.code = f.code ∧ p.fits"),
    # of the machine alone: two runs from states alike in everything not marked let the same things be observed
    ("Ode.ends_trace : ∀ {world : List Ode.Program} {p : Ode.Program} {a a' b b' : Ode.State}, "
     "Ode.Alike a b → Ode.Ends world p a a' → Ode.Ends world p b b' → a'.trace = b'.trace"),
    # the marks change no value: a run of the machine with marks is a run of the machine without any
    ("Ode.runs_plain : ∀ {world : List Ode.Program} {perm : Ode.Perm} {p : Ode.Program} {Q : Ode.State → Prop} {s : Ode.State}, "
     "Ode.Runs world perm p Q s → Ode.RunsP world perm p (fun t => ∃ s', Q s' ∧ t = s'.plain) s.plain"),
    # and nothing need be forbidden: it is a run of the plain machine that may touch all memory
    ("Ode.runs_free : ∀ {world : List Ode.Program} {perm : Ode.Perm} {p : Ode.Program} {Q : Ode.State → Prop} {s : Ode.State}, "
     "Ode.Runs world perm p Q s → Ode.RunsP world Ode.Perm.all p (fun t => ∃ s', Q s' ∧ t = s'.plain) s.plain"),
    # constant time of what the verifier says yes of, on the plain machine: stated directly on entry agreement
    # (`traceAgree`), with no mention of marks
    ("Ode.verify_all_trace : ∀ (world : List Ode.Program) (pieces : List Ode.Piece) (defs : List Ode.Def) (fns : List Ode.Fn), "
     "Ode.Linked world fns → Ode.verdictAll pieces defs fns = none → "
     "∀ (f : Ode.Fn), f ∈ fns → ∃ p, Ode.findProgram world f.name = some p ∧ "
     "∀ (a b : Ode.State), Ode.Loaded pieces a → f.contract.clear world pieces a → f.contract.pre p a → "
     "Ode.Loaded pieces b → f.contract.clear world pieces b → f.contract.pre p b → "
     "f.contract.traceAgree defs a b → "
     "∀ (a' b' : Ode.State), Ode.EndsP world p a.plain a' → Ode.EndsP world p b.plain b' → a'.trace = b'.trace"),
    # return-value independence (`result depends on`), stated directly on entry agreement (`traceAgree`)
    ("Ode.verify_all_result : ∀ (world : List Ode.Program) (pieces : List Ode.Piece) (defs : List Ode.Def) (fns : List Ode.Fn), "
     "Ode.Linked world fns → Ode.verdictAll pieces defs fns = none → "
     "∀ (f : Ode.Fn), f ∈ fns → ∃ p, Ode.findProgram world f.name = some p ∧ "
     "(f.contract.resultFollowsTrace = true → "
     "∀ (a b : Ode.State), Ode.Loaded pieces a → f.contract.clear world pieces a → f.contract.pre p a → "
     "Ode.Loaded pieces b → f.contract.clear world pieces b → f.contract.pre p b → "
     "f.contract.traceAgree defs a b → "
     "∀ (a' b' : Ode.State), Ode.EndsP world p a.plain a' → Ode.EndsP world p b.plain b' → a'.reg 0 = b'.reg 0) ∧ "
     "∀ (rh : List String), f.contract.resultHidden = some rh → "
     "∀ (a b : Ode.State), Ode.Loaded pieces a → f.contract.clear world pieces a → f.contract.pre p a → "
     "Ode.Loaded pieces b → f.contract.clear world pieces b → f.contract.pre p b → "
     "(f.contract.forResult rh).traceAgree defs a b → "
     "∀ (a' b' : Ode.State), Ode.EndsP world p a.plain a' → Ode.EndsP world p b.plain b' → a'.reg 0 = b'.reg 0"),
    # a run of the plain machine to a function's return: by `execP` with nothing forbidden
    ("Ode.EndsP.ret : ∀ {world : List Ode.Program} (p : Ode.Program) (s : Ode.State) (i : Ode.Instr) (u : Nat → Nat) (s' : Ode.State), "
     "p.fetch s.rip = some i → Ode.execP Ode.Perm.all p i u s = some (Ode.Outcome.returned s') → Ode.EndsP world p s s'"),
    ("Ode.EndsP.step : ∀ {world : List Ode.Program} (p : Ode.Program) (s : Ode.State) (i : Ode.Instr) (u : Nat → Nat) (s1 s' : Ode.State), "
     "p.fetch s.rip = some i → Ode.execP Ode.Perm.all p i u s = some (Ode.Outcome.next s1) → Ode.EndsP world p s1 s' → Ode.EndsP world p s s'"),
    ("Ode.EndsP.call : ∀ {world : List Ode.Program} (p : Ode.Program) (s : Ode.State) (i : Ode.Instr) (name : String) (q : Ode.Program) (s1 s' : Ode.State), "
     "p.fetch s.rip = some i → Ode.callTarget i = some name → Ode.findProgram world name = some q → "
     "Ode.EndsP world q (Ode.afterCallP p q i s) s1 → Ode.EndsP world p s1 s' → Ode.EndsP world p s s'"),
]


@unittest.skipUnless(LAKE, "Lean's lake is not installed")
class Sound(unittest.TestCase):
    def test_the_theorems_are_proved_from_leans_axioms_alone(self):
        env = dict(os.environ, PATH=os.path.dirname(LAKE) + os.pathsep + os.environ["PATH"])
        built.built("Sound")
        built.built("Trace")
        built.built("Plain")
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "Ask.lean")
            with open(path, "w") as f:
                f.write("import SoundTop\nimport Trace\nimport Plain\n" + "".join(f"#print axioms {name}\n" for name in THEOREMS) +
                        "#check @Ode.verify_all_sound\n#check @Ode.verify_sound\n#print Ode.Linked\n#check @Ode.ends_trace\n#check @Ode.runs_plain\n"
                        "#check @Ode.runs_free\n#check @Ode.verify_all_trace\n#check @Ode.verify_all_result\n#print Ode.EndsP\n")
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
