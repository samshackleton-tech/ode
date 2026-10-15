"""Kernel conformance: rules, definitions, induction scope, and identity.

The positive case is an unbounded loop-batching theorem. Mutants attack
its derivation and its statement separately; honest rehashing never
turns a wrong equation into a valid theorem. No timing probes here.
"""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from ode.canon import Bytes, Sym, canonical_bytes, hash_of, parse
from ode.kernel import DEFAULT_WORK, Kernel, Reject, verify
from ode.proof_cli import read_object
from tools.make_batching_proof import artifacts

EXAMPLE = ROOT / "examples" / "proofs"


def objects():
    return [parse((EXAMPLE / f"batching.{kind}.sexp").read_bytes())
            for kind in ("theory", "goal", "proof")]


def rebind(theory, goal, proof):
    goal[2] = hash_of(theory)
    proof[2] = hash_of(goal)
    return theory, goal, proof


def simple(equation, body, variables="((n Nat))"):
    theory = parse("(theory 3 () () ())")
    goal = parse(f"(goal 3 #{hash_of(theory).hex()} {variables} {equation})")
    proof = parse(f"(proof 3 #{hash_of(goal).hex()} () {body})")
    return theory, goal, proof


class KernelTest(unittest.TestCase):
    def test_unbounded_batching(self):
        result = verify(*objects())
        self.assertEqual(result["rules"], 24)
        self.assertEqual(result["terms"], 33)
        self.assertLess(result["work"], 2000)

    def test_reproducible_producer(self):
        theory, goal, proof = objects()
        made_goal, made_proof = artifacts(theory)
        self.assertEqual(canonical_bytes(goal), canonical_bytes(made_goal))
        self.assertEqual(canonical_bytes(proof), canonical_bytes(made_proof))

    def test_reflexivity_congruence_symmetry_transitivity(self):
        args = simple("(eq (succ n) (succ n))",
                      "(derive ((refl n) (cong succ 0) (sym 1) (trans 1 2)))")
        self.assertEqual(verify(*args)["rules"], 4)

    def test_zero_argument_congruence(self):
        verify(*simple("(eq (zero) (zero))", "(derive ((cong zero)))", "()"))

    def test_induction_on_a_goal_with_no_other_variables(self):
        verify(*simple("(eq n n)",
                       "(induct n ((zero () ((refl (zero)))) (succ (k) ((ih k) (cong succ 0)))))"))

    def test_false_equation_rejected_even_with_an_honest_hash(self):
        args = simple("(eq (zero) (succ (zero)))", "(derive ((refl (zero))))", "()")
        with self.assertRaisesRegex(Reject, "different equation"):
            verify(*args)

    def test_future_negative_boolean_and_own_step_references_rejected(self):
        for i in (-1, 0, 1, True):
            args = list(simple("(eq n n)", "(derive ((refl n)))"))
            args[2][4][1] = [[Sym("sym"), i]]
            with self.subTest(ref=i), self.assertRaises(Reject):
                verify(*args)

    def test_sort_and_arity_checks(self):
        for body in ("(derive ((refl (succ))))",
                     "(derive ((refl (succ n n))))",
                     "(derive ((refl unbound)))"):
            with self.subTest(body=body), self.assertRaises(Reject):
                verify(*simple("(eq n n)", body))
        theory, goal, proof = objects()
        proof[4][2][1][2][1] = parse("(refl (succ s))")  # s is State, not Nat
        with self.assertRaisesRegex(Reject, "sort mismatch"):
            verify(theory, goal, proof)

    def test_hypothesis_is_available_only_in_the_step(self):
        for body in ("(derive ((ih)))", "(induct n ((zero () ((ih k))) (succ (k) ((refl (succ k))))))"):
            with self.subTest(body=body), self.assertRaisesRegex(Reject, "induction hypothesis"):
                verify(*simple("(eq n n)", body))

    def test_induction_must_check_both_exact_premises(self):
        for phase in (0, 1):
            theory, goal, proof = objects()
            proof[4][2][phase][2] = [parse("(refl s)")]
            with self.subTest(phase=phase), self.assertRaisesRegex(Reject, "different equation"):
                verify(theory, goal, proof)

    def test_predecessor_must_be_fresh_and_nat(self):
        theory, goal, proof = objects()
        proof[4][2][1][1][0] = Sym("s")
        with self.assertRaisesRegex(Reject, "fresh"):
            verify(theory, goal, proof)
        proof[4][1] = Sym("s")
        proof[4][2][1][1][0] = Sym("k")
        with self.assertRaisesRegex(Reject, "datatype"):
            verify(theory, goal, proof)

    def test_current_counter_cannot_be_used_as_hypothesis(self):
        theory, goal, proof = objects()
        # Supplying a counter to IH attempts to generalize k: IH only accepts
        # (s,m,i), at the FIXED predecessor k.
        proof[4][2][1][2][9] = parse("(ih (succ k) s m i)")
        with self.assertRaisesRegex(Reject, "recursive field"):
            verify(theory, goal, proof)
        proof[4][2][1][2][9] = parse("(ih k s m n)")  # n is out of scope in the step
        with self.assertRaisesRegex(Reject, "unbound variable n"):
            verify(theory, goal, proof)

    def test_hypothesis_instantiation_is_simultaneous(self):
        # The example instantiates s with a term CONTAINING s. Applying that
        # substitution repeatedly would loop; sequential substitution could
        # also change the meaning of parameters that occur in each other.
        k = Kernel(DEFAULT_WORK)
        env = k.parameters(parse("((x Nat) (y Nat))"))
        term = k.term(parse("(succ x)"), env)
        got = k.substitute(term, {env[Sym("x")]: env[Sym("y")],
                                  env[Sym("y")]: k.app(Sym("zero"), [])})
        self.assertEqual(got, k.term(parse("(succ y)"), env))

    def test_no_assumed_fact_or_unchecked_evaluator_rule(self):
        for rule in ("axiom", "sorry", "assume", "eval", "oracle", "admit"):
            theory, goal, proof = objects()
            proof[4][2][1][2][-1] = [Sym(rule), goal[4]]
            with self.subTest(rule=rule), self.assertRaisesRegex(Reject, "unknown rule"):
                verify(theory, goal, proof)

    def test_no_nondecreasing_recursive_definition(self):
        for body in ("(double (succ k))", "(double (double k))"):
            theory, goal, proof = objects()
            theory[4][0][3][1][2] = parse(body)
            with self.subTest(body=body), self.assertRaisesRegex(Reject, "does not decrease"):
                verify(*rebind(theory, goal, proof))

    def test_base_case_cannot_recurse_and_forward_calls_are_unknown(self):
        for body in ("(double (zero))", "(chain (zero) s m i)"):
            theory, goal, proof = objects()
            theory[4][0][3][0][2] = parse(body)
            with self.subTest(body=body), self.assertRaises(Reject):
                verify(*rebind(theory, goal, proof))

    def test_constructor_redefinition_duplicate_names_and_bad_scope(self):
        for mutation in ("constructor", "duplicate-param", "duplicate-sort", "free-variable"):
            theory, goal, proof = objects()
            if mutation == "constructor":
                theory[3].append(parse("(succ (Nat) Nat)"))
            elif mutation == "duplicate-param":
                theory[4][1][1].append(parse("(s State)"))
            elif mutation == "duplicate-sort":
                theory[2].append(Sym("Nat"))
            else:
                theory[4][1][3][0][2] = Sym("outsider")
            with self.subTest(mutation=mutation), self.assertRaises(Reject):
                verify(*rebind(theory, goal, proof))

    def test_hash_binding_versions_and_unknown_extra_fields(self):
        for which in range(3):
            for action in ("version", "extra"):
                args = objects()
                if action == "version":
                    args[which][1] = 0
                else:
                    args[which].append(parse("(axiom (eq (zero) (succ (zero))))"))
                with self.subTest(which=which, action=action), self.assertRaises(Reject):
                    verify(*args)
        for which in (1, 2):
            args = objects()
            args[which][2] = Bytes(bytes(32))
            with self.subTest(which=which), self.assertRaisesRegex(Reject, "different"):
                verify(*args)

    def test_budget_and_size_limits_fail_stop(self):
        with self.assertRaisesRegex(Reject, "budget exhausted"):
            verify(*objects(), work=100)
        args = objects()
        args[2] = [Sym("refl"), args[2]]
        for _ in range(129):
            args[2] = [args[2]]
        with self.assertRaisesRegex(Reject, "depth limit"):
            verify(*args)
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "hostile.sexp"
            for data in (b"9" * 100000, b"(" * 10000, b"x" * 1000001):
                p.write_bytes(data)
                with self.subTest(size=len(data)), self.assertRaises(Reject):
                    read_object(p)

    def test_theory_and_goal_mutants_are_rejected_after_honest_rehashing(self):
        # Wrong skip, wrong loop count, wrong state recurrence, wrong theorem.
        for mutant in ("skip", "count", "state", "goal"):
            theory, goal, proof = objects()
            if mutant == "skip":
                theory[4][2][3][1][2][-1] = parse("(succ i)")
            elif mutant == "count":
                theory[4][0][3][1][2] = parse("(succ (double k))")
            elif mutant == "state":
                theory[4][2][3][1][2][2] = Sym("s")
            else:
                goal[4][2][1] = parse("(succ n)")
            with self.subTest(mutant=mutant), self.assertRaises(Reject):
                verify(*rebind(theory, goal, proof))

    def test_sharing_avoids_exponential_tree_expansion(self):
        # Each congruence doubles the *unfolded* expression size. The kernel
        # works on a shared DAG, so 50 doublings remain 51 term nodes.
        theory = parse("(theory 3 () ((f (Nat Nat) Nat)) ())")
        k = Kernel(DEFAULT_WORK)
        k.load_theory(theory)
        env = k.parameters(parse("((n Nat))"))
        steps = [parse("(refl n)")] + [
            [Sym("cong"), Sym("f"), i, i] for i in range(50)]
        a, b = k.block(steps, env)
        self.assertEqual(a, b)
        self.assertEqual(len(k.nodes), 51)
        self.assertLess(k.limit - k.remaining, 1000)

    def test_attack_corpus(self):
        from game.kernel_attacks import cases
        for name, args, accepted in cases():
            with self.subTest(name=name):
                if accepted:
                    verify(*args)
                else:
                    with self.assertRaises(Reject):
                        verify(*args)

    def test_a_planted_kernel_bug_is_detectable(self):
        # Remove transitivity's middle-term check in a *temporary module*.
        # It then proves zero = succ(zero) from two reflexivity facts.
        # The real kernel rejects this same proof. This verifies that the
        # negative control can distinguish a broken rule implementation.
        source = (ROOT / "ode" / "kernel.py").read_text()
        line = 'require(b == c, "transitivity middle terms differ")'
        self.assertEqual(source.count(line), 1)
        mutant = {"__name__": "ode._mutant_kernel", "__package__": "ode"}
        exec(compile(source.replace(line, "pass"), "<mutant-kernel>", "exec"), mutant)
        args = simple("(eq (zero) (succ (zero)))",
                      "(derive ((refl (zero)) (refl (succ (zero))) (trans 0 1)))", "()")
        with self.assertRaisesRegex(Reject, "middle terms differ"):
            verify(*args)
        mutant["verify"](*args)  # the planted bug admits the wrong equation

    def test_user_command_and_tampered_proof(self):
        paths = [str(EXAMPLE / f"batching.{k}.sexp") for k in ("theory", "goal", "proof")]
        cmd = [sys.executable, "-m", "ode.proof_cli"]
        p = subprocess.run(cmd + paths, cwd=ROOT, capture_output=True, text=True, timeout=10)
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertIn("ACCEPT", p.stdout)
        with tempfile.TemporaryDirectory() as d:
            proof = objects()[2]
            proof[4][2][1][2][-1] = parse("(refl s)")
            path = Path(d) / "proof.sexp"
            path.write_bytes(canonical_bytes(proof))
            p = subprocess.run(cmd + paths[:2] + [str(path)], cwd=ROOT,
                               capture_output=True, text=True, timeout=10)
            self.assertEqual(p.returncode, 1, p.stdout + p.stderr)
            self.assertIn("REJECT", p.stdout)


if __name__ == "__main__":
    unittest.main()
