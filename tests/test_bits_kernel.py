"""Structural induction, bit semantics, and hostile datatype declarations."""
import copy
from pathlib import Path
import unittest

from ode.canon import Sym, canonical_bytes, hash_of, parse
from ode.kernel import Reject, verify
from tools.make_xor_proof import artifacts

EXAMPLES = Path(__file__).resolve().parent.parent / 'examples' / 'proofs'


def example(name='xor-cancel'):
    theory = parse((EXAMPLES / 'bits.theory.sexp').read_bytes())
    goal = parse((EXAMPLES / f'{name}.goal.sexp').read_bytes())
    proof = parse((EXAMPLES / f'{name}.proof.sexp').read_bytes())
    return theory, goal, proof


def rehash(theory, goal, proof):
    goal[2] = hash_of(theory, 'theory')
    proof[2] = hash_of(goal, 'goal')
    return theory, goal, proof


class BitsKernelTest(unittest.TestCase):
    def test_cancellation_and_width_for_every_finite_bit_string(self):
        for name, rules in (('xor-cancel', 24), ('xor-width', 40)):
            with self.subTest(name=name):
                args = example(name)
                self.assertEqual(verify(*args)['rules'], rules)
                generated = artifacts(args[0])[name]
                for actual, expected in zip(generated, args[1:]):
                    self.assertEqual(canonical_bytes(actual), canonical_bytes(expected))

    def test_all_four_bit_xor_results_follow_from_definitions(self):
        t, _, _ = example()
        for a in (0, 1):
            for b in (0, 1):
                g = parse(f'''(goal 3 #{hash_of(t, "theory").hex()} ()
                            (eq (xor-bit (bit{a}) (bit{b})) (bit{a ^ b})))''')
                steps = f'(unfold xor-bit (bit{a}) (bit{b}))'
                if a:
                    steps += f' (unfold not-bit (bit{b})) (trans 0 1)'
                p = parse(f'(proof 3 #{hash_of(g, "goal").hex()} () (derive ({steps})))')
                verify(t, g, p)
                g[4][2] = parse(f'(bit{1 - (a ^ b)})')
                p[2] = hash_of(g, "goal")
                with self.assertRaises(Reject):
                    verify(t, g, p)

    def test_missing_duplicate_or_foreign_induction_case_rejected(self):
        for mutation in ('missing', 'duplicate', 'foreign'):
            t, g, p = example()
            cases = p[4][2]
            if mutation == 'missing':
                del cases[0]
            elif mutation == 'duplicate':
                cases.append(copy.deepcopy(cases[1]))
            else:
                cases[0][0] = Sym('zero')  # Nat's constructor, not Bits'
            with self.subTest(mutation=mutation), self.assertRaises(Reject):
                verify(t, g, p)

    def test_only_recursive_fields_grant_induction_hypotheses(self):
        for hypothesis in ('h', 'x'):
            t, g, p = example()
            p[4][2][1][2][9] = parse(f'(ih {hypothesis})')
            with self.subTest(hypothesis=hypothesis), self.assertRaisesRegex(Reject, 'recursive field'):
                verify(t, g, p)
        t, g, p = example()
        p[4][2][0][2] = [parse('(ih t)')]
        with self.assertRaisesRegex(Reject, 'recursive field'):
            verify(t, g, p)

    def test_constructor_fields_must_be_fresh_and_correctly_typed(self):
        for fields in ('(h x)', '(h h)', '(t)', '(h t extra)'):
            t, g, p = example()
            p[4][2][1][1] = parse(fields)
            with self.subTest(fields=fields), self.assertRaises(Reject):
                verify(t, g, p)

    def test_no_infinite_or_forward_or_duplicate_datatypes(self):
        for decl in ('(Endless ((again (Endless))))', '(Void ())',
                     '(Bad ((bad (Future))))', '(Bits ((other ())))',
                     '(Bad ((bit0 ())))'):
            t, g, p = example()
            t[2].append(parse(decl))
            with self.subTest(declaration=decl), self.assertRaises(Reject):
                verify(*rehash(t, g, p))

    def test_definitions_require_exhaustive_cases(self):
        t, g, p = example()
        del t[4][0][3][1]  # not-bit only defined on bit0
        with self.assertRaisesRegex(Reject, 'every constructor'):
            verify(*rehash(t, g, p))

    def test_recursion_cannot_use_the_parent_or_an_arbitrary_parameter(self):
        for body in ('(xor-bits (bit h t) ys)', '(xor-bits ys t)'):
            t, g, p = example()
            t[4][5][3][1][2] = parse(body)
            with self.subTest(body=body), self.assertRaisesRegex(Reject, 'does not decrease'):
                verify(*rehash(t, g, p))
        t, g, p = example()
        t[4][5][3][0][2] = parse('(xor-bits (empty) ys)')
        with self.assertRaisesRegex(Reject, 'does not decrease'):
            verify(*rehash(t, g, p))

    def test_wrong_xor_equation_is_rejected_even_after_honest_rehashing(self):
        t, g, p = example()
        t[4][1][3][1][2] = Sym('b')  # define XOR's bit1 branch as identity
        with self.assertRaises(Reject):
            verify(*rehash(t, g, p))

    def test_multiple_recursive_fields(self):
        # Exercises both induction hypotheses, not just the list-tail case.
        t = parse('''(theory 3 ((Tree ((leaf ()) (node (Tree Tree))))) ()
          ((mirror ((t Tree)) Tree
            ((leaf () (leaf))
             (node (l r) (node (mirror r) (mirror l)))))))''')
        g = parse(f'''(goal 3 #{hash_of(t, "theory").hex()} ((t Tree))
                       (eq (mirror (mirror t)) t))''')
        p = parse(f'''(proof 3 #{hash_of(g, "goal").hex()} ()
          (induct t
            ((leaf () ((unfold mirror (leaf)) (cong mirror 0) (trans 1 0)))
             (node (l r)
               ((unfold mirror (node l r)) (cong mirror 0)
                (unfold mirror (node (mirror r) (mirror l))) (trans 1 2)
                (ih l) (ih r) (cong node 4 5) (trans 3 6))))))''')
        self.assertEqual(verify(t, g, p)['rules'], 11)
        p[4][2][1][2][5] = parse('(ih l)')  # reuse the wrong subtree's hypothesis
        with self.assertRaises(Reject):
            verify(t, g, p)

    def test_a_planted_case_coverage_bug_is_detected(self):
        from ode import kernel
        source = Path(kernel.__file__).read_text()
        line = 'require(covered == set(self.constructors[sort]), "cases must cover every constructor")'
        self.assertEqual(source.count(line), 1)
        mutant = {"__name__": "ode._mutant_kernel", "__package__": "ode"}
        exec(compile(source.replace(line, "pass"), "<mutant-kernel>", "exec"), mutant)
        t, _, _ = example()
        g = parse(f'(goal 3 #{hash_of(t, "theory").hex()} ((b Bit)) (eq (bit0) (bit1)))')
        p = parse(f'(proof 3 #{hash_of(g, "goal").hex()} () (induct b ()))')
        with self.assertRaisesRegex(Reject, 'every constructor'):
            verify(t, g, p)
        mutant['verify'](t, g, p)  # vacuous induction would admit a false equation

    def test_versions_one_and_two_rejected(self):
        for version in (1, 2):
            for obj in range(3):
                args = example()
                args[obj][1] = version
                with self.subTest(version=version, obj=obj), self.assertRaisesRegex(Reject, 'version'):
                    verify(*args)


if __name__ == '__main__':
    unittest.main()
