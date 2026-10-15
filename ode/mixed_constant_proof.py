"""Fold a constant suffix inside a symbolic normalization derivation.

Reuse the existing algebraic normalizer and constructor-evaluation
producer. Constants sort after symbolic atoms, so their evaluation proof
can be lifted through the surrounding symbolic expression by congruence.
"""
from .canon import canonical_bytes,hash_of
from .ground_proof import Evaluation
from .equational_proof import Normalizer, app, equation, var
from .word_literal import ZERO


def is_word(term):
    return isinstance(term,list) and bool(term) and term[0]=='word32'


class NormalizerWithConstants(Normalizer):
    def __init__(self, theory, library, operation, laws):
        super().__init__(operation,ZERO,laws)
        self.theory,self.library = theory,library

    def order_key(self, atom):
        return is_word(atom),canonical_bytes(atom)

    def normalize(self, term):
        atoms, prefix_proof = super().normalize(term)
        split = next((i for i,a in enumerate(atoms) if is_word(a)),len(atoms))
        symbols,constants = atoms[:split],atoms[split:]
        if len(constants)<2:
            return atoms,prefix_proof
        expression = self.term(constants)
        evaluation = Evaluation(self.theory)
        value,last = evaluation.evaluate(expression)
        evaluation.trans(last,evaluation.refl(value))
        goal = [var('goal'),3,hash_of(self.theory),[],equation(expression,value)]
        proof = [var('proof'),3,hash_of(goal),[],[var('derive'),evaluation.steps]]
        q = self.lemma(self.library.include(goal,proof))
        suffix = [] if value==ZERO else [value]
        for atom in reversed(symbols):
            q = self.cong(self.operation,self.refl(atom),q)
            if value==ZERO:
                q = self.trans(q,self.law('right',atom))
                value = atom
            else:
                value = app(self.operation,atom,value)
        return symbols+suffix,self.trans(prefix_proof,q)
