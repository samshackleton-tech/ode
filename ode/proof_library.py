"""Assemble already-produced theorem derivations into one proof library.

This is producer code, not a checker. Equal statements share an earlier
entry; every retained derivation still has to pass the kernel. Theories
must match and references must point backwards within each input proof.
"""
from copy import deepcopy
from .canon import canonical_bytes
from .proof_slice import instructions
from .equational_proof import var


class Library:
    def __init__(self, theory_hash):
        self.theory_hash = theory_hash
        self.lemmas = []
        self.index = {}

    def add(self, lemma):
        key = canonical_bytes(lemma[1:3])
        if key not in self.index:
            self.index[key] = len(self.lemmas)
            self.lemmas.append(lemma)
        return self.index[key]

    def include(self, goal, proof):
        assert goal[2] == self.theory_hash, 'theorem uses a different theory'
        from .canon import hash_of
        assert proof[2] == hash_of(goal, 'goal'), 'proof names a different goal'
        remap = {}
        entries = proof[3] + [[var('lemma'),goal[3],goal[4],proof[4]]]
        for i,entry in enumerate(entries):
            lemma = deepcopy(entry)
            for step in instructions(lemma[3]):
                if step[0] == 'lemma':
                    assert type(step[1]) is int and step[1] in remap, 'lemma must refer backwards'
                    step[1] = remap[step[1]]
            remap[i] = self.add(lemma)
        return remap[len(proof[3])]
