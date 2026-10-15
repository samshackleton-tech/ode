"""Remove unused supporting lemmas from a produced proof.

Producer-side dependency slicing only: the kernel still checks every
retained lemma and the final derivation. Input must be a version-3 proof
whose lemma references point strictly backwards. Input is left unchanged.
"""
from copy import deepcopy


def instructions(derivation):
    if derivation[0] == 'derive':
        yield from derivation[1]
    else:
        assert derivation[0] == 'induct', 'unknown derivation form'
        for _, _, steps in derivation[2]:
            yield from steps


def slice_proof(proof):
    assert proof[0] == 'proof' and proof[1] == 3, 'requires version-3 proof'
    lemmas = proof[3]
    needed = set()

    def dependencies(derivation, before):
        for step in instructions(derivation):
            if step[0] == 'lemma':
                i = step[1]
                assert type(i) is int and 0 <= i < before, 'lemma must refer backwards'
                yield i

    # Check references even in discarded lemmas: a malformed producer
    # input stops rather than having its invalid references hidden.
    links = [set(dependencies(lemma[3], i)) for i, lemma in enumerate(lemmas)]
    todo = list(dependencies(proof[4], len(lemmas)))
    while todo:
        i = todo.pop()
        if i not in needed:
            needed.add(i)
            todo.extend(links[i])
    ordered = sorted(needed)
    remap = {old: new for new, old in enumerate(ordered)}
    result = deepcopy(proof[:3]) + [deepcopy([lemmas[i] for i in ordered]), deepcopy(proof[4])]
    for derivation in [lemma[3] for lemma in result[3]] + [result[4]]:
        for step in instructions(derivation):
            if step[0] == 'lemma':
                step[1] = remap[step[1]]
    return result
