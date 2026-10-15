"""Share repeated proof steps and retain only dependencies of the conclusion.

Producer-side transformation: the kernel checks every retained step and
lemma. References must point strictly backwards. Input is left unchanged.
"""
from copy import deepcopy
from .canon import canonical_bytes


def blocks(derivation):
    if derivation[0] == 'derive':
        yield derivation[1]
    else:
        assert derivation[0] == 'induct', 'unknown derivation form'
        for _, _, steps in derivation[2]:
            yield steps


def instructions(derivation):
    for steps in blocks(derivation):
        yield from steps


def reachable(links, roots):
    needed, todo = set(), list(roots)
    while todo:
        i = todo.pop()
        if i not in needed:
            needed.add(i)
            todo.extend(links[i])
    return sorted(needed)


def references(step):
    """Positions of local proof references; terms and lemma indices stay separate."""
    if step[0] == 'sym':
        return (1,)
    if step[0] == 'trans':
        return (1,2)
    if step[0] == 'cong':
        return range(2,len(step))
    return ()


def compact_block(steps):
    assert steps, 'proof block must contain steps'
    unique, known, remap, links = [], {}, {}, []
    for i, original in enumerate(steps):
        step = list(original)
        for position in references(step):
            old = step[position]
            assert type(old) is int and 0 <= old < i, 'proof reference must point backwards'
            step[position] = remap[old]
        key = canonical_bytes(step)
        if key not in known:
            known[key] = len(unique)
            unique.append(step)
            links.append([step[p] for p in references(step)])
        remap[i] = known[key]
    ordered = reachable(links,[remap[len(steps)-1]])
    result = [unique[i] for i in ordered]
    remap = {old:new for new,old in enumerate(ordered)}
    for step in result:
        for position in references(step):
            step[position] = remap[step[position]]
    # The conclusion is last because every dependency precedes it.
    return result


def slice_proof(proof):
    assert proof[0] == 'proof' and proof[1] == 3, 'requires version-3 proof'

    def dependencies(derivation, before):
        for step in instructions(derivation):
            if step[0] == 'lemma':
                i = step[1]
                assert type(i) is int and 0 <= i < before, 'lemma must refer backwards'
                yield i

    # Validate lemma references even in blocks or lemmas later discarded.
    for i,lemma in enumerate(proof[3]):
        list(dependencies(lemma[3],i))
    list(dependencies(proof[4],len(proof[3])))
    result = deepcopy(proof)
    for derivation in [lemma[3] for lemma in result[3]]+[result[4]]:
        for steps in blocks(derivation):
            steps[:] = compact_block(steps)
    lemmas = result[3]
    links = [set(dependencies(lemma[3],i)) for i,lemma in enumerate(lemmas)]
    ordered = reachable(links,dependencies(result[4],len(lemmas)))
    remap = {old:new for new,old in enumerate(ordered)}
    result[3] = [lemmas[i] for i in ordered]
    for derivation in [lemma[3] for lemma in result[3]]+[result[4]]:
        for step in instructions(derivation):
            if step[0] == 'lemma':
                step[1] = remap[step[1]]
    return result
