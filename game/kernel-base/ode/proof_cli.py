"""File interface for the kernel; the kernel itself performs no I/O.

The owner supplies THEORY and GOAL separately from the producer's PROOF.
The goal pins the theory and the proof pins the goal. Source files may
carry whitespace and comments; identities are hashes of canonical forms.
"""
from .canon import _tokens, canonical_bytes, parse
from .kernel import MAX_DEPTH, MAX_INPUT_BYTES, Reject, verify


def read_object(path):
    with open(path, "rb") as stream:
        data = stream.read(MAX_INPUT_BYTES + 1)
    if len(data) > MAX_INPUT_BYTES:
        raise Reject("object exceeds byte limit")
    # Bound parser work *before* converting integer literals or descending.
    text = data.decode("utf-8")
    depth = 0
    for token in _tokens(text):
        if len(token) > 128:
            raise Reject("token exceeds length limit")
        if token == "(":
            depth += 1
        elif token == ")":
            depth -= 1
        if not 0 <= depth <= MAX_DEPTH:
            raise Reject("syntax exceeds depth limit or has unmatched parentheses")
    return parse(text)


def main(argv):
    if len(argv) != 3:
        print("usage: pypy3 -m ode.proof_cli THEORY GOAL PROOF")
        return 2
    try:
        theory, goal, proof = (read_object(p) for p in argv)
        result = verify(theory, goal, proof)
    except (Reject, ValueError, OSError) as error:
        print(f"REJECT: {error}")
        return 1
    print("ACCEPT: the universally quantified equation follows from the definitions")
    print(canonical_bytes(goal[4]).decode())
    print(f"theory #{result['theory'].hex()}")
    print(f"goal   #{result['goal'].hex()}")
    print(f"{result['lemmas']} proved lemmas; {result['rules']} inference steps; "
          f"{result['terms']} shared terms; "
          f"{result['work']} work units")
    return 0


if __name__ == "__main__":
    import sys
    raise SystemExit(main(sys.argv[1:]))
