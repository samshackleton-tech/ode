"""Produce a checked Word32 proof, or print a residual goal for the author.

stdout is one ordinary s-expression: proof on success (exit 0), residual
goal when help is needed (exit 2). Diagnostics go to stderr. Rerun with
a proof of that residual goal as the third input to finish the original
proof. Failure (exit 1) supplies no proof. No semantic goal is weakened.
"""
import sys
from .canon import canonical_bytes
from .equation_proof import NeedProof,produce
from .kernel import verify
from .proof_cli import read_object


def main(argv):
    if len(argv) not in (2,3):
        print('usage: pypy3 -m ode.equation_cli THEORY GOAL [RESIDUAL_PROOF]',file=sys.stderr)
        return 1
    try:
        theory,goal=(read_object(path) for path in argv[:2])
        hint=read_object(argv[2]) if len(argv)==3 else None
        proof=produce(theory,goal,hint)
        verify(theory,goal,proof)
    except NeedProof as request:
        print(canonical_bytes(request.goal).decode())
        print('NEEDS PROOF: the equality remains unresolved. Supply a proof of this residual goal to continue.',file=sys.stderr)
        return 2
    except (AssertionError,ValueError,OSError) as error:
        print(f'REJECT: {error}',file=sys.stderr)
        return 1
    print(canonical_bytes(proof).decode())
    print('PROVED: the kernel checked the original goal.',file=sys.stderr)
    return 0


if __name__=='__main__':
    raise SystemExit(main(sys.argv[1:]))
