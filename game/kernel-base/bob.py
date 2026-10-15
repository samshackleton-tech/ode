"""Recipient of an owner-pinned fragment claim; run from the hashed package.

The unchanged root launcher admits this package by its tree hash. Theory
and both goals are separately pinned by the owner. Proofs and code may
come from anyone. All checked objects and bytes are read once and retained.
Acceptance is a declared-model fragment claim; this recipient runs no code.
"""
import os
from ode.canon import field,hash_of,parse
from ode.encoding_cli import check,read_code
from ode.kernel import Reject
from ode.proof_cli import read_object


def main(reliance_bytes,argv):
    if len(argv)!=2 or argv[1]!='g-fragment':
        print('REJECT expected STORE g-fragment')
        return 1
    try:
        pins=parse(reliance_bytes)
        store=argv[0]
        objects=[]
        for key,name in (('theory','encoding.theory.sexp'),
                         ('encoding-goal','encoding-g.goal.sexp'),
                         ('execution-goal','encoding-g-execution.goal.sexp')):
            value=read_object(os.path.join(store,name))
            if hash_of(value, "theory" if key=="theory" else "goal")!=field(pins,key):
                raise Reject(f'{key} differs from the owner pin')
            objects.append(value)
        theory,encoding_goal,execution_goal=objects
        encoding_proof=read_object(os.path.join(store,'encoding-g.proof.sexp'))
        execution_proof=read_object(os.path.join(store,'encoding-g-execution.proof.sexp'))
        code=read_code(os.path.join(store,'encoding-g.bin'))
        check(theory,encoding_goal,encoding_proof,execution_goal,execution_proof,code)
    except (ValueError,OSError) as error:
        print(f'REJECT {error}')
        return 1
    print('ACCEPT exact fragment bytes, encoding, and abstract execution for the owner-pinned goals')
    return 0
