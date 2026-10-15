"""Bind matching encoding/execution theorems to exact code bytes.

The kernel checks both equations; this reader checks that they name the
same program and compares the constructor word list against the file. Reliance includes this byte/bit
conversion, file I/O, and the owner's chosen encoding model. Acceptance
establishes encoding and abstract execution in that model, not native ISA
refinement or correctness of a callable function.
"""
from .kernel import MAX_INPUT_BYTES,Reject,verify
from .proof_cli import read_object
from .word_literal import word_value


def code_bytes(words):
    """Decode exactly a constructor list of literal instruction words."""
    result=bytearray()
    while words != ['no-words']:
        if not (isinstance(words,list) and len(words)==3 and words[0]=='instruction-word'):
            raise Reject('expected a constructor list of instruction words')
        result.extend(word_value(words[1]).to_bytes(4,'little'))
        words=words[2]
    return bytes(result)


def check(theory,goal,proof,execution_goal,execution_proof,code):
    """Check exact bytes and both owner-selected claims about the same program."""
    encoding=verify(theory,goal,proof)
    execution=verify(theory,execution_goal,execution_proof)
    left,right=goal[4][1:]
    if goal[3] or not (isinstance(left,list) and len(left)==2 and left[0]=='encode-program'):
        raise Reject('expected a closed encode-program equation')
    run=execution_goal[4][1]
    if not (isinstance(run,list) and len(run)==3 and run[0]=='run'):
        raise Reject('expected a run execution equation')
    if left[1]!=run[1]:
        raise Reject('encoding and execution describe different programs')
    if code_bytes(right)!=code:
        raise Reject('code bytes differ from the proved instruction words')
    return {'encoding':encoding,'execution':execution}


def main(argv):
    if len(argv)!=6:
        print('usage: pypy3 -m ode.encoding_cli THEORY ENCODING_GOAL ENCODING_PROOF EXECUTION_GOAL EXECUTION_PROOF CODE')
        return 2
    try:
        theory,goal,proof,execution_goal,execution_proof=(read_object(p) for p in argv[:5])
        with open(argv[5],'rb') as stream:
            code=stream.read(MAX_INPUT_BYTES+1)
        if len(code)>MAX_INPUT_BYTES:
            raise Reject('code exceeds byte limit')
        check(theory,goal,proof,execution_goal,execution_proof,code)
    except (ValueError,OSError) as error:
        print(f'REJECT: {error}')
        return 1
    print('ACCEPT: code bytes encode the same program whose abstract execution is proved in the supplied theory')
    return 0


if __name__=='__main__':
    import sys
    raise SystemExit(main(sys.argv[1:]))
