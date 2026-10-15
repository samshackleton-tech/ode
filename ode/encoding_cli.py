"""Bind an owner-selected encoding theorem to exact little-endian code bytes.

The kernel checks the equation; this reader additionally checks the
constructor word list against the file. Reliance includes this byte/bit
conversion, file I/O, and the owner's chosen encoding model. Acceptance
establishes encoding in that model, not native execution correctness.
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


def check(theory,goal,proof,code):
    record=verify(theory,goal,proof)
    left,right=goal[4][1:]
    if goal[3] or not (isinstance(left,list) and len(left)==2 and left[0]=='encode-program'):
        raise Reject('expected a closed encode-program equation')
    if code_bytes(right)!=code:
        raise Reject('code bytes differ from the proved instruction words')
    return record


def main(argv):
    if len(argv)!=4:
        print('usage: pypy3 -m ode.encoding_cli THEORY GOAL PROOF CODE')
        return 2
    try:
        theory,goal,proof=(read_object(p) for p in argv[:3])
        with open(argv[3],'rb') as stream:
            code=stream.read(MAX_INPUT_BYTES+1)
        if len(code)>MAX_INPUT_BYTES:
            raise Reject('code exceeds byte limit')
        check(theory,goal,proof,code)
    except (ValueError,OSError) as error:
        print(f'REJECT: {error}')
        return 1
    print('ACCEPT: code bytes match the proved instruction encoding in the supplied theory')
    return 0


if __name__=='__main__':
    import sys
    raise SystemExit(main(sys.argv[1:]))
