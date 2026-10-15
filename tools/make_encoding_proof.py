#!/usr/bin/env pypy3
"""Emit a declared encoding proof and the 56-byte G arithmetic fragment."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT))
from ode.canon import canonical_bytes,parse
from ode.encoding_proof import theory,artifacts,execution_artifacts
from ode.register_proof import g_instructions

# W3,W4,W5,W6,W7,W8 stand for a,b,c,d,x,y. Independent instruction words.
WORDS=[0x0b040063,0x0b070063,0x4a0300c6,0x138640c6,0x0b0600a5,0x4a050084,0x13843084,
       0x0b040063,0x0b080063,0x4a0300c6,0x138620c6,0x0b0600a5,0x4a050084,0x13841c84]


def main():
    d=ROOT/'examples'/'proofs'
    t=theory(parse((d/'bits.theory.sexp').read_bytes()),parse((d/'g-definition.sexp').read_bytes()))
    text=['; Declared ADD/EOR/ROR encodings; abstract a,b,c,d,x,y map to W3..W8.',
          '; Arithmetic fragment only: no memory, RET, ABI, or Arm ISA refinement theorem.',
          '(theory 3','  (']
    text+=['    '+canonical_bytes(x).decode() for x in t[2]]
    text+=['  )','  ()','  (']
    text+=['    '+canonical_bytes(x).decode() for x in t[4]]
    text+=['  ))']
    (d/'encoding.theory.sexp').write_text('\n'.join(text)+'\n')
    for name,(g,p) in (('encoding-g',artifacts(t,g_instructions(),WORDS)),
                        ('encoding-g-execution',execution_artifacts(t))):
        for kind,value in (('goal',g),('proof',p)):
            (d/f'{name}.{kind}.sexp').write_bytes(canonical_bytes(value))
    (d/'encoding-g.bin').write_bytes(b''.join(w.to_bytes(4,'little') for w in WORDS))


if __name__=='__main__':
    main()
