"""Readable theory files for owners; canonical identity is whitespace-independent."""
from ode.canon import canonical_bytes


def write_theory(path,theory,comments):
    """Write a version-3 theory with one constructor/definition per source line.

    Comments are single lines beginning with ';'. The caller supplies a valid
    theory; recipients independently check its identity and definitions.
    """
    assert len(theory)==5 and theory[:2]==['theory',3], 'requires a version-3 theory'
    assert all(line.startswith(';') and '\n' not in line for line in comments)
    text=list(comments)+['(theory 3','  (']
    text+=['    '+canonical_bytes(x).decode() for x in theory[2]]
    text+=['  )','  '+canonical_bytes(theory[3]).decode(),'  (']
    text+=['    '+canonical_bytes(x).decode() for x in theory[4]]
    text+=['  ))']
    path.write_text('\n'.join(text)+'\n')
