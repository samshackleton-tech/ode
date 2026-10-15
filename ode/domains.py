"""Current semantic domains for every Ode content identity.

A domain revision changes whenever the meaning of its hashed objects
changes, even if their bytes/format do not. Preserve revisions for
meaning-preserving refactors. Never accept an older domain as a fallback.
The URL is a permanent namespace, not a location to fetch at runtime.
This same registry is copied into the bootstrap root, which serves it to
both delivered checker packages.
"""
NAMESPACE = 'https://github.com/samshackleton-tech/ode'
REVISIONS = {
    'spec': 1,           # Ode word/natural/list specification semantics
    'certificate': 1,    # executable verification claims and bindings
    'theory': 1,         # sorted definitions and structural recursion
    'goal': 1,           # universally quantified sorted equations
    'proof': 1,          # equality/structural-induction proof objects
    'binary-w32': 1,     # W32 bytecode encoding and execution model
    'binary-a64': 1,     # supported AArch64 encoding and execution model
    'package-file': 1,   # exact bytes of one delivered package file
    'package-tree': 1,   # sorted path/NUL/file-identity manifest
}


def context(kind):
    """The currently accepted semantic context; callers choose the kind."""
    if kind not in REVISIONS:
        raise ValueError(f'unknown identity domain {kind!r}')
    return f'{NAMESPACE}/{kind}/semantics-v{REVISIONS[kind]}'
