#!/usr/bin/env pypy3
"""Render the report with the same mandoc layout on every revision. No third-party Python packages."""
from pathlib import Path
import subprocess
import sys

source = Path(sys.argv[1])
dest = Path(sys.argv[2])
with source.open() as f:
    lines = f.read().splitlines()
roff = ['.Dd November 22, 2026', '.Dt ODE 7', '.Os Ode']
literal = False

def esc(line):
    return r'\&' + line.replace('\\', r'\e').replace('`', '')

for line in lines:
    if line.startswith('```'):
        roff.append('.Ed' if literal else '.Bd -literal -offset indent')
        literal = not literal
    elif literal:
        roff.append(esc(line))
    elif line.startswith('# '):
        roff.extend(('.Sh TITLE', esc(line[2:])))
    elif line.startswith('## '):
        roff.append('.Sh "' + line[3:].replace('"', '') + '"')
    elif line:
        roff.append(esc(line))
    else:
        roff.append('.Pp')
assert not literal
rendered = subprocess.run(['mandoc', '-Tpdf', '-O', 'paper=letter'], input=('\n'.join(roff)+'\n').encode(), stdout=subprocess.PIPE, check=True).stdout
assert rendered.startswith(b'%PDF-')
with dest.open('wb') as f:
    f.write(rendered)
