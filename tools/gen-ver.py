#!/usr/bin/env pypy3
"""Create an Ode release commit and annotated tag; publishing is explicit.

Inspired by zooko/bench-hashes tools/gen-ver.py at
63ee3ae04f56c61db08de8f938a0854d4619de27. This implementation uses a single
VERSION file and commit, with Git's tag providing the commit identity.
"""
from pathlib import Path
import re
import subprocess
import sys


class ReleaseError(Exception):
    pass


def version(text):
    """Accept canonical MAJOR.MINOR[.PATCH]; return three integers."""
    if not re.fullmatch(r'(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)(\.(0|[1-9][0-9]*))?',text):
        raise ReleaseError('expected MAJOR.MINOR or MAJOR.MINOR.PATCH, without a v prefix or suffix')
    parts=tuple(map(int,text.split('.')))
    return parts+(0,) if len(parts)==2 else parts


def release(root,requested):
    """Require a clean attached checkout, an increasing version, and an unused tag.

    Failures stop at their cause; completed writes/commits remain for inspection.
    No network operations, rollback, or edits outside VERSION are performed.
    """
    root=Path(root).resolve()
    def git(*args):
        return subprocess.run(['git',*args],cwd=root,check=True,text=True,
                              stdout=subprocess.PIPE).stdout.rstrip('\r\n')

    proposed=version(requested)
    if Path(git('rev-parse','--show-toplevel')).resolve()!=root:
        raise ReleaseError('release must target the repository root')
    git('symbolic-ref','--quiet','HEAD')
    if git('status','--porcelain=v1','--untracked-files=all'):
        raise ReleaseError('release requires a clean working tree, including untracked files')
    path=root/'VERSION'
    current=path.read_text().strip()
    if current!='.'.join(map(str,version(current))):
        raise ReleaseError('VERSION must contain canonical MAJOR.MINOR.PATCH')
    if proposed<=version(current):
        raise ReleaseError('new version must be greater than VERSION')
    name='.'.join(map(str,proposed));tag='v'+name
    if git('tag','--list',tag):
        raise ReleaseError(f'tag already exists: {tag}')
    path.write_text(name+'\n')
    git('add','--','VERSION')
    git('commit','-m',f'Release Ode {name}','--','VERSION')
    git('tag','-a',tag,'-m',f'Ode {name}')
    if git('rev-parse',tag+'^{commit}')!=git('rev-parse','HEAD'):
        raise ReleaseError('release tag does not identify HEAD')
    if git('status','--porcelain=v1','--untracked-files=all'):
        raise ReleaseError('working tree changed during release')
    return tag


def main():
    if sys.argv[1:]==['--help']:
        print('Usage: pypy3 tools/gen-ver.py MAJOR.MINOR[.PATCH]\nCreates a release commit and annotated tag; does not push.')
        return 0
    if len(sys.argv)!=2:
        raise ReleaseError('supply exactly one version; see --help')
    print(release(Path(__file__).resolve().parent.parent,sys.argv[1]))
    return 0


if __name__=='__main__':
    try:
        raise SystemExit(main())
    except (ReleaseError,subprocess.CalledProcessError,OSError) as error:
        print(f'REJECT: {error}',file=sys.stderr)
        raise SystemExit(1)
