# Releasing Ode

`VERSION` is the single release number, printed by `pypy3 -m ode --version`.
Ode's 0.1 series is a research prototype; [QUALITY.md](QUALITY.md) states its
assurance boundary. Release numbers, kernel format versions, and semantic
hash-domain revisions serve separate purposes. Follow [DOMAINS.md](DOMAINS.md)
whenever an interpretation changes.

## Procedure

Use a clean checkout on a branch, with Git author identity configured.
Commit reviewed source, docs, tests, generated artifacts, and pins first.

```sh
pypy3 game/pin_ode_base.py
pypy3 -m unittest discover -s tests
pypy3 game/kernel_attacks.py
# Review and commit any refreshed code/pins before proceeding.
pypy3 tools/gen-ver.py 0.1
```

The tool accepts `MAJOR.MINOR` or `MAJOR.MINOR.PATCH`; `0.1` becomes `0.1.0`.
It requires an increasing version, an unused tag, and a clean working tree
including untracked files. It updates only `VERSION`, makes one commit,
and creates an annotated `v0.1.0` tag identifying that commit. Failures stop
with completed work intact for inspection. Run one release operation at a
time; concurrent edits, commits, and hooks that modify the tree are outside
this workflow's contract.

After verifying the release checkout:

```sh
pypy3 -m ode --version
git show v0.1.0 --stat
git push --atomic origin main v0.1.0
```

Use the actual new version/tag on subsequent releases. The tool performs no
network operations and creates no GitHub Release page. The annotated Git
tag is the release marker; its commit supplies source provenance without
embedding a self-referential commit hash in the version file.

## Origin of the tool

The workflow is inspired by [zooko/bench-hashes `tools/gen-ver.py` at
63ee3ae](https://github.com/zooko/bench-hashes/blob/63ee3ae04f56c61db08de8f938a0854d4619de27/tools/gen-ver.py).
Ode's implementation keeps the preconditions and explicit commit/tag steps.
It uses a plain version file instead of Cargo manifest/lock updates and a
single release commit instead of the upstream build-metadata commit pair.
Tests exercise it in disposable repositories, including dirty trees,
duplicate tags, invalid/decreasing versions, and detached HEADs.
