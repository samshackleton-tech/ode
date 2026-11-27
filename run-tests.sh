#!/bin/sh
# Run the active Ode test suite in parallel with pytest + pytest-xdist.
#
#   ./run-tests.sh                  # all active suites (pyproject.toml testpaths)
#   ./run-tests.sh lang/test_hl.py  # any subset or extra pytest flags
#   PYTEST=/path/to/pytest ./run-tests.sh
set -eu

here=$(cd "$(dirname "$0")" && pwd)
cd "$here"

lake=$(command -v lake || true)
if [ -z "$lake" ] && [ -x "$HOME/.elan/bin/lake" ]; then
    lake="$HOME/.elan/bin/lake"
fi

if [ -n "$lake" ] && [ "${ODE_SKIP_LEAN_BUILD:-0}" != "1" ]; then
    (
        cd "$here/proof-core"
        PATH="$(dirname "$lake"):$PATH" "$lake" build odeverify odeprove odespec arith odemachine SoundTop
    )
    export ODE_LEAN_BUILT=1
fi

if [ -n "${PYTEST:-}" ]; then
    exec "$PYTEST" "$@"
fi

if command -v pytest >/dev/null 2>&1 && pytest --help 2>/dev/null | grep -q -- '--dist'; then
    exec pytest "$@"
fi

if command -v uv >/dev/null 2>&1; then
    if command -v pypy3 >/dev/null 2>&1; then
        exec uv run --python pypy3 --with pytest --with pytest-xdist pytest "$@"
    fi
    exec uv run --with pytest --with pytest-xdist pytest "$@"
fi

echo "run-tests.sh: install pytest and pytest-xdist (or uv), or set PYTEST=/path/to/pytest" >&2
exit 1
