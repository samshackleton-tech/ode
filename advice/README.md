# advice/: numbers about speed, relied on for nothing

Nothing in this folder is read by a verifier, and no verdict depends on it. It holds what helps the coder
choose instructions: how fast instruction forms are on particular processors, and tests of how well such
numbers predict the speed of real code.

The rule (DESIGN.md, section 5): what a verdict relies on is in the instruction table `core/x86.tab`
and in the Lean model; what only helps a coder go faster is kept apart, here, keyed by the table's row names.

- `uops-test/`: a first test (November 20, 2026): can uops.info's per-processor table predict the cycles the
  16-way BLAKE3 kernel takes for a block? It ranks three processors correctly and is low by 17% to 35%.
