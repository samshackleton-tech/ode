# Ode: A Language for Native Machine Code That Carries Its Proof

The language report is [`ODE.pdf`](ODE.pdf) (Revision 9, November 2026).

This page is only a pointer. The report has one source, [`ode.typ`](ode.typ), so that no second copy of
its text can drift from the first.

How the report is made:

- `pypy3 paper/render-paper.py` makes [`facts.json`](facts.json) (numbers worked out from the repository),
  the figures in [`figures/`](figures/), and `ODE.pdf` (with [Typst](https://typst.app)).
- The listings in the report are read from files that the tests compile and verify:
  [`examples/all_zero.ode`](examples/all_zero.ode), [`examples/quad.ode`](examples/quad.ode),
  and two contracts in `proof-core/`.
- `pypy3 paper/test_paper.py` checks that the facts are current and, where the verifier is built,
  that the report's example is verified for both processors with the sizes the report prints.
- `pypy3 paper/cold_edit.py paper/ODE.pdf` sends the rendered pages, and nothing else, to an editor
  that has not seen the project.
