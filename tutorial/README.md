# AutoCorrode Tutorial

A Beamer slide deck generated from formally-checked Isabelle/HOL theories.
Every slide is a live theory: definitions, types, lemmas, and proofs shown
in the PDF were type-checked at build time, so the deck cannot compile if a
referenced fact stops being true.

The deck is intended both as a guided walkthrough of AutoCorrode and as an
experimentation ground -- open the sources in jEdit, change a definition or
a contract, and watch which proofs still go through.

## Layout

- `ROOT` -- Isabelle session `AutoCorrodeTutorial`, inheriting the
  `AutoCorrode` parent session.
- `Slides.thy` -- outer-syntax commands (`slide`, `end_slide`,
  `interlude`, ...) that emit Beamer frame markup from `.thy` files.
- `Tutorial_*.thy` -- one theory per topic (preamble, monads, Hoare logic,
  separation logic, etc.). Loaded in order from `document/root.tex`.
- `document/root.tex` -- Beamer document skeleton; chooses which
  `Tutorial_*.tex` are included and in what order.
- `Makefile` -- thin wrapper around `isabelle build`. Common targets:
  `make heaps` (parent image), `make build`, `make view`, `make jedit`,
  `make clean`.
- `output/` -- Isabelle's session output directory; `output/document.pdf`
  is copied to `autocorrode_tutorial.pdf`.

## Build

```
make heaps    # one-off: build the AutoCorrode parent heap
make          # build the tutorial PDF -> autocorrode_tutorial.pdf
make view     # build then open the PDF (macOS)
make jedit    # open the tutorial theories in jEdit
```

Override `ISABELLE_HOME` if the Isabelle binary lives somewhere other than
`/Applications/Isabelle2025-2.app/bin`:

```
make ISABELLE_HOME=/path/to/Isabelle/bin build
```

The same target is available from the repository root as `make tutorial`.
