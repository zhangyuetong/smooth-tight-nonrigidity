# An embedded band foliated by closed asymptotic lines and nonrigid smooth tight tori

Manuscript version: **ver503**.

- [Read the paper](paper.pdf).
- [LaTeX source](paper.tex).
- `figures/` contains the six PDF figures required by the source.

The figures show the balanced band and its local geometry, the bending map,
other identity-return bands, the seed curves, the completion process, and
the Cantor sign family. Captions distinguish numerical illustrations and
schematic sketches from the analytic construction.

## Build

From this directory, with a TeX distribution and `latexmk` installed:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex
```

The bibliography is included in `paper.tex`; no separate bibliography file
or running web interface is needed.
