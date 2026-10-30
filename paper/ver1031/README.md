# ver1031: Isometric tight tori with different enclosed volumes

Author: **Yuetong Zhang**, Peking University.
Manuscript date: **October 31, 2026**.

This is local **ver617**, published in this repository as **ver1031**.
The manuscript, final roadmap PDF, and source archive are byte-for-byte
copies of the ver617 originals. The PDF is the final
`isometric_tight_tori_ver617_roadmap.pdf` identified by the revision record,
published here as `paper.pdf`.

- [Read the paper](paper.pdf)
- [LaTeX source](main.tex)
- [arXiv source archive](ver1031-arxiv-source.tar.gz)
- [Verification script](verify_ver1031.py)
- [Verification results](verification.json)
- [Original ver617 revision record](revision.json)

The introduction presents seven roadmap theorems: the main result, a starting
tight torus, preparation of its asymptotic curve, periodic ruled annuli, exact
insertion, a supported infinitesimal bending, and the isometric pair. Brief
method explanations accompany the construction theorems, followed by a short
preliminaries section. The construction uses a Codazzi-based bending formula
and a differentiated area identity to obtain nonzero normal flux.

## Rebuild and checks

From this directory, compile twice to resolve cross-references:

```sh
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
```

The source archive contains only `main.tex`; no external figures or separate
bibliography files are required.

With Python and SymPy installed, run:

```sh
python verify_ver1031.py
```

All **39 exact algebra and source-consistency checks pass**, including checks
that the 32 numbered equations from ver616 are preserved and the introduction
contains seven roadmap theorems. The SHA-256 of `main.tex` is:

```text
b0f873bf2d789eac340e52e50c0e20c381069a2331faa0223a3eb03a38e9c7a5
```

The original revision record retains local version numbers and filenames for
provenance. These checks do not certify the differential, geometric,
topological, or existence arguments in the manuscript. No formal proof
certificate for this version is asserted. The existing Lean audit targets
the earlier frozen ver503 source in [ver1009](../ver1009/README.md).

The previous published [ver1030](../ver1030/README.md) remains available.
