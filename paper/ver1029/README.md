# ver1029: Isometric tight tori with different enclosed volumes

Author: **Yuetong Zhang**, Peking University.
Manuscript date: **October 29, 2026**.

This is local **ver613**, published in this repository as **ver1029**.
The manuscript, PDF, and source archive are byte-for-byte copies of the
ver613 originals. The verification script is included as `verify_ver1029.py`.

- [Read the paper](paper.pdf)
- [LaTeX source](main.tex)
- [arXiv source archive](ver1029-arxiv-source.tar.gz)
- [Verification script](verify_ver1029.py)
- [Verification results](verification.json)

The manuscript constructs isometric smooth embedded tight tori with different
enclosed volumes. Its route starts with a closed asymptotic curve from the
annulus of Banks, Ghomi, Qiu, and Raffaelli, modifies the ends to infinite-order
planar contact, and completes the annulus to a tight torus. A modification near
the curve produces a supported infinitesimal bending with nonzero normal flux;
opposite multiples give the proposed pair. The existence and implication
theorems state their hypotheses explicitly.

## Rebuild and checks

From this directory, compile twice to resolve cross-references:

```sh
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
```

The source archive contains only `main.tex`. There are no external figures or
separate bibliography files.

With Python and SymPy installed, run:

```sh
python verify_ver1029.py
```

All **17 exact algebra and source-consistency checks pass**. The script also
records the SHA-256 of `main.tex`:

```text
694e1fd0c965e43580f06f23ce388c29d4dd54c0fc37231c11b5ac2149f9e9b7
```

These checks cover symbolic identities and reference consistency. Analytic,
topological, and existence arguments remain in the manuscript; no Lean
certificate for this version is asserted. The repository's existing Lean
audit targets the earlier frozen ver503 source in [ver1009](../ver1009/README.md).
