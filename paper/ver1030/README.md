# ver1030: Isometric tight tori with different enclosed volumes

Author: **Yuetong Zhang**, Peking University.
Manuscript date: **October 30, 2026**.

This is local **ver614**, published in this repository as **ver1030**.
The manuscript, PDF, and source archive are byte-for-byte copies of the
ver614 originals. The verification script is included as `verify_ver1030.py`.

- [Read the paper](paper.pdf)
- [LaTeX source](main.tex)
- [arXiv source archive](ver1030-arxiv-source.tar.gz)
- [Verification script](verify_ver1030.py)
- [Verification results](verification.json)

The manuscript constructs isometric smooth embedded tight tori with different
enclosed volumes. Its route starts with a closed asymptotic curve from the
annulus of Banks, Ghomi, Qiu, and Raffaelli. Section 3 uses their existing
curvature argument with a flat end profile, then gives a geometric completion
to a tight torus using Gauss--Bonnet. A modification near the retained curve
produces a supported infinitesimal bending with nonzero normal flux;
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
python verify_ver1030.py
```

All **14 exact algebra and source-consistency checks pass**. The script also
records the SHA-256 of `main.tex`:

```text
37b11d55d4ae5f901f969a00a510e8b82cd779ecd70eebcf2d5ea5b0c74cec8a
```

These checks cover symbolic identities and reference consistency. Analytic,
topological, and existence arguments remain in the manuscript; no Lean
certificate for this version is asserted. The repository's existing Lean
audit targets the earlier frozen ver503 source in [ver1009](../ver1009/README.md).
