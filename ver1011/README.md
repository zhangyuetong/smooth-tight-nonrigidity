# ver505: arXiv submission files

Author: **Yuetong Zhang**, Peking University.
Contact: **gzhangyuetong@gmail.com** (permanent), **2300010810@stu.pku.edu.cn** (university).

- [Read ver505](paper.pdf)
- [Download the arXiv source ZIP](ver505-arxiv-source.zip)
- [LaTeX source and six required figures](source/)
- [Submission metadata](metadata.txt)
- [Preparation checks](validation.json)
- [Original GitHub wording and provenance](provenance/)

This version includes the full definition review, the acknowledgement to
Xiang Ma, the AI-use account from the GitHub README, with grammar and
formatting corrected and its October 10 update replacing the earlier
correctness statement. The account appears before the technical appendices. The earlier illustrated paper is preserved in
[ver1009](../ver1009/README.md).

## Submit to arXiv

1. Start a new mathematics submission; the relevant category is `math.DG`.
2. Upload **ver505-arxiv-source.zip**. Its root contains `paper.tex` and
   `figures/`; choose **pdfLaTeX**, **TeX Live 2025**, and `paper.tex` as the main file.
3. Copy the title, author and abstract from `metadata.txt`. A non-exclusive
   arXiv distribution license is the minimal distribution option; choose and
   accept the license in your own submission account.
4. Inspect the PDF produced by arXiv, including every figure and the AI-use account,
   then complete the remaining account, endorsement and submission steps.

`paper.pdf` here is a preview. Upload the source ZIP rather than that PDF
alone: arXiv requires the source for a TeX-authored paper. The ZIP contains
only the manuscript and its six used PDF figures, with case-matching paths.
Metadata, this guide, provenance and validation records stay outside the ZIP.
No manually constructed `00README` is needed for this single-main-file paper.

## Rebuild

From `source/` run:

```sh
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error paper.tex
```

The references are in `paper.tex`; no BibTeX, downloaded assets, custom fonts,
or external rendering commands are required. See [arXiv source instructions](https://info.arxiv.org/help/submit_tex.html),
[TeX Live support](https://info.arxiv.org/help/faq/texlive.html),
[author metadata rules](https://info.arxiv.org/help/prep.html), and
[generative-AI policy](https://info.arxiv.org/help/moderation/index.html#policy-for-authors-use-of-generative-ai-language-tools).

The existing Lean audit targets the frozen manuscript under `paper/`.
It is retained as the original source snapshot; it is not a new audit of ver505.
