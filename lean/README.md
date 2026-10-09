# Current Lean formalization

This directory publishes the **latest integrated formalization**, not the older main-checkout baseline. The retained namespace `TightVer401` is an engine name; it does not indicate the age of this snapshot.

- Source snapshot: `502220cc44850941449b848f7080e8828c731364` (see [snapshot metadata](audit/snapshot.json) for the exact authoritative ID).
- Final integration audit: `0d2e3fcfe73350a14d3734b6887dbda961190015`, **2026-10-09 01:37:31 UTC**.
- Recorded result: **PASS — 1,403 modules and 17,564 declarations**, with no admissions or custom axioms in the audited import closure.
- Full construction: **INCOMPLETE**. Both the unconditional existence theorem and `exists_noncongruent_isometric_tight_tori_pair_of_classical` remain pending.

## What is checked

The checked work includes the actual identity-holonomy band and compactly supported bending; exact equal-metric sign branches; signed annular degree; the full quadratic filling and its inverse; the normalized reflected saddle; and the same-meridian Gauss and affine-marker applications. Downstream theorems construct a noncongruent embedded tight pair **given the specified completed support/saddle inputs and explicit classical background parameters**.

These conditional consumers do not establish the existence of the original construction inputs. The remaining bottlenecks are the actual selected source/core placement, the universal ordinary connector-data family, and the incoming rebasing/relative smoothing that preserves the full open incoming germ and the required negative Hessian.

The [coverage register](coverage.json) records **17 proved, 3 partial and 20 pending** numbered manuscript statements. These counts are not an estimate of how much mathematical work remains. Extension applications, Cantor families and orbit-space topology are deferred in this formalization.

## Trust and source provenance

[The complete recorded kernel audit](audit/kernel-report.json) lists declaration types, transitive axioms, import dependencies and exact source hashes. [Snapshot metadata](audit/snapshot.json) identifies the source and publication adaptations. All audited Lean source bytes and vendored foundation bytes are preserved. Compiled objects, local caches, logs, old snapshots and unaudited WIP are excluded. Later frozen worker changes that were not integrated in this audit receive no transferred proof credit here.

The only permitted foundational axioms are `propext`, `Classical.choice` and `Quot.sound`. Four classical/external statements are explicitly registered in [classical-external-results.json](classical-external-results.json). They remain theorem parameters; defining their types does not prove them or grant the desired torus construction.

The exact mathematical target is the ver500 manuscript pinned by [target-lock.json](target-lock.json). Its byte-identical reference is bundled as [target/manuscript.tex](target/manuscript.tex) so coverage can be reproduced. A small [statement-reuse comparison record](target/reuse-statements.json) supports the historical statement-identity check; it contains no old proof engine or certificate. The [current readable paper](../paper/README.md) is ver503. This source audit does **not** assert a separate formal verification of every ver503 passage or figure.

Start with [blueprint/interfaces.md](blueprint/interfaces.md), which specifies the actual objects, dependencies, proved interfaces and remaining gates. It is the generated blueprint at this snapshot. The proof entry point is [TightVer401.lean](TightVer401.lean), and [Audit.lean](Audit.lean) performs the kernel axiom/admission audit.

## Reproduce the build

Requirements: Git, Python 3, and Lean's `elan`/`lake`. The audited compatibility profile uses **Lean 4.33.0-rc1** and **Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`**. The unmodified OpenAI sources are pinned to **`adc7f1241b42e322a6451854ab7e4b4c146bf78a`**; Schoenflies is pinned to **`05a43d29cde026618777db3d4e4316204ccca237`**. Their licenses and exact locks are included.

From the repository root:

```sh
cd lean
elan toolchain install leanprover/lean4:v4.33.0-rc1
lake update
lake exe cache get
python scripts/verify.py --jobs 3
```

On systems where Python is named `python3`, substitute that name. Use **the supplied builder/checker**, because a plain `lake build` does not apply the recorded source-compatibility transformations. Internet access is needed only to obtain the pinned Lean and Mathlib dependencies; the selected OpenAI and Schoenflies sources are included.

The verifier compiles the current import closure, verifies source/object/dependency hashes, rejects admissions and custom axioms, and checks coverage exports. Successful verification creates a new local `kernel-report.json`. The published integration record remains in `audit/kernel-report.json` for comparison. A copied report alone is not a validation of subsequent source edits.

Optional: set `VER401_LEAN` to the pinned Lean executable or `VER401_PACKAGES` to an existing directory containing the exact Mathlib checkout and its dependency packages. The builder verifies the compiler version and Mathlib revision. Each checkout must write its own `.lake/build`, compatibility sources and `build-logs`; share dependency caches read-only.

The recorded audit was performed on Windows. The launcher supports Windows and Unix executable names; a fresh Unix build has not been certified by this publication step. The package changes only executable discovery and the bundled manuscript/statement lookup, not any Lean proof or compatibility transformation.
