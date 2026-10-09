# Current ver503 formalization

Active proof engine: `/lean`; manuscript target: [`paper/paper.tex`](../paper/paper.tex), exact bytes pinned by [target-lock.json](target-lock.json). Namespace remains `TightVer401`.

The first-pair construction remains **INCOMPLETE**. Neither the unconditional existence theorem nor `exists_noncongruent_isometric_tight_tori_pair_of_classical` is present. Extension and Cantor-family applications remain deferred.

## Current checked checkpoint

A fresh full integration verification passed on 2026-10-09 at 14:30:39 UTC against source commit `fc8d7997c66d386842c41373ae46dfb92ce47f85` and exact ver503 target SHA256 `a809ad8ef4810fcdf61fd2511cb389b1ba4816478f309b42c729a69ed586bf9a`. [Audit metadata](audit/snapshot.json) binds the current [kernel report](audit/kernel-report.json) to source, target, toolchain, foundation/dependency and migration-review hashes. There are no admissions or custom axioms in the certified import closure. The ver500 certificate is retained as historical provenance; it was not transferred as a ver503 certificate.

The retained original producers include the identity-holonomy band/nonzero supported bending, signed annular degree, full quadratic filling/inverse, normalized reflected saddle calculus, same-meridian convex closure/Gauss and affine marker applications. Checked downstream consumers produce the literal marked pair from actual completed support/saddle inputs, one chosen full meridian and explicit classical theorem parameters.

Newly validated frozen results derive canonical source/reversed-gradient order from honest signed-degree premises, retain central fields for the SAME chosen displaced inverse, and rebase source/scalar/gradient simultaneously. The ver503 bridge proves the fixed affine normalization acts on vectors by negation and the transported field is exactly `-Y` on the SAME source chart; the existing extension is zero outside. These are useful checked exports, not completed original connector inputs.

## Remaining original construction gates

| Gate | Required producer | Final consumer |
|---|---|---|
| Selected source/core geometry | Actual strict nesting of selected graphs, protected support between them, original-potential open agreement | `exists_markedTorus_pair_of_negative_gradient_order` |
| Compatible incoming rebase | SAME inverse; actual seam embedding/value/gradient matching; displaced terminal geometry; eta-first/rho-second common bounds | Final relative-smoothing application and ordinary data |
| Final scalar H | Full fixed V, Gin/raw on actual side domains, both genuine open boundary germs, negative Hessian on entire required closed band | `VisibleConnectorWitnessAssemblyOrdinaryData` |
| Ordinary connector family | Actual universal ordinary data with F/O/terminal/boundary facts, using final H's own reconstructed gradient inverse | Completion/pair consumers, then ultimate first-pair theorem |

No original first-pair construction gate is closed by importing an equivalent conditional wrapper. Full incoming open equality cannot be replaced by matching first jets. Native inverse e, Cartesian inverse E and the final H gradient inverse are distinct objects with required same-object identifications.

The 13 uncompiled IncomingGin leaves from `5176081` are preserved separately in [pending](pending/IncomingGin5176081/README.md), outside the certified closure. [Frozen source review](research/coordination/ver503-frozen-review.md) and [mathematical migration](research/coordination/ver503-mathematical-migration.md) record exact provenance, reuse and remaining obligations. Per-claim [reuse review](target/ver503-reuse-review.json) binds all current statement hashes, including changed support/holonomy/protected-realization/localized-sign passages. Coverage is a scope register, not a percentage of the construction.

## Exact external theorem parameters

The [registry](classical-external-results.json) retains four explicit statements with references and consumers:

- `ClassicalPositiveGaussTightnessClaim` and `ClassicalCoincidentEmbeddingFixedOpenClaim`, bundled in `ClassicalExternalResults`.
- `ClassicalEmbeddedImageReparametrizationClaim`, separately supplied.
- `MarkerEllipseAxesRecognition`, separately supplied.

Their definitions and conditional applications are kernel checked; their mathematical truth remains assumed. No inhabitant or original construction data is granted. Every actual geometry, inverse, marker, metric and final-pair input must be produced.

## Reproduce the current build

Requirements: Git, Python 3 and Lean/elan. Pins: Lean `4.33.0-rc1`, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, OpenAI/math `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, Schoenflies `05a43d29cde026618777db3d4e4316204ccca237`.

```sh
cd lean
elan toolchain install leanprover/lean4:v4.33.0-rc1
lake update
lake exe cache get
python scripts/verify.py --jobs 3
python scripts/build_blueprint.py
```

Use the supplied builder/checker; plain `lake build` does not apply the recorded compatibility transformations. Compiler lookup is portable; the new verification was performed on Windows. Optional `VER401_LEAN` and `VER401_PACKAGES` select the pinned executable and read-only packages. Each checkout owns `.lake/build`, compatibility sources and `build-logs`. A copied report or cache does not validate source edits; the builder and full verifier check current source/dependency/object/log hashes.

For concurrent Windows worktrees follow [SESSION_WORKTREES.md](../SESSION_WORKTREES.md), [COORDINATION.md](../COORDINATION.md), the [rebuilt precise blueprint](blueprint/interfaces.md) and [frozen consumers](research/coordination/ver503-consumer-contract.md). Parent chats are their worktrees' sole compiler writers; subagents use exclusive source leaves or read-only reviews. The publication excludes caches, compiled binaries and bulk logs, preserving personal README additions and timestamp files.
