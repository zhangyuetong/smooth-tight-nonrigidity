# ver503 formalization

Active proof engine: `/lean`; manuscript target: [`paper/paper.tex`](../paper/paper.tex), exact bytes pinned by [target-lock.json](target-lock.json). Namespace remains `TightVer401`.

The first-pair construction remains **INCOMPLETE**. Neither the unconditional existence theorem nor `exists_noncongruent_isometric_tight_tori_pair_of_classical` is present. Extension and Cantor-family applications remain deferred.

## Current checked checkpoint

A full combined current-source integration verification passed against source commit `96ff7f8` and the exact ver503 manuscript (Audit: 196.966 seconds). [Audit metadata](audit/snapshot.json) binds the [kernel report](audit/kernel-report.json) to source, target, toolchain and dependency hashes. The certified closure has no admissions or custom axioms; the first-pair construction remains incomplete.

The retained original producers include the identity-holonomy band/nonzero supported bending, signed annular degree, full quadratic filling/inverse, normalized reflected saddle calculus, same-meridian convex closure/Gauss and affine marker applications. Checked downstream consumers produce the literal marked pair from actual completed support/saddle inputs, one chosen full meridian and explicit classical theorem parameters.

Newly validated frozen results derive canonical source/reversed-gradient order from honest signed-degree premises, retain central fields for the SAME chosen displaced inverse, and rebase source/scalar/gradient simultaneously. The ver503 bridge proves the fixed affine normalization acts on vectors by negation and the transported field is exactly `-Y` on the SAME source chart; the existing extension is zero outside. These are useful checked exports, not completed original connector inputs.

This checked checkpoint adds full smoothing-carrier/boundary/side producers, actual source chart and boundary-separation producers, and connections retaining the final protected field and the final scalar's own gradient inverse. The integrated Gin seam jets, raw scalar and once-only full-domain smoothing application retain their actual hypotheses. [The exact first-pair obligation audit](research/coordination/ver503-first-pair-obligations.md) lists the absent ultimate theorem, named external statements and remaining inputs. The complete original selected geometry and D-only coherent parameter choice are now checked actual producers; universal ordinary-family construction and the final pair application remain unfinished.

`actualSeed_exists_selected_single_prefix` is now checked with NO premises. It internally chooses `N = 10000`, builds one corrected seed/native support chart, and selects FINAL nonzero compact `Y` after the visible-turn margin. The complete single-prefix output retains one final scalar and its own actual gradient inverse, both clocks/traces, four normalized positive fillings and origin enclosures, strict selected Jordan nesting, exact protected support placement, actual gradient/tangent/visibility facts, a full-source closed homotopy and OPEN original-potential equality. Fixed prefix leaves are selected once; the common budget precedes the FINAL graphs. The original selected source/core construction gate is closed.

`visibleConnectorIncomingParametersChoice_nonempty` constructs coherent choices from arbitrary incoming `D` and positive `etaMax` alone: eta, its literal Gin family, one native inverse and one rho, with coefficient/lower-Delta signs, phase/height facts, full negative Gin strip, whole-family visibility-domain homotopy strip and terminal filling. Primitive terminal radial/directional/excess thresholds are constructed and intersected before that single rho.

The checked concrete Cartesian smoothing application derives the literal old-height classifier, exact zero seam, regular injective seam, negative normal and compact full-band carrier, then constructs final H with full-domain negative Hessian and genuine open boundary germs from actual Gin/raw jets and domain inputs. The D-only parent scalar and universal `VisibleConnectorWitnessAssemblyOrdinaryData` assembly remain unfrozen work in progress. Root must finish that universal producer and connect the actual selected output projections to the final pair caller. [The exact obligation audit](research/coordination/ver503-first-pair-obligations.md) records these remaining same-object obligations.

## Remaining original construction gates

| Gate | Required producer | Final consumer |
|---|---|---|
| Final selected-to-pair application | Project the checked premise-free seed/single-prefix witnesses to exact caller conventions, preserving clocks, scalar/inverse and FINAL Y | `exists_markedTorus_pair_of_negative_gradient_order` |
| Universal incoming-to-ordinary assembly | Consume the checked D-only coherent eta/e/rho choice; convert retained primitive terminal signs and instantiate SAME rebased/raw/smoothing data | Final relative-smoothing application and ordinary data |
| Final scalar H | Instantiate the SAME actual Gin/raw jets and side-domain Hessian facts; invoke the checked concrete smoothing producer once on full V and reconstruct H's own gradient inverse | `VisibleConnectorWitnessAssemblyOrdinaryData` |
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
