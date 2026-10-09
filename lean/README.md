# ver503 formalization

Active proof engine: `/lean`; manuscript target: [`paper/paper.tex`](../paper/paper.tex), exact bytes pinned by [target-lock.json](target-lock.json). Namespace remains `TightVer401`.

The canonical [`exists_noncongruent_isometric_tight_tori_pair`](TightVer401/NonrigidTorusPair.lean) is **unconditionally proved**, with no background or construction premises. All four background propositions have closed proofs. It constructs two smooth tight embedded tori with one common smooth positive induced metric, noncongruent images, nonempty open agreement and no open planar patches. The full manuscript remains **INCOMPLETE**; Cantor-family and extension applications are deferred.

Read the [formalization report](formalization-report.md) for exact paper coverage, important general infrastructure in several fields, inherited foundations and potential contributions to Lean. The [library catalog](TightVer401/Library/README.md) groups reusable imports into Calculus, Topology, Analysis, Riemannian, DifferentialGeometry and Construction.

## Current verification and actual construction

Full current-source verification **PASS** at `a733b93d31cf80a2b2a4d3654890029cbe200b69` on `2026-10-09T20:30:18.604546+00:00` (Audit: 162.584 seconds). All FOUR exact closed background proofs, the closed bundle, the premise-free canonical theorem and its full kernel-checked result type are certified. The closure has no admissions or custom axioms.

The [snapshot](audit/snapshot.json) binds the 1,536-module, 18,332-declaration closure to the current [kernel report](audit/kernel-report.json). Counts include helpers, definitions, generated declarations and inherited results; they are not distinct published theorems or a completion percentage.

The retained producers include the identity-holonomy band/nonzero supported bending, signed annular degree, full quadratic filling/inverse, normalized reflected saddle calculus, same-meridian convex closure/Gauss and affine marker applications. Source/reversed-gradient order and simultaneous source/scalar/gradient rebase preserve the same displaced inverse. The ver503 bridge proves the fixed affine normalization acts on vectors by negation and the transported bending is exactly `-Y` on the same source chart, with zero extension outside.

`actualSeed_exists_selected_single_prefix` constructs original selected geometry with NO premises. It internally chooses `N = 10000`, builds one corrected seed/native support chart, discards the earlier support-package field and selects FINAL nonzero compact `Y` after the visible-turn margin. The complete single prefix retains one final selected scalar and its actual gradient inverse, both clocks/traces, four normalized positive fillings and origin enclosures, strict selected Jordan nesting, exact protected support placement, actual gradient/tangent/visibility facts, a full-source closed homotopy and OPEN original-potential equality. Fixed prefix leaves are selected once; the common budget precedes the FINAL graphs.

`visibleConnectorIncomingParametersChoice_nonempty` constructs eta, its literal Gin family, one native inverse and one rho from arbitrary incoming `D` and positive `etaMax` alone. All phase/height, coefficient/lower-Delta, full negative-Gin-strip, whole-family visibility-domain and terminal radial/directional/excess thresholds are constructed before the single rho. The universal `visibleConnectorOrdinaryFamily_nonempty_from_incoming` then produces EXACT `Nonempty (VisibleConnectorWitnessAssemblyOrdinaryData D etaMax)` from those same two inputs. It derives actual raw source/topology/closure and Gin/raw seam jets, invokes full-domain smoothing once, and retains one final H with both genuine open boundary germs, full closed-band negative Hessian and actual terminal circle/angle/radial/tangent/enclosure/order facts. Its final gradient inverse is reconstructed from that SAME H; the raw source inverse is not substituted for it.

`actualSeed_exists_markedTorus_pair_of_ordinary_connector_family` connects the actual selected output projections to the existing pair caller. The ultimate theorem supplies its universal ordinary-family input locally using the concrete producer, leaving no paper-specific construction assumption. It produces actual smooth tight embedded tori with a common positive smooth Riemannian metric, exact native induced-form equality, noncongruent images, nonempty open agreement and no open planar patches.

The result retains the SAME completed `Gtilde/E/beta/Q/Cdata` tuple and once-chosen FULL `D.meridian`. Its maps are the actual affine marked base plus/minus the SAME transported bending; its open agreement set is exactly the complement of the same chart image of `tsupport Y`. Native inverse e, raw Cartesian source E and final H gradient inverse remain distinct objects throughout.

The 13 historical uncompiled IncomingGin leaves from `5176081` remain in [pending](pending/IncomingGin5176081/README.md), outside the certified closure; the concrete universal construction uses the current producers. [Frozen source review](research/coordination/ver503-frozen-review.md), [mathematical migration](research/coordination/ver503-mathematical-migration.md) and per-claim [reuse review](target/ver503-reuse-review.json) record provenance and exact manuscript scope. Coverage is a scope register, not a percentage of the construction.

## Proved background statements

The [registry](classical-external-results.json) has no remaining grants. It records these exact closed proofs:

- [`classicalEmbeddedImageReparametrization_proved`](TightVer401/ClassicalEmbeddedReparamProof.lean): smooth reparametrization of equal-image actual embeddings.
- [`markerEllipseAxesRecognition_proved`](TightVer401/MarkerEllipseAxesRecognitionProof.lean): recognition of unequal ellipse axes.
- [`classicalCoincidentEmbeddingFixedOpen_proved`](TightVer401/ClassicalCoincidentEmbeddingFixedOpenProof.lean): equal-image embeddings with equal induced forms and open agreement coincide.
- [`classicalPositiveGaussTightness_proved`](TightVer401/ClassicalPositiveGaussTightnessProof.lean): an actual Gauss chart of the entire positive-curvature locus onto a finitely punctured sphere implies tightness.

The rigidity proof uses the genuine compatible intrinsic metric and actual C¹ path-distance infimum. The Gauss proof uses regular directions, curvature and normal signs at maxima, connected components and approximation. Neither uses a construction grant. [`classicalExternalResults_proved`](TightVer401/ClassicalExternalProof.lean) inhabits the retained bundle; conditional helper interfaces remain reusable with these proved inputs.

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
