# ver503 formalization

Active proof engine: `/lean`; manuscript target: [`paper/paper.tex`](../paper/paper.tex), exact bytes pinned by [target-lock.json](target-lock.json). Namespace remains `TightVer401`.

The actual first-pair theorem [`exists_noncongruent_isometric_tight_tori_pair_of_classical`](TightVer401/NonrigidTorusPair.lean) is implemented with only `background : ClassicalExternalResults`, containing the two exact statements below. Smooth equal-image reparametrization and ellipse-axis recognition are now proved and supplied internally. All original first-pair construction gates are discharged in source. Direct compiler checks of the new proof leaves and reduced ultimate theorem passed; combined current-source verification **PASS** at `3a8f551` (Audit: 166.665 seconds). The earlier combined PASS at `07a2980` certifies the previous four-statement theorem. The full paper remains **INCOMPLETE**; extension and Cantor-family applications remain deferred.

## Current verification and actual construction

Full current-source verification **PASS** at `3a8f551901af2d613bd0950df4ee11fff462f79f` on `2026-10-09T18:31:19.661370+00:00` (Audit: 166.665 seconds). Both EXACT closed proof inhabitants and ONLY `ClassicalExternalResults` before the ultimate first existential are checked. The closure has no admissions or custom axioms; exactly two external statements remain. Historical source `07a2980` certified the earlier four-statement theorem. [Audit metadata](audit/snapshot.json) and [kernel report](audit/kernel-report.json) bind the current sources, compiled closure, pins and verification scripts.

The retained producers include the identity-holonomy band/nonzero supported bending, signed annular degree, full quadratic filling/inverse, normalized reflected saddle calculus, same-meridian convex closure/Gauss and affine marker applications. Source/reversed-gradient order and simultaneous source/scalar/gradient rebase preserve the same displaced inverse. The ver503 bridge proves the fixed affine normalization acts on vectors by negation and the transported bending is exactly `-Y` on the same source chart, with zero extension outside.

`actualSeed_exists_selected_single_prefix` constructs original selected geometry with NO premises. It internally chooses `N = 10000`, builds one corrected seed/native support chart, discards the earlier support-package field and selects FINAL nonzero compact `Y` after the visible-turn margin. The complete single prefix retains one final selected scalar and its actual gradient inverse, both clocks/traces, four normalized positive fillings and origin enclosures, strict selected Jordan nesting, exact protected support placement, actual gradient/tangent/visibility facts, a full-source closed homotopy and OPEN original-potential equality. Fixed prefix leaves are selected once; the common budget precedes the FINAL graphs.

`visibleConnectorIncomingParametersChoice_nonempty` constructs eta, its literal Gin family, one native inverse and one rho from arbitrary incoming `D` and positive `etaMax` alone. All phase/height, coefficient/lower-Delta, full negative-Gin-strip, whole-family visibility-domain and terminal radial/directional/excess thresholds are constructed before the single rho. The universal `visibleConnectorOrdinaryFamily_nonempty_from_incoming` then produces EXACT `Nonempty (VisibleConnectorWitnessAssemblyOrdinaryData D etaMax)` from those same two inputs. It derives actual raw source/topology/closure and Gin/raw seam jets, invokes full-domain smoothing once, and retains one final H with both genuine open boundary germs, full closed-band negative Hessian and actual terminal circle/angle/radial/tangent/enclosure/order facts. Its final gradient inverse is reconstructed from that SAME H; the raw source inverse is not substituted for it.

`actualSeed_exists_markedTorus_pair_of_ordinary_connector_family` connects the actual selected output projections to the existing pair caller. The ultimate theorem supplies its universal ordinary-family input locally using the concrete producer, leaving no paper-specific construction assumption. It produces actual smooth tight embedded tori with a common positive smooth Riemannian metric, exact native induced-form equality, noncongruent images, nonempty open agreement and no open planar patches.

The result retains the SAME completed `Gtilde/E/beta/Q/Cdata` tuple and once-chosen FULL `D.meridian`. Its maps are the actual affine marked base plus/minus the SAME transported bending; its open agreement set is exactly the complement of the same chart image of `tsupport Y`. Native inverse e, raw Cartesian source E and final H gradient inverse remain distinct objects throughout.

The 13 historical uncompiled IncomingGin leaves from `5176081` remain in [pending](pending/IncomingGin5176081/README.md), outside the certified closure; the concrete universal construction uses the current producers. [Frozen source review](research/coordination/ver503-frozen-review.md), [mathematical migration](research/coordination/ver503-mathematical-migration.md) and per-claim [reuse review](target/ver503-reuse-review.json) record provenance and exact manuscript scope. Coverage is a scope register, not a percentage of the construction.

## Exact external theorem parameters

The ultimate theorem now has ONLY `background : ClassicalExternalResults`. The [registry](classical-external-results.json) identifies the two retained exact statements:

- `ClassicalPositiveGaussTightnessClaim` (`background.positiveGaussTightness`).
- `ClassicalCoincidentEmbeddingFixedOpenClaim` (`background.coincidentEmbeddingFixedOpen`).

Their mathematical truth remains assumed. The former `reparam` and `axes` parameters are discharged by [`classicalEmbeddedImageReparametrization_proved`](TightVer401/ClassicalEmbeddedReparamProof.lean) and [`markerEllipseAxesRecognition_proved`](TightVer401/MarkerEllipseAxesRecognitionProof.lean). The first uses actual embedding range homeomorphisms and local smooth factor recovery through injective differentials; the second proves ellipse recognition directly. Both proof terms are supplied internally. No original geometry, scalar, inverse, marker, metric or final-pair construction is granted. The current combined certificate validates both closed proofs and the two-statement reduction. Extension and Cantor-family claims remain deferred.

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
