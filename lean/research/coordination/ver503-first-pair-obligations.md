# ver503 first-pair obligation audit

Read-only source review on 2026-10-09 in `ver503-integration`, HEAD `1a33fdf` (with concurrent working-tree changes). This document records source interfaces, not a fresh compiler certificate. Root remains the sole integration compiler.

## Actual caller and absent ultimate theorem

`TightVer401/TorusMarkedGradientOrderPairConnection.lean` declares `exists_markedTorus_pair_of_negative_gradient_order`. It is an actual conditional pair producer: once its original construction inputs are supplied, it returns the two maps, their common smooth positive Riemannian metric, embedding, tightness, image noncongruence, nonempty open agreement and no open planar patches. It also retains the full completed scalar/geometry tuple.

Searching `lean/TightVer401` for `exists_noncongruent_isometric_tight_tori_pair_of_classical` finds no source declaration. `lean/TightVer401/NonrigidTorusPair.lean` does not exist. The name occurs in blueprint and registry metadata as a target. Consequently the actual caller above must not be reported as the ultimate first-pair theorem: it still takes paper-specific construction hypotheses, especially a universal ordinary connector family.

## Explicit external parameters

The actual caller retains three parameters comprising four exact statements:

- `background : ClassicalExternalResults`, in `ClassicalExternal.lean`: `positiveGaussTightness : ClassicalPositiveGaussTightnessClaim` and `coincidentEmbeddingFixedOpen : ClassicalCoincidentEmbeddingFixedOpenClaim`. The former consumes an actual embedded torus, smooth orthogonal global normal, and a smooth Gauss inverse whose source is exactly the actual positive-curvature locus and target is the sphere minus a finite set. The latter consumes two actual embeddings, equal actual native induced forms, equal entire images, and nonempty open map agreement, and returns equality of maps.
- `reparam : ClassicalEmbeddedImageReparametrizationClaim`, in `ClassicalEmbeddedReparam.lean`: equal embedded images give a source homeomorphism smooth in both directions with `Y (e p) = X p`.
- `axes : MarkerEllipseAxesRecognition`, in `TorusAffineMarkerEllipseBasic.lean`: an affine isometry carrying a noncircular axis-aligned ellipse to its translate carries its center to the other center and acts by coordinate signs.

These are the named grants in `lean/classical-external-results.json`. Their types and applications do not prove the statements or provide original torus/connector data. The ultimate theorem must retain them explicitly; no desired construction package is an external premise.

## Original inputs still to assemble at the actual caller

All names below are the exact assumptions of `exists_markedTorus_pair_of_negative_gradient_order`.

| Caller assumptions | Same-object producer or remaining assembly |
| --- | --- |
| `hOrdinary` | For every `Gin`, open-domain data `Uin`, radius `R`, `D : VisibleConnectorIncomingData Gin Uin 1 R` and positive `etaMax`, produce `Nonempty (VisibleConnectorWitnessAssemblyOrdinaryData D etaMax)`. An exit-specific connector or a conditional assembly wrapper does not inhabit this universal input. Actual Incoming, RawPotential and full-smoothing leaves must be instantiated together. |
| `e0`, `hG`, `hNegative`, `heG`, `hInverse` | Retain the final selected `Gexit`, its actual smooth gradient chart and smooth inverse. `PositiveExitConstructionSelectedPatches.lean` / `positiveExit_exists_two_selected_visible_cartesian_patches` produces the selected scalar and subtype gradient inverse. `PositiveExitConstructionFinalGradientConnection.lean` / `positiveExit_final_gradient_cartesian_connection` transports the same chart to ambient Cartesian coordinates. Root must apply it to the retained witness; a raw connector inverse is not an inverse for a smoothed scalar. |
| `hpPlus`, `hpMinus`, `hgPlus`, `hgMinus`; `hpMinus0`, `hgPlus0`, `hgMinus0` | Four actual normalized `DualRadialCompletionPositiveTrace` witnesses and three origin enclosures. Reuse the selected trace and `DualRadialCompletionExitApplicationPeriod.lean` / `dualRadialCompletionExitApplicationPeriod_positive_traces` with the same clocks and graphs; retain their parametrizations and inside identities. |
| `hSourceNested` | Actual strict inclusion `closure (HpMinus '' ball 0 1) ⊆ HpPlus '' ball 0 1)`. Selected source-order/nesting leaves are producers to instantiate, not permission to assume this inclusion. The caller derives reversed gradient order internally; it does not require it as another hypothesis. |
| `H`, `hH0`, `hH1`, `hclosed`, `hHU` | One closed-loop source homotopy from the same normalized `pMinus` to `pPlus`, entirely in `angularDescentComplex '' e0.source`. `PositiveExitConstructionSelectedHomotopyPair.lean` / `positiveExit_actual_selected_pair_source_homotopy` and its Fermi/join leaves are available; root must connect their exact source domain to the retained Cartesian chart. Endpoint curves alone do not prove `hHU`. |
| `hActualPlus`, `hActualMinus`, `hPairPlus`, `hPairMinus` | Exact gradient image and positive tangent pairing of those same four traces. Selected patch/normalization exports supply these after rewriting the SAME `e0 = planarGradient Gexit` on its source. |
| `hRPlus`, `hRMinus`, `hVisPlus`, `hVisMinus` | Positive radii and exact `ComplexVisiblePair` facts, with the lower pair specifically `corrugatedReverseReflect gammaMinus` and `I * corrugatedReverseReflect pMinus`. Keep the actual selected visibility, reflection and clock normalization. |
| `hCore` | `c0 '' tsupport Y` lies inside the exact selected source annulus. Root must connect the retained final protected field to selected strict source/core-placement producers. Compact support by itself does not imply this placement. |
| `hw`, `hc0`, `hci0`, `hBand` | Positive band width, smooth native chart and inverse, and `planarSupportMap G0 (c0 p) = d.bandMap p` on that chart. Reuse the actual identity-band support chart for the same seed frame `d`, width and `G0`. |
| `hY`, `hcompact`, `hnonzero`, `hKsource` | SAME final band bending `Y`, compact and nonzero, with support inside `c0.source`. Choose it once using `positiveExit_same_seed_visible_turn_protected_field`; consume `PositiveExitConstructionFinalSeedConnection.lean` / `positiveExit_final_seed_support_connection` and `positiveExit_final_band_bending_transfer` for its actual identity-band coordinates. Do not mix the earlier seed field with a later margin-selected field. |
| `hO`, `hKO`, `hOldEq` | One open protected neighborhood `O` containing `c0 '' tsupport Y`, with `EqOn Gexit G0 O`. The actual patch change support/complement and selected protected margins must provide it for the same final scalar; pointwise equality on the support is insufficient. |

Root's seed and selected-patch assembly must choose the corrected seed, phase clocks, common margin, protected field and selected scalar once. Current leaves do not yet constitute a declaration that eliminates all of these original hypotheses.

## Ordinary-family construction conditions

`VisibleConnectorWitnessAssemblyInputs.lean` defines `VisibleConnectorWitnessAssemblyOrdinaryData D etaMax`. Its fields are substantive construction obligations: `0 < eta < etaMax`; one final scalar `G` smooth on open `U`; actual terminal facts and increasing angle with full turn, terminal gradient circle and positive radial source; strict source and reversed-gradient nesting; the entire physical source closure inside `U` with negative actual Hessian there; an open incoming neighborhood containing the incoming curve and lying in `U ∩ Uin` on which `G = Gin`; and one source map `F` smooth on open `O` covering the closed round band, with positive actual annular Jacobian and exact incoming/terminal boundary traces.

Existing producer chain must preserve these objects:

1. Fix the rotation `eta` before its actual displaced Gin family. Select one native inverse and its real phase `a`/height `b`, then one positive `rho` satisfying all compatible bounds. Root reports frozen worker2 revision `c64229f` has `ParametersCoefficients` and `ParametersSigns.uniform_actual_coefficient_signs` for actual joint coefficient calculus/sign persistence. These modules are not yet present under the reviewed integration `lean/TightVer401`; their import/audit and actual Gin-family instantiation remain explicit integration steps. The inverse's displacement-domain width is distinct from the rotation angle.
2. Rebase the same ruling using `d = tc ∘ a - b`. `visibleConnector_rebase_source`, `_height`, `_gradient`, `_B`, `_positive`, and `OrdinaryFamilySourceChart_rebased_endpoint_signs` transport the exact raw scalar, jets and source signs; retain terminal identity from `IncomingTerminalRebase`.
3. `visibleConnectorOrdinaryFamilyRawPotential_global` constructs the actual Cartesian source inverse `E`, scalar and full closed physical carrier. Its output named `B` is the raw scalar, whereas `visibleConnectorFinalSmoothing_exists_full_scalar` uses `B` as the old inverse-height classifier. Keep `Graw` and `heightSign` distinct and use the same `E`.
4. Consume concrete `FinalSmoothingHeight*` producers for classifier smoothness, zero seam, literal old-height pullback and negative normal derivative. `IncomingRebase_cartesian_seam_matches` supplies raw/Gin jets on the displaced height-zero seam, not an open original-incoming germ. Original incoming points have `b < 0`; all their nonpositive ruling portion must stay in `GinU`.
5. Identify the physical closed source annulus with the same raw closed-band image using `WitnessAssemblyTopology_annulus_geometry` and RawPotential's image equality. `FinalSmoothingCarrier_closed_subset` then consumes actual raw-strip containment, nonpositive Gin-strip containment and literal height identity. `visibleConnectorFinalSmoothing_exists_full_scalar` returns ONE final `H` on full fixed `V`, negative Hessian on that full domain/closed band and genuine open incoming/terminal equality germs.
6. Construct the final `H` gradient inverse through `visibleConnectorWitnessAssembly_of_ordinary` and `visibleConnectorGradientInverseApplication_charts`. The original raw inverse must not be substituted for this final gradient inverse. Derive final target nesting from actual negative Hessian and retained traces using the gradient-order consumers.

These are assembly obligations, not a proposal for new conditional wrappers. Producer modules currently being integrated require root's combined source audit.

## Conclusions already supplied downstream

`TorusMarkedGradientOrderPairConnection` calls `exists_markedTorus_pair_of_ordinary_connector_data` in `TorusMarkedOrdinaryConnectorDataConnection.lean`, preserving `d,G0,Gexit,c0,Y`. That route constructs and retains `Gtilde,E,beta,Q,Cdata,D`, including `Q.verticalOffset = dInfinity` and the SAME full meridian `D.meridian`.

`TorusMarkedCompletedPairConnection.lean` / `exists_completedSaddleTorus_marked_pair` constructs a positive nonzero amplitude below its derived stability bound. It invokes:

- `completedSaddleTorus_marked_branch_stability` for actual embeddings, curvature stability and tightness under the explicit positive-Gauss background;
- `affineMarkedTorusLinear_common_smooth_metric` for a `Bundle.ContMDiffRiemannianMetric` (positive definiteness is part of that type), its smoothness and agreement with both actual induced forms;
- `affineMarkedTorusLinear_opposite_native_forms` for exact native induced-form equality;
- `affineMarkedTorus_actualCylinder_bending_imageNoncongruent` for image noncongruence under the named rigidity/reparameterization/ellipse premises;
- `protectedTorus_marked_branch_germs_off_support` and an actual point outside the compact support image for nonempty open agreement;
- `affineMarkedTorus_actualCylinder_bending_hasNoOpenPlanarPatch` for both no-planar-patch conclusions.

Thus metric positivity/smoothness, embedding, noncongruence, agreement and no-planar conclusions need not be postulated anew in the ultimate theorem. They become available by applying the actual caller after all original input obligations above are discharged.

The retained maps are exactly the affine marked base of `F = protectedTorusMap Q.cylinder.saddle D.meridian (dInfinity-d0)` plus/minus the SAME transported bending. `CompletedSaddleTorusVer503Bending.lean` / `completedSaddleTorusBendingField_source_eq_neg` identifies that transported bending with `-Y` on the original chart, implementing the ver503 normalization. The agreement region is exactly the complement of the same chart image of `tsupport Y`.

