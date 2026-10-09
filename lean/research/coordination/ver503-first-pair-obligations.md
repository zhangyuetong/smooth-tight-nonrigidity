# ver503 first-pair obligation audit

Full current-source verification **PASS** at `a733b93d31cf80a2b2a4d3654890029cbe200b69` on `2026-10-09T20:30:18.604546+00:00` (Audit: 162.584 seconds). All FOUR exact closed background proofs, the closed bundle, the premise-free canonical theorem and its full kernel-checked result type are certified. The closure has no admissions or custom axioms.

## Present ultimate theorem and exact assumptions

`TightVer401/NonrigidTorusPair.lean` declares the canonical `exists_noncongruent_isometric_tight_tori_pair` with no premises. The retained `_of_classical` helper takes the positive-Gauss criterion; the canonical proof supplies its exact closed proved inhabitant and preserves the helper's entire existential conclusion.

All four former assumptions have exact closed proofs: `classicalEmbeddedImageReparametrization_proved`, `markerEllipseAxesRecognition_proved`, `classicalCoincidentEmbeddingFixedOpen_proved`, and `classicalPositiveGaussTightness_proved`. The audit checks their exact types, the closed bundle and complete canonical result type using the kernel.

No seed, connector, geometry, completion, ordinary family or desired torus package is a premise. The helper builds the actual universal ordinary family locally and supplies the proved rigidity, reparametrization and ellipse terms. `classicalExternalResults_proved` provides the retained geometric bundle for other conditional consumers.

## Actual seed and exact selected caller projection

`PositiveExitConstructionActualSeedSelected.lean` / `actualSeed_exists_selected_single_prefix` has no premises. It fixes `N = 10000` and `eta = 1`, constructs the corrected seed and original native chart, and retains one final protected field `Y` selected after the margin. Its output supplies positive width, smooth native chart and inverse, the literal support-map identity for the same `d,c0,G0`, band bending, compact support, a nonzero witness, support containment, and `Nonempty (PositiveExitSinglePrefixGeometry d c0 G0 Y)`.

`PositiveExitConstructionSinglePrefix.lean` constructs one scalar `Ge`, its own final gradient chart/inverse, one fixed prefix and final trace pair, four normalized positive fillings, strict source nesting, protected Jordan-annulus placement, actual gradient traces and tangent pairings, visibility, a closed homotopy in the final chart source, and genuine equality with `G0` on an open protected neighborhood. The original source, clocks, field and common perturbation budget are retained together.

`PositiveExitConstructionActualPair.lean` / `actualSeed_exists_markedTorus_pair_of_ordinary_connector_family` obtains that seed existential once, obtains its selected geometry `sg` once, and invokes `TorusMarkedGradientOrderPairConnection.lean` / `exists_markedTorus_pair_of_negative_gradient_order` once. It supplies the actual caller as follows:

| Caller inputs | Actual retained producer |
| --- | --- |
| `hOrdinary` | Universal `visibleConnectorOrdinaryFamily_nonempty_from_incoming`; locally proved in the ultimate theorem. |
| Final scalar, negative Hessian, gradient chart and smooth inverse | `sg.Ge`, `sg.smooth`, `sg.negative`, `sg.e0`, `sg.e0_source`, `sg.e0_actual`, `sg.e0_inverse_smooth`. |
| Four normalized fills and origin enclosures | `sg.sourcePlus`, `sg.sourceMinus`, `sg.gradientPlus`, `sg.gradientMinus`, and their retained origin fields; only the `jordanInterior` notation is unfolded. |
| Strict source nesting | `sg.source_nested` for those same fillings. |
| Closed homotopy and source containment | `sg.H`, `H0`, `H1`, `Hclosed`, `Hdomain`, with the exact final `e0.source`. |
| Actual gradient traces and positive tangent pairings | `sg.actualPlus`, `actualMinus`, `pairPlus`, `pairMinus`, with the same final scalar and clocks. |
| Visibility and positive radii | `sg.visiblePlus`, `visibleMinus`, using the retained numerical radii `1/4` and `4/5`. |
| Protected core | `sg.protected_core` for the same `c0 '' tsupport Y`; only the annular/Jordan set notation is unfolded. |
| Native band and protected bending | The actual seed existential's `hw`, `hc0`, `hci0`, `hBand`, `hY`, `hcompact`, `hnonzero`, `hKsource`. |
| Open protected equality | `sg.O`, `Oopen`, `protected_O`, `old_eq`. |

This is an actual same-object application, not an assumed geometry package. The resulting pair and completion are packaged directly into the original-data existential; no second completion, full meridian or marked pair is chosen.

## Universal D-only ordinary-family construction

The frozen `61ee647c815f4f6d3cf5b9a0abd53bc479c3fd2b` source supplies `VisibleConnectorOrdinaryFamilyFromIncomingAssembly.lean` / `visibleConnectorOrdinaryFamily_nonempty_from_incoming`. For arbitrary `Gin`, `Uin`, positive `L`, `R` and `etaMax`, its inputs are only `D : VisibleConnectorIncomingData Gin Uin L R` and `hetaMax : 0 < etaMax`, with the usual positive-`L` instance. Its result is `Nonempty (VisibleConnectorWitnessAssemblyOrdinaryData D etaMax)`. There is no extra original-construction grant or external classical parameter in this producer.

The concrete dependency chain retains the same objects:

1. The incoming choice chooses one eta below `etaMax`, the literal Gin family, one native inverse `e`, and one rho after intersecting all actual sign, visibility and terminal thresholds. Actual terminal radial/directional/excess facts are proved at that same rho.
2. `VisibleConnectorOrdinaryFamilyFromIncomingRaw` rebases the retained ruling with `d = tc ∘ a - b`, constructs its actual Cartesian source inverse `E`, raw scalar and physical carrier, and retains the incoming Gin identities and seam jets. The raw/source inverse is not the final smoothed gradient inverse.
3. `VisibleConnectorOrdinaryFamilyFromIncomingScalar` applies concrete full smoothing to those same raw data and Gin branch. The final height is literally `visibleConnectorFinalSmoothingHeight L b d E`; the final carrier is built from that height and the same raw/incoming domains. It returns the final scalar with strict negative Hessian on its open domain and full closed physical band, plus genuine open incoming and terminal equality germs.
4. `FromIncomingAssembly` invokes the retained scalar family once at positive error budget `1`, keeping one final `H`. `ActualChoiceTerminal`, `ActualChoiceTurn`, `RebasedGradientCircle`, `TerminalJets`, `SourceClosure` and `GradientEnclosure` supply the terminal facts, increasing full-turn angle, actual circle and origin enclosures, source closure and nesting, and reversed gradient nesting for that final scalar. The retained source map has the actual boundary traces and positive annular Jacobian.
5. The downstream witness/gradient-inverse application constructs the own final `H` gradient inverse. It does not reuse `E` as a gradient inverse. Thus the ordinary-family consumer receives the same final scalar, its own gradient chart, its genuine incoming germ and its full physical closed-band Hessian statement.

The universal family obligation is now discharged in source for every `D` and positive `etaMax`; it is no longer an unfinished conditional assembly requirement. The universal producer is included in the current root PASS certificate.

## Literal ultimate conclusions and completed tuple

The ultimate theorem explicitly returns `Xplus`, `Xminus` and one `Bundle.ContMDiffRiemannianMetric planeModel ∞ Plane` on their common source. Positive definiteness and smoothness are fields of that metric structure. For every tangent pair it asserts that this same metric equals both actual `inducedForm` bilinear forms; it also asserts equality of the actual `nativeProductInducedForm` forms.

Both maps satisfy `NativeTorusSmoothEmbedding`, `IsTightImage` and infinity smoothness. The result includes `ImageNoncongruent`, one nonempty open set `V` with `EqOn Xplus Xminus V`, and `HasNoOpenPlanarPatch` for both maps. These are conclusions, not new assumptions.

The result retains `A,RN,mu,B,d0,dInfinity,epsilon,L,Gtilde,W,E,beta,Q,Cdata,D,a`, including the scalar inequalities, open protected neighborhood, exact source/target of `E`, protected scalar equality and germs, literal completed cylinder identity, `Q.verticalOffset = dInfinity`, and the matching `Cdata` tuple identities. The maps are exactly the affine marked base of

`F = protectedTorusMap Q.cylinder.saddle D.meridian (dInfinity - d0)`

plus/minus the same positive amplitude times the affine marked bending of

`Z = protectedTorusBendingField (completedSaddleTorusBandChart Q) (completedSaddleTorusBandAffine Q) Y`.

The full meridian is the same `D.meridian` returned by the completion caller. The agreement set is exactly the complement of the same chart image of `tsupport Y`. `CompletedSaddleTorusVer503Bending.lean` / `completedSaddleTorusBendingField_source_eq_neg` supplies the ver503 normalization `Z = -Y` on the original chart.

Downstream, `TorusMarkedCompletedPairConnection.lean` / `exists_completedSaddleTorus_marked_pair` supplies these conclusions through `completedSaddleTorus_marked_branch_stability`, `affineMarkedTorusLinear_common_smooth_metric`, `affineMarkedTorusLinear_opposite_native_forms`, `affineMarkedTorus_actualCylinder_bending_imageNoncongruent`, `protectedTorus_marked_branch_germs_off_support`, and `affineMarkedTorus_actualCylinder_bending_hasNoOpenPlanarPatch`, using the proved positive-Gauss statement and the other three proved background terms.

## Certification boundary and deferred scope

The universal D-only producer, actual seed/selected construction, same-object pair projection and premise-free canonical theorem are in the current certified closure. All four background proofs and the closed bundle are checked, with no admissions or custom axioms. The kernel verifies equality of the complete canonical result type to the supplied retained helper result. Historical certificates remain provenance for their earlier source snapshots.

The objective remains the global nonrigid-torus first pair. Extension applications and Cantor families are deferred.
