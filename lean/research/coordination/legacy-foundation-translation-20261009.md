# Legacy foundation translation review

Date: 2026-10-09. Read-only comparison of the selected ver28 and ver104 arguments with the current pinned OpenAI geometry. This file is the sole write; no Lean, vendor source, build, cache, audit, root import, or certificate was changed.

Current engine: C:/Users/gzhan/.codex/worktrees/ver500-tori/tight/formalization/ver401.
Legacy roots: C:/Users/gzhan/Desktop/tight/formalization/ver28 and C:/Users/gzhan/Desktop/tight/formalization/ver104.
Pinned OpenAI repository: https://github.com/openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, geometry tree 802c5efb3142a299fb780105e14b7a9f268c4d32 (current upstream-lock.json). This review read the local pinned sources; parent and sibling own online discovery. This report is not a fresh compilation or new certification.

## Verdict

The selected source arguments are compatible after actual derivative/metric/curvature conversions. They are not compatible by changing imports or renaming the old geometric predicates. Ambient Euclidean three-space already agrees; the coordinate and torus models do not agree nominally. Old extrinsic determinant curvature must be identified with the current intrinsic curvature by the existing OpenAI Gauss equation.

The essential affine-marker rule is: surface BX, bending B inverse-transpose Y. The marked pair is BX ± t B inverse-transpose Y, rather than B(X ± tY). General invertible marking preserves curvature signs, not curvature values, and produces a new common metric rather than preserving the old branch metric.

No flaw was found that makes the current two classical contracts stronger than their stated background corollaries. Their actual application hypotheses must remain visible. Neither supplies the protected patch, marker boundary geometry, stabilizer, curvature transport, or torus construction.

## 1. Exact basic-object comparison

| Object | ver28 / ver104 | Current OpenAI/native engine | Required conversion |
| --- | --- | --- | --- |
| Ambient | SphereSupport.R3 = EuclideanSpace ℝ (Fin 3) | OAI.SmoothLocal.Geometry.Ambient = EuclideanSpace ℝ (Fin 3) | Same mathematical Euclidean space and inner product; retain current instance declarations. No rescaling or metric substitution. |
| Local coordinates | R2 = ℝ × ℝ, d i F p = fderiv F p (coord i) | Coord = Fin 2 → ℝ, coordPartial i F p = fderiv F p (Pi.single i 1) | Explicit linear coordinate equivalence, actual chain rule, both coordinate-basis images. |
| Source torus | Circle × Circle; tangent model EuclideanSpace(Fin 1) × EuclideanSpace(Fin 1) | NonrigidTorusSource = AddCircle(2π) × AddCircle(2π); nativeProductModel = real-product model | Adapt the generic argument to the current source. Do not transport an old constructed torus or assert old chart/tangent instances are definitionally equal. |
| Manifold differential | mfderiv and vector-valued mvfderiv, actual Mathlib derivative | Native mfderiv and OAI.ClosedSurfaceR4.surfaceDifferential | Use proved nativeProductPlane_mfderiv identities. |
| Induced form | inducedMetric I X p v w = inner(dX v,dX w) | nativeProductInducedForm X p v w = inner(native mfderiv X v,native mfderiv X w) | Same pullback construction after the explicit tangent map, not a chordal-distance equality. |
| Local metric | SphereSupport.Metric F Gram matrix | OAI inducedMetric F Gram matrix | Pull back F through actual coordinate equivalence; establish both derivatives, then all coefficients. |
| K | det(Metric inverse * SecondForm), with actual unit normal; ver28 chartNormal from normalized cross product | gaussianCurvature(actual inducedMetric), defined via actual Christoffel/Riemann coefficients | Use OAI Gauss equation and det(metric)>0 on actual smooth immersion neighborhood. |
| Ambient congruence | R3 ≃ᵢ R3, then Mazur–Ulam affine decomposition | Ambient ≃ᵃⁱ[ℝ] Ambient directly | Current affine linear part and translation already supplied. No new Mazur–Ulam theorem needed for current target. |
| Affine marker | invertible B = rows (1,0,1),(0,2,1),(0,0,1) | Actual Ambient continuous linear equivalence to define | B is NOT an affine isometry. Keep separate from the congruence A API. |

Exact definitions checked:
- ver28/TightTori/Geometry/SphereSupport.lean: R2, R3, coord, d, Metric.
- ver28/TightTori/Geometry/Bending.lean: inducedMetric, InfinitesimalBending, affinePerturbation.
- ver28/TightTori/Geometry/SurfaceGeometry.lean: SecondForm, Shape, GaussCurvature; manuscript convention dX*S = -dn.
- ver28/TightTori/Geometry/SurfaceGerm.lean: chartNormal, chartCurvature.
- ver104/IdentityHolonomy/Geometry/SphereSupport.lean and SurfaceGeometry.lean use the same basic actual Gram/second-form construction.
- Current vendor/openai-math/lean/OAI/Geometry/IsometricImmersion/Metric.lean: Ambient, SmoothPositiveOn, IsometricOn, induced-geometry definitions, gaussianCurvature, secondFundamental.
- Current vendor/openai-math/lean/OAI/Geometry/IsometricImmersion/Calculus/CoordinateDerivatives.lean: Coord, coordPartial.
- Current ClassicalExternal.lean: nativeTorusChartCurvature is actual OAI intrinsic K at the preferred native chart center; nativeTorusPositiveRegion uses precisely this K.

## 2. Existing active conversions: reuse these actual exports

All names in this section are TightVer401 exports unless qualified otherwise.

NativeProductPlaneAtlas.lean imports the pinned OAI.Analysis.CircleDomains.Topology.EuclideanPlaneCoordinates:
- nativeProductPlaneEquiv = OAI.CircleDomainRigidity.euclideanPlaneCoordinates.symm.
- nativeProductPlaneEquiv_symm_apply, nativeProductPlaneEquiv_apply_zero/one.
- nativeProductPlaneEquiv_inner identifies Euclidean pairing with the sum of coordinate products.
- nativeProductPlaneChartedSpace constructs the opt-in transported atlas.
- nativeProductPlane_contMDiff_iff and smooth identity/inverse maps.

Important: the product norm on ℝ×ℝ is the max norm; nativeProductPlaneEquiv is a continuous linear equivalence, not an isometry of that product norm. Manifold smoothness and tangent inner products are transported explicitly. Do not infer norm equality or intrinsic-distance compatibility from the coordinate equivalence.

NativeProductPlaneForms.lean:
- nativeProductPlane_mfderiv and nativeProductPlane_mfderiv_apply.
- nativeProductPlane_immersion_iff.
- nativeProductPlane_inducedForm and nativeProductPlane_linearMetricForm.
- nativeProductPlane_zero_strain_iff.

NativeProductPlaneCurvature.lean:
- nativeProductPlane_coordinateMap_eq: native and transported preferred-chart maps are literally the same physical representative.
- nativeProductPlane_coordinate_fderiv: chart derivative equals actual native mfderiv composed with finTwoArrow.
- nativeProductPlane_coordinate_inducedForm, nativeProductPlane_coordinate_metric.
- nativeProductPlane_coordinate_curvature.
- nativeProductPlane_curvature_of_chart_germ, nativeProductPlane_support_curvature, nativeProductPlane_ruled_curvature.

These compare the TWO ATLASES ON THE SAME SOURCE. They do not prove curvature invariance under an arbitrary source diffeomorphism. A port of TorusEmbeddedReparam must derive that additional coordinate-change identity.

NativeProductPlaneMetricBundle.lean:
- nativeProductImmersionMetric, nativeProductImmersionMetric_inner.
- nativeProductPlaneImmersionMetric and nativeProductPlaneImmersionMetric_transport.
Actual derivative injectivity proves positive definiteness and bounded induced unit ball; actual smooth derivative proves bundle smoothness. This avoids assuming a fabricated Riemannian metric.

SurfaceMetric.lean:
- inducedMetric_bilinear, inducedMetric_posDef, inducedMetric_isometricOn, inducedMetric_smoothPositiveOn.

GaussBridge.lean, using the pinned GaussEquation/IntrinsicCurvature:
- curvature_eq_second_form_det_div_metric_det.
- negative_curvature_iff_second_form_det_neg.
Pinned OAI.SmoothLocal.Geometry.det_secondFundamental_eq_gaussianCurvature_mul_det is the actual underlying theorem.

CurvatureLocality.lean:
- inducedMetric_eventuallyEq, curvature_unchanged_off_support.
Pinned OAI gaussianCurvature_eq_of_eventuallyEq transfers actual metric germs, including the derivatives used by K. Pointwise agreement cannot replace germ agreement.

TorusSourceGeometry.lean:
- nonrigidTorusSource_compact, nonrigidTorusSource_connected, nonrigidTorusSource_isManifold.
No new old-circle model is needed.

## 3. Port ver28 noncongruence at the argument level

Selected files:
- TightTori/Geometry/TorusNoncongruence.lean: images_noncongruent_of_protected_positive_patch.
- TightTori/Geometry/ReparamRigidity.lean: eq_of_reparam_of_rigidity.
- Supporting TorusEmbeddedReparam.lean, SurfaceCurvatureReparam.lean, TorusRigidMotion.lean.

Current same-object route:
1. Use actual smooth embedded native X,Y and exact common nativeProductInducedForm.
2. An alleged affine isometry A satisfies A '' range X = range Y.
3. Derive actual positive-curvature image transport:
   A '' (X '' nativeTorusPositiveRegion X) = Y '' nativeTorusPositiveRegion Y.
4. Exact positive loci are the same nonempty open O, and X=Y on O. Thus A preserves the actual unchanged positive image.
5. Construction-specific trivial stabilizer forces A=id.
6. Equal images, equal actual induced forms, and open agreement feed classicalCoincidentEmbeddings_eq.
7. Actual nonzero bending at t≠0 contradicts equality of the opposite parametrized branches.

Step 3 is not supplied by either current classical contract. Needed small actual adapters:
- In a preferred native chart, use actual affine decomposition A(z)=A.linearIsometryEquiv(z)+A(0).
- Derive the composition differential via actual chain rule; existing ProtectedTorusBendingStrain.protectedTorus_affine_pullback_zero_strain already demonstrates the current A.map_vadd/linearIsometryEquiv API and nominal tangent handling.
- Derive local Gram metric equality under A. Equality as metric FIELDS yields OAI K equality, including all derivatives, on the unchanged source.
- For equal embedded images with different parametrizations, derive a genuine local smooth inverse/reparameterization or apply an appropriately stated ordinary embedded-submanifold theorem. Then identify actual regular chart change and K under it; use GaussBridge to avoid rebuilding Christoffel-coordinate invariance if convenient.
- Legacy SurfaceCurvatureReparam derives actual regular chart changes from a genuine diffeomorphism. Retain that source logic; do not assume equality of independently chosen preferred chart maps.

Current ClassicalCoincidentEmbeddingFixedOpenClaim already packages the generic same-image smooth-reparameterization plus fixed-open isometry conclusion. It makes recreating ver28 InducedMetricRigidity and induced-distance instances unnecessary on the blocking route. Ver28's source remains a checked explanation of the corollary, not a requirement to port every old atlas.

No old curvature scalar or arbitrary legacy CurvatureField may silently be identified with nativeTorusChartCurvature. For any old local proof reused, establish actual coordinate Gram and second-form equality and then invoke the OAI Gauss equation under smoothness and immersion.

## 4. Principal marker and inverse-transpose rule

Source: ver104/IdentityHolonomy/Marking.lean.

B(x,y,z)=(x+z,2y+z,z).
B inverse-transpose(x,y,z)=(x,y/2,z−x−y/2).
Exports: mark, unmark, contra, dual_pairing, strain_transport, contra_support, contra_closed_support.

The exact identity is inner(Bv,B inverse-transpose w)=inner(v,w). Deriving the second cross term uses symmetry of the real inner product. It is not inner(Bv,Bw)=inner(v,w).

On the current native source define:
- Xmarked(p)=B(X(p)).
- Ymarked(p)=B inverse-transpose(Y(p)).
Actual mfderiv composition gives dXmarked=B*dX and dYmarked=B inverse-transpose*dY. Hence actual nativeProductLinearMetricForm vanishes if the original does.

Then reuse:
- NativeProductPlaneFormsApplications.nativeProductIsBending.
- nativeProduct_bending_common_metric.
- nativeProduct_exact_sign_pair (or the common quadratic identity with ±t).
- NativeProductPlaneMetricBundleApplications.nativeProduct_bending_branch_immersion.
- nativeProductPlane_bending_scaled_common_smooth_metric.

The common marked branch metric is g_BX+t²g_B inverse-transpose Y. It need not equal the original pair's common metric. Every amplitude remains immersed from actual zero strain and baseline immersion; actual compact embedding still requires a small amplitude threshold.

Support and nonzero transfer:
B inverse-transpose is invertible and sends zero to zero; ordinary support and closed support are EXACTLY unchanged on the source, without a continuity premise. Nonzero field transfers by injectivity. The field remains zero on the actual protected open patch.

Normal and curvature:
- Unit normal of B*X is B inverse-transpose(n)/norm(B inverse-transpose(n)), up to the harmless global orientation sign.
- For actual immersed charts, K_BX = K_X / (det(B)^2 * norm(B inverse-transpose(n))^4).
- The factor is strictly positive; positive/zero/negative loci are unchanged on the source.
- For rigid A only, the factor is one and K values agree.
- The normal-direction map n↦B inverse-transpose(n)/norm(...) is a smooth sphere diffeomorphism, so a genuine positive Gauss diffeomorphism remains one after marking; the finite exceptional set becomes its actual image.
- Tightness is also preserved directly by invertible affine maps through halfspace pullback ell↦ell∘B. No equality of K values or total absolute curvature is needed for this direct transfer.

These are mathematical conversion obligations, not claimed new compiled exports. ver104 AffineCurvatureSigns.ClassicalAffineCurvatureFactor states the weaker positive-factor corollary as an explicit parameter. Current pinned GaussBridge makes a direct determinant proof feasible; any added grant must state the ordinary local affine-curvature formula, not a marked-torus conclusion.

## 5. EllipseMarker and MarkerApplication: exact scope survives translation

Files: ver104/IdentityHolonomy/Geometry/EllipseMarker.lean and MarkerApplication.lean.

EllipseAxesPrinciple is a valid narrowly classical single-ellipse input: an actual affine Euclidean isometry taking a noncircular axis-aligned ellipse with semiaxes a<e to a translated ellipse with the SAME semiaxes takes center to center and preserves each principal-axis line. It grants no pair stabilizer or annulus.

Actual proof exports:
- marked_circle maps the circle of radius R at height h to ellipse centered at (h,h,h), semiaxes R and 2R.
- pair_stabilizer: preservation/permutation of the two marked ellipses at ±h implies identity OR central inversion.
- marked_annulus_stabilizer excludes central inversion from an actual positive non-even radial meridian.
- MarkerApplication.lateral_closure, lateral_boundary_circles, marked_boundary, boundary_preserved, actual_boundary_permutation, marked_open_annulus_rigid derive the boundary permutation from the actual lateral annulus closure and connectedness.

Required current consumer data:
- Actual current positive-image equality to the full marked lateral revolution set, not merely a subset or parametrized patch.
- Its actual closure-minus-open-image is exactly two terminal circles, and marking sends these to the advertised two ellipses.
- Positive meridian and an actual witness r(z)≠r(−z), with |z|<h.
- The full two-boundary-ellipse statement applies to the current actual patch.

Radius mismatch warning: the old public pair theorem uses one common R at both ±h. Current ParabolicConvexClosure admits RN and RS. If they are unequal, derive that an isometry cannot swap ellipses of different axis sizes, then use single-ellipse rigidity; do not feed the old same-R theorem by renaming either radius. If the constructed actual witness has RN=RS, prove that equality explicitly.

The old circular collar versus current parabolic collar mismatch does not prevent reusing ellipse algebra: both endpoints can still be literal circles. It does prevent reusing a full old attachment or collar-germ theorem. Derive terminal circle and lateral closure facts from the current completed native maps.

## 6. SingleBendingPair: extract assembly, avoid opaque packages

File: ver104/IdentityHolonomy/Geometry/SingleBendingPair.lean.
Imports FamilySurfaceGeometry and ActualProtectedMarker.

Useful argument-level exports:
- value_zero, immersion, metric_pair, unchanged.
- arbitrarily_small combines continuous affine dependence, actual compact negativity, and embedding openness.
- noncongruent combines actual positive-image invariance, protected marker, actual metric equality and fixed-open image rigidity.

Current replacements:
- nativeProduct_bending_branch_immersion gives actual native immersion for all amplitudes.
- nativeProduct_bending_common_metric gives actual exact metric equality.
- nativeCompactEmbedding_exists_amplitude_threshold gives compact embedding stability without a granted smooth-function-space topology.
- CurvatureLocality gives actual off-support K invariance.
- Current actual compact curvature/parameter bounds should replace ClassicalSmoothCurvature on the first-pair route.

Abstraction caution:
- ver104 ClassicalSmoothCurvature.value is an abstract Map→Torus→ℝ. Its field condition identifies it with actual extrinsic CurvatureField only after an actual embedded immersion and such a field are supplied.
- FamilySurfaceGeometry.Data contains actual curvature field and area-characterization conditions, so its noncongruence proof does not simply use an arbitrary scalar. Nevertheless the CURRENT native K identification remains necessary; copying the data structure is not that identification.
- arbitrarily_small by itself is an abstract compact-negativity statement about curv.value. Do not count it as actual OpenAI K stability before the field/Gauss-equation adapter.
- ClassicalRigidCurvature is a generic Euclidean-congruence invariance of actual surface curvature fields, not a permission to assert preservation of a construction-specific positive image.
- ActualProtectedMarker.protected_marker depends on the actual NorthernData/MarkedTorusBudget and actual support-core disjointness; that assembly cannot be imported as an already constructed current protected patch.

## 7. Current classical boundary: consistency checks

Current ClassicalExternal.lean and classical-external-results.json explicitly retain only two named assumed corollaries.

ClassicalCoincidentEmbeddingFixedOpenClaim:
actual C∞ embeddings and native differential injectivity, actual induced form equality, equal entire images, nonempty open agreement imply X=Y. Connectedness is fixed by the genuine current torus. This is ordinary smooth embedded-submanifold inversion plus connected induced-Riemannian isometry uniqueness. It supplies no ambient stabilizer or noncongruence. Current nativeProductImmersionMetric already supplies the actual positive smooth metric if one elects to unfold that proof.

ClassicalPositiveGaussTightnessClaim:
actual smooth embedded immersion, actual global round-sphere unit normal orthogonal to the actual mfderiv, and actual smooth Gauss restriction with exact source {actual OAI K>0} and exact target sphere minus a finite set imply IsTightImage. The normal must be the same actual map on the entire positive source. The claim is the positive-Gauss-area/equality corollary; no arbitrary prescribed K or positive-region package is accepted. If one unfolds the area argument, OAI GaussBridge provides the required intrinsic/extrinsic identification. Do not replace the exact source equality by inclusion or a single selected positive sheet.

No current granted contract assumes a marker, saddle annulus, dual completion, or final pair. Both are explicit theorem parameters, not supplied inhabitants. The final construction remains conditional on the declared background and must derive every application hypothesis.

## Practical conclusion

Port the elementary algebra, set/image logic, and source proof arguments into current definitions. Reuse active native/OAI derivative and metric transport, Gauss equation, curvature locality, compact embedding stability, and the two authorized ordinary classical corollaries. The remaining substantive adapters are actual curvature reparameterization/congruence transport, actual marker inverse-transpose native strain, affine curvature-sign/normal transfer, and the current terminal-boundary/positive-image identification. No raw legacy namespace, axiom, object file, certificate, old torus instance, or abstract curvature package belongs in the current closure.
