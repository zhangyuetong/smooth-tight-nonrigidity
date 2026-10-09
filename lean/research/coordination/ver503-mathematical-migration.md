# ver503 mathematical migration review

Review date: 2026-10-09. This is a read-only source/type review, not a proof certificate. The reviewed publication checkout is `C:/Users/gzhan/Documents/ChatGPT/tight_another_review/smooth-tight-nonrigidity-publication`; the new integration checkout is `C:/Users/gzhan/Documents/ChatGPT/tight_another_review/ver503-integration`. Namespace remains `TightVer401`.

## Target and comparison

Current manuscript: `paper/paper.tex`, exact SHA256 `a809ad8ef4810fcdf61fd2511cb389b1ba4816478f309b42c729a69ed586bf9a`. Historical target metadata: `lean/target/ver500-coverage-historical.json`, ver500 SHA256 `0af363cb3372b6f24c0492efc378f41139731c8ab0e6cb2844dd9ecebf0ce304`.

After normalizing line endings solely for the textual comparison, four numbered statement bodies differ: `prop:support`, `lem:holonomy-integral-new`, `thm:protected-realization`, and `thm:localized-sign`. Other numbered statement bodies match. This does not certify unchanged dependencies: conventions and construction prose also change. Exact target pinning and audits must use source bytes, without newline normalization.

## Claim-specific reuse

### prop:support: compatible bilinear and endomorphism conventions

`SphereSupportTensor.lean` defines `sphereSupportTensor g H = covHessian g H + H*g`, the covariant bilinear coefficients. `SphereSupportCurvature.lean` defines `sphereSupportEndomorphism g H = g.inverse * sphereSupportTensor g H`, raising one index. `SphereSupportForms.lean` proves `sphereSupportMap_inducedMetric = tensor * g.inverse * tensor.transpose` and `sphereSupportMap_secondFundamental = -tensor`. `sphereSupportMap_curvature` gives reciprocal determinant of the endomorphism. These are precisely the ver503 bilinear metric, second-form sign, and determinant convention. Existing differential, immersion, normal, converse and global chart exports remain relevant.

Reuse justification: the old Lean types already distinguish the two tensors; ver503 clarifies their relationship rather than changing the mathematics. Do not replace the coordinate metric formula with an ordinary raw matrix square. Award reuse only after the current-source audit.

### thm:protected-realization: fixed normalized field and zero extension

`protectedTorusBendingField` in `ProtectedTorusBendingExtension.lean` uses one `OpenPartialHomeomorph e`, applies `A.linearIsometryEquiv` to `Y(e.symm q)` on `e.target`, and is zero outside. Its source formula, smooth compact-support extension, support bound, and nonzero result are proved. `protectedTorus_compact_nonzero_bending` additionally consumes literal same-object placement `F(e p) = A(X p)`.

The completed-saddle normalization is ALREADY present: `completedSaddleTorusBandChart Q` composes the retained band coordinates with the quotient phase chart; `completedSaddleTorusBandChart_placement` proves the map equals `-d.bandMap p + Q.verticalOffset * revolutionAxis` on that same source. `completedSaddleTorusBandAffine Q` is `AffineIsometryEquiv.constVSub` at that same offset, and `completedSaddleTorusBandAffine_apply` proves the identical formula. `completedSaddleTorusBending_placement` retains this affine map for any assembly with `D.toProtectedSaddleCylinderInput = Q.cylinder`. `exists_completedSaddleTorus_compact_nonzero_bending` passes it to the checked zero-extension theorem and retains the SAME saddle and newly chosen meridian.

Consequently, normalization does not require recreating placement or bending transport. There is no discovered named export spelling the linear action as `-Y`; a minimal optional literal adapter is described below. An actual inhabitant of `CompletedSaddleAnnulusGeometryOutput` remains an original construction obligation. The full injective linear profile family, all protected-realization conclusions, and numerical total-absolute-curvature claim must not be awarded merely from the one-field conditional consumer.

### thm:localized-sign: explicit stabilizer, partial reuse only

Ver503 explicitly requires a tight embedding of a closed connected surface and a trivial ambient stabilizer of its positive-curvature image. `torusImageNoncongruent_of_positive_marker_and_open_agreement` in `TorusMarkedImageNoncongruenceConnection.lean` already consumes the exact entire common positive image `P` and `hmarker : forall A, A '' P = P -> forall x, A x = x`, actual smooth embeddings, the same actual induced forms, a nonempty open agreement and map inequality. Its positive-image transport uses the explicit registered `ClassicalEmbeddedImageReparametrizationClaim`; fixed-open rigidity uses `ClassicalExternalResults`.

The existing `Manifold.infinite_sign_metric` and `signedSeries_coefficients_injective` remain partial coverage only. They do not establish image noncongruence, small smooth series construction, tight embeddings or orbit-space topology. Keep countable/Cantor work deferred.

### lem:holonomy-integral-new: terminology only, still pending

Only the title changes from Intrinsic to Asymptotic return multiplier. The oriented arclength, perpendicular tangent, `sigma = sign II(T,Z)`, and logarithmic multiplier identity are unchanged. The full geometric Han--Khuri identity remains pending. `projectiveReturn_multiplier_one` in `ReturnMap.lean` shows that derivative one does not imply full identity; `exists_scalarFlowPeriod_return_family` in `ScalarFlowPeriodReturn.lean` gives the multiplier of an actual constructed scalar solution family. Neither supplies the general geometric integral identification. Keep those scopes distinct.

## Additional dependency and construction review

- `V` relatively compact in `U` now means compact closure contained in `U`. Existing explicit compact-support inputs suffice where used; do not silently equate them with every relatively compact open set.
- A collar may be one-sided at a genuine boundary, but retaining a germ still means agreement on an open overlap in the relevant domain.
- Differential Legendre duality now explicitly requires a global gradient inverse on the chosen gradient image, with the chosen additive constant recovered. Negative determinant alone gives only local inversion. Preserve native inverse `e` versus Cartesian inverse `E` and the actual chosen potential through each consumer.
- Completion prose separates degree applications for connector source `P`, joined support gradient, and dual-filling gradient. The reflected inner construction uses the original outer gradient boundary as its new source boundary; reflection and reversed parametrization reverse orientation twice. Domain sides and retained boundary collars must be proved for their actual objects.
- Quadratic smoothing preserves negative determinant and tangential positivity; it need not preserve radial concavity on the incoming side. Do not add the stronger claim to a consumer.
- `exists_relative_saddle_smoothing_on_sides` already produces one scalar `H` on the full fixed open domain `V`, negative Hessian everywhere on `V`, and eventual equality to both branch germs outside the seam neighborhood `N`. Its hypotheses include both seam-domain containments, full side-domain containments, actual smoothness and Hessian negativity on each domain, side geometry, and matching values/gradients. Worker obligations are to construct these inputs and place boundary germs outside `N`; matching first jets alone is insufficient. A required closed band contained in `V` inherits the output Hessian condition. The original inverse is not automatically the inverse gradient of final `H`.
- The affine convention agrees with `affineMarkedTorusLinear_secondFundamental` in `AffineMarkedTorusLinearCurvature.lean`: multiplication by the positive inverse norm of the inverse-transpose normal. Curvature signs survive; metrics and curvature values generally change. Retain the marked common metric constructed from marked branches.
- Convex closure clarifies integrable infinite endpoint slopes in the height coordinate and smoothness in the collar parameter. Smoothness across auxiliary disk rims is unnecessary. Reuse the one full meridian witness through closure, Gauss, marking and pair consumers.

## Minimal normalization adapter proposal (not implemented or compiled)

Place beside the completed-saddle bending consumer, or in a separate small module if assigned by the coordinator:

1. `completedSaddleTorusBandAffine_linear_apply (Q) (x : Ambient) : (completedSaddleTorusBandAffine Q).linearIsometryEquiv x = -x`.
2. `completedSaddleTorusBendingField_source_eq_neg (Q) (Y) {p} (hp : p in (completedSaddleTorusBandChart Q).source) : protectedTorusBendingField (completedSaddleTorusBandChart Q) (completedSaddleTorusBandAffine Q) Y (completedSaddleTorusBandChart Q p) = -Y p`.
3. Optionally the target formula with `Y((completedSaddleTorusBandChart Q).symm q)` for `q` in target; outside-target zero is already exported.

The second statement follows from `protectedTorusBendingField_source` and the first. The first is the linear part of `constVSub`, provable by its linear definition or by affine displacement at zero plus `completedSaddleTorusBandAffine_apply`. No new geometric assumptions, new witnesses or reconstruction are necessary. Exact final consumer: `exists_completedSaddleTorus_compact_nonzero_bending`, then marked pair stability/completion; same-object input: the SAME `Q`, chart and `Y` already retained there. The vertical offset is the actual normalization chosen by the completed output; identify it with the completed scalar tuple through existing output data rather than choosing another translation.

## Coverage adaptation

Regenerate statement text, titles, source lines and labels from exact ver503 target bytes. Update `target-lock.json`, `coverage.json`, blueprint and audit metadata consistently. Replace stale blanket 'exact numbered statement unchanged' notes for the four changed claims with the precise reviews above. For the other claims record unchanged statement text plus any changed dependencies. Preserve the ver500 certificate as historical evidence, never a migrated certificate. Pending protected realization, first-pair construction and deferred Cantor claims remain pending. Full current-worktree verification is required after source integrations before granting credit.
