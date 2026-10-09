import TightVer401.ClassicalExternal
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Add

/-! Exact intrinsic curvature under an ambient affine Euclidean isometry.
The actual derivative is its linear isometry composed with the original
derivative. Consequently the entire induced metric field is equal, including
all derivatives used by the pinned intrinsic Gaussian curvature formula.
This uses no source reparametrization or classical curvature grant. -/
open Manifold
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

/-- Pinned derivative identities for an invertible linear isometry and a
constant translation hold even at points where the default derivative is zero. -/
theorem torusRigid_coord_fderiv
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient) (X : Coord → Ambient) (p : Coord) :
    fderiv ℝ (A ∘ X) p =
      (A.linearIsometryEquiv.toLinearIsometry.toContinuousLinearMap).comp
        (fderiv ℝ X p) := by
  have hfun : A ∘ X = fun q => A.linearIsometryEquiv (X q) + A 0 := by
    funext q
    simpa only [Function.comp_apply, vadd_eq_add, add_zero] using
      A.map_vadd (0 : Ambient) (X q)
  rw [hfun, fderiv_add_const]
  exact A.linearIsometryEquiv.comp_fderiv

/-- Ambient affine isometries preserve the actual full induced metric field.
No immersion, curvature relation or compatible metric is assumed. -/
theorem torusRigid_coord_inducedMetric
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient) (X : Coord → Ambient) :
    inducedMetric (A ∘ X) = inducedMetric X := by
  funext p
  ext i j
  change inner ℝ (fderiv ℝ (A ∘ X) p (Pi.single i 1))
      (fderiv ℝ (A ∘ X) p (Pi.single j 1)) =
    inner ℝ (fderiv ℝ X p (Pi.single i 1))
      (fderiv ℝ X p (Pi.single j 1))
  rw [torusRigid_coord_fderiv]
  exact A.linearIsometryEquiv.inner_map_map _ _

/-- The SAME native preferred-chart intrinsic curvature is unchanged by
an ambient affine isometry. The metric equality above is global in the chart,
so the higher metric derivatives defining curvature agree as well. -/
theorem nativeTorusChartCurvature_affineIsometry
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient) (F : NonrigidTorusSource → Ambient)
    (p : NonrigidTorusSource) :
    nativeTorusChartCurvature (A ∘ F) p = nativeTorusChartCurvature F p := by
  unfold nativeTorusChartCurvature
  change gaussianCurvature (inducedMetric (A ∘ nativeProductCoordinateMap F p))
      ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm (chartAt (ModelProd ℝ ℝ) p p)) =
    gaussianCurvature (inducedMetric (nativeProductCoordinateMap F p))
      ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm (chartAt (ModelProd ℝ ℝ) p p))
  rw [torusRigid_coord_inducedMetric]

/-- The entire actual positive source region is invariant under ambient
affine ISOMETRIES. This does not apply to a general invertible linear marking. -/
theorem nativeTorusPositiveRegion_affineIsometry
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient) (F : NonrigidTorusSource → Ambient) :
    nativeTorusPositiveRegion (A ∘ F) = nativeTorusPositiveRegion F := by
  ext p
  change (0 < nativeTorusChartCurvature (A ∘ F) p) ↔
    (0 < nativeTorusChartCurvature F p)
  rw [nativeTorusChartCurvature_affineIsometry]

/-- The positive image of the literal composed map is precisely the
ambient isometry image of the original entire positive image. -/
theorem nativeTorusPositiveImage_affineIsometry
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient) (F : NonrigidTorusSource → Ambient) :
    (A ∘ F) '' nativeTorusPositiveRegion (A ∘ F) =
      A '' (F '' nativeTorusPositiveRegion F) := by
  rw [nativeTorusPositiveRegion_affineIsometry, Set.image_comp]

end
end TightVer401

