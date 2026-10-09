import TightVer401.NativeProductPlaneForms
import TightVer401.CurvatureLocality
import TightVer401.PlanarSupportCurvature
import TightVer401.RuledCurvature

/-! Local intrinsic curvature in the same physical two-coordinate representatives.
This identifies the actual pulled-back metric fields, not ambient chordal distance. -/
open Manifold
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter OAI.ClosedSurfaceR4 OAI.SmoothLocal.Geometry

section Charts
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ModelProd ℝ ℝ) M]
local instance nativeProductPlaneCurvatureChartedSpace : ChartedSpace Plane M := nativeProductPlaneChartedSpace M

/-- Native preferred chart read in the existing physical Coord model. -/
def nativeProductCoordinateMap (F : M → Ambient) (p : M) : Coord → Ambient :=
  fun q => F ((chartAt (ModelProd ℝ ℝ) p).symm (q 0, q 1))

/-- Transported plane preferred chart read in the same physical Coord model. -/
def nativeProductPlaneCoordinateMap (F : M → Ambient) (p : M) : Coord → Ambient :=
  fun q => F ((chartAt Plane p).symm ((EuclideanSpace.equiv (Fin 2) ℝ).symm q))

/-- The explicit inverse coordinate equivalence identifies the two actual chart maps. -/
theorem nativeProductPlane_coordinateMap_eq (F : M → Ambient) (p : M) :
    nativeProductPlaneCoordinateMap F p = nativeProductCoordinateMap F p := by
  funext q
  rfl

/-- Derivative of the actual preferred-chart representative, at the native chart center. -/
theorem nativeProductPlane_coordinate_fderiv {F : M → Ambient} {p : M}
    (hF : MDifferentiableAt nativeProductModel 𝓘(ℝ, Ambient) F p) :
    fderiv ℝ (nativeProductCoordinateMap F p)
      ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm (chartAt (ModelProd ℝ ℝ) p p)) =
    (mfderiv nativeProductModel 𝓘(ℝ, Ambient) F p).comp
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).toContinuousLinearMap := by
  have hr : Set.range nativeProductModel = Set.univ := ModelWithCorners.range_eq_univ nativeProductModel
  have h := hF.hasMFDerivAt.2
  rw [hr] at h
  have hd : HasFDerivAt (fun x : ℝ × ℝ => F ((chartAt (ModelProd ℝ ℝ) p).symm x))
      (mfderiv nativeProductModel 𝓘(ℝ, Ambient) F p)
      (chartAt (ModelProd ℝ ℝ) p p) := by
    convert! h.hasFDerivAt_of_univ using 1 <;>
      simp [writtenInExtChartAt, extChartAt, nativeProductModel, Function.comp_def]
  have hc := hd.comp ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
      (chartAt (ModelProd ℝ ℝ) p p)) (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).hasFDerivAt
  convert! hc.fderiv using 1 <;> rfl

/-- The actual local metric coefficients are the OpenAI manifold induced pairing
on the explicitly transported coordinate basis. -/
theorem nativeProductPlane_coordinate_inducedForm {F : M → Ambient} {p : M}
    (hF : MDifferentiableAt nativeProductModel 𝓘(ℝ, Ambient) F p) (i j : Fin 2) :
    inducedMetric (nativeProductPlaneCoordinateMap F p)
      ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm (chartAt (ModelProd ℝ ℝ) p p)) i j =
    inducedForm F p
      (nativeProductPlaneEquiv ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ) (Pi.single i 1)))
      (nativeProductPlaneEquiv ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ) (Pi.single j 1))) := by
  rw [nativeProductPlane_coordinateMap_eq, nativeProductPlane_inducedForm hF]
  simp only [inducedMetric, coordPartial, nativeProductPlane_coordinate_fderiv hF,
    ContinuousLinearMap.comp_apply, nativeProductInducedForm]
  rfl

/-- Equality of the actual induced metric fields, including all derivatives used by curvature. -/
theorem nativeProductPlane_coordinate_metric (F : M → Ambient) (p : M) :
    inducedMetric (nativeProductPlaneCoordinateMap F p) =
      inducedMetric (nativeProductCoordinateMap F p) := by
  rw [nativeProductPlane_coordinateMap_eq]

/-- Local intrinsic curvature compatibility for arbitrary actual native surfaces. -/
theorem nativeProductPlane_coordinate_curvature (F : M → Ambient) (p : M) (q : Coord) :
    gaussianCurvature (inducedMetric (nativeProductPlaneCoordinateMap F p)) q =
      gaussianCurvature (inducedMetric (nativeProductCoordinateMap F p)) q := by
  rw [nativeProductPlane_coordinate_metric]

/-- A local matching map germ transfers actual intrinsic curvature to the transported chart. -/
theorem nativeProductPlane_curvature_of_chart_germ {F : M → Ambient} {p : M}
    {X : Coord → Ambient} {q : Coord}
    (h : nativeProductCoordinateMap F p =ᶠ[𝓝 q] X) :
    gaussianCurvature (inducedMetric (nativeProductPlaneCoordinateMap F p)) q =
      gaussianCurvature (inducedMetric X) q := by
  rw [nativeProductPlane_coordinate_curvature]
  exact gaussianCurvature_eq_of_eventuallyEq (inducedMetric_eventuallyEq h)

/-- Apply the actual support curvature formula through a matching local native chart. -/
theorem nativeProductPlane_support_curvature {F : M → Ambient} {p : M}
    {G : Coord → ℝ} {U : Set Coord} {q : Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) (hq : q ∈ U)
    (hdet : (planarHessian G q).det ≠ 0)
    (h : nativeProductCoordinateMap F p =ᶠ[𝓝 q] planarSupportMap G) :
    gaussianCurvature (inducedMetric (nativeProductPlaneCoordinateMap F p)) q =
      1 / (planarWeight q ^ 4 * (planarHessian G q).det) := by
  rw [nativeProductPlane_curvature_of_chart_germ h]
  exact planarSupportMap_gaussianCurvature_at hG hU hq hdet

/-- Likewise, a ruled-band chart germ transfers the retained strict negative curvature. -/
theorem nativeProductPlane_ruled_curvature {F : M → Ambient} {p : M}
    {γ T E n : ℝ → Ambient} {k τ : ℝ → ℝ} {U : Set Coord} {q : Coord}
    (hγ : ∀ s, HasDerivAt γ (T s) s)
    (hE : ∀ s, HasDerivAt E (-k s • T s + τ s • n s) s)
    (hX : ContDiffOn ℝ ∞ (ruledMap γ E) U) (hU : IsOpen U) (hq : q ∈ U)
    (hf : ∀ z ∈ U, IsOrthonormalFrame (T (z 0)) (E (z 0)) (n (z 0)))
    (hτ : ∀ z ∈ U, τ (z 0) ≠ 0)
    (h : nativeProductCoordinateMap F p =ᶠ[𝓝 q] ruledMap γ E) :
    gaussianCurvature (inducedMetric (nativeProductPlaneCoordinateMap F p)) q < 0 := by
  rw [nativeProductPlane_curvature_of_chart_germ h]
  exact ruled_gaussianCurvature_neg hγ hE hX hU hf hτ hq

end Charts
end
end TightVer401



