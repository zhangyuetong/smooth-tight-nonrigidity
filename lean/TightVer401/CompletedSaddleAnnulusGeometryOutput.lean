import TightVer401.CompletedSaddleAnnulusProtectedBand
import TightVer401.NativeProductPlaneCurvature

/-! Full geometric output specification for the completed saddle producer.
This has no claimed inhabitant; the actual construction remains pending. -/
open Manifold
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Actual height separation and negative intrinsic curvature accompany the
native cylinder and its genuine protected coordinate map in the full output. -/
structure CompletedSaddleAnnulusGeometryOutput {T w : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T) (K : Set (AddCircle T × Ioo (0 : ℝ) w))
    (RN μ h : ℝ) extends CompletedSaddleAnnulusOutput d K RN μ h where
  height_separation : ∀ p ∈ (univ : Set (AddCircle (2 * Real.pi))) ×ˢ Ioo (0 : ℝ) Real.pi,
    -h < cylinder.saddle p 2 ∧ cylinder.saddle p 2 < h
  curvature_neg : ∀ p ∈ (univ : Set (AddCircle (2 * Real.pi))) ×ˢ Ioo (0 : ℝ) Real.pi,
    gaussianCurvature (inducedMetric (nativeProductCoordinateMap cylinder.saddle p))
      ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm (chartAt (ModelProd ℝ ℝ) p p)) < 0

end
end TightVer401
