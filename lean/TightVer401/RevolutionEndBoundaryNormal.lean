import TightVer401.RevolutionEndBoundaryImmersion
import TightVer401.RevolutionEndGaussSmooth

namespace TightVer401
noncomputable section
open Set Bundle Manifold OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

theorem revolutionEndCircle_boundary_normal_orthogonal {q : ℝ → ℝ}
    (hq : ContDiff ℝ ∞ q) {H : ℝ} (p : RevolutionClosedEnd H)
    (v : TangentSpace revolutionEndBoundaryModel p) :
    inner ℝ (show Ambient from mfderiv revolutionEndBoundaryModel 𝓘(ℝ, Ambient)
      (revolutionEndCircle q H) p v)
      (revolutionEndCircleNormal q (revolutionEndBoundaryInclusion H p)) = 0 := by
  have heq : revolutionEndCircle q H = revolutionEndCircleFull q ∘ revolutionEndBoundaryInclusion H := by
    funext p
    exact revolutionEndCircle_eq_full q H p
  have hi := (revolutionEndBoundaryInclusion_contMDiff H p).mdifferentiableAt (by simp)
  have hx := (revolutionEndCircleFull_contMDiff hq (revolutionEndBoundaryInclusion H p)).mdifferentiableAt (by simp)
  rw [heq, mfderiv_comp p hx hi]
  exact revolutionEndCircleNormal_orthogonal hq (revolutionEndBoundaryInclusion H p)
    (mfderiv revolutionEndBoundaryModel revolutionCylinderModel (revolutionEndBoundaryInclusion H) p v)

theorem revolutionEndCircle_boundary_isUnitNormal {q : ℝ → ℝ}
    (hq : ContDiff ℝ ∞ q) {H : ℝ} (p : RevolutionClosedEnd H) :
    inner ℝ (revolutionEndCircleNormal q (revolutionEndBoundaryInclusion H p))
      (revolutionEndCircleNormal q (revolutionEndBoundaryInclusion H p)) = 1 ∧
    ∀ v : TangentSpace revolutionEndBoundaryModel p,
      inner ℝ (show Ambient from mfderiv revolutionEndBoundaryModel 𝓘(ℝ, Ambient)
        (revolutionEndCircle q H) p v)
        (revolutionEndCircleNormal q (revolutionEndBoundaryInclusion H p)) = 0 :=
  ⟨revolutionEndCircleNormal_unit q _, revolutionEndCircle_boundary_normal_orthogonal hq p⟩

theorem revolutionEndGauss_boundary_contMDiff {q : ℝ → ℝ}
    (hq : ContDiff ℝ ∞ q) (H : ℝ) :
    ContMDiff revolutionEndBoundaryModel (𝓡 2) ∞ (revolutionEndGauss q H) := by
  have h := (revolutionEndCircleGauss_contMDiff hq).comp (revolutionEndBoundaryInclusion_contMDiff H)
  convert h using 1
  funext p
  exact revolutionEndGauss_eq_full q H p

end
end TightVer401
