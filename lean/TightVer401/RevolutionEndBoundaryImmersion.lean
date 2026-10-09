import TightVer401.RevolutionEndBoundaryDifferential
import TightVer401.RevolutionEndRiemannian

namespace TightVer401
noncomputable section
open Set Bundle Manifold OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

abbrev RevolutionClosedEnd (H : ℝ) := AddCircle (2 * Real.pi) × Ici H
abbrev revolutionEndBoundaryModel := 𝓘(ℝ, ℝ).prod (𝓡∂ 1)
def revolutionEndBoundaryInclusion (H : ℝ) : RevolutionClosedEnd H → RevolutionCylinder :=
  Prod.map id (fun z : Ici H => (z : ℝ))

theorem revolutionEndBoundaryInclusion_contMDiff (H : ℝ) :
    ContMDiff revolutionEndBoundaryModel revolutionCylinderModel ∞
      (revolutionEndBoundaryInclusion H) :=
  contMDiff_fst.prodMk ((revolutionEndBoundaryVal_contMDiff H).comp contMDiff_snd)

theorem revolutionEndBoundaryInclusion_mfderiv_injective (H : ℝ) (p : RevolutionClosedEnd H) :
    Function.Injective (mfderiv revolutionEndBoundaryModel revolutionCylinderModel
      (revolutionEndBoundaryInclusion H) p) := by
  rw [revolutionEndBoundaryInclusion, mfderiv_prodMap mdifferentiableAt_id
    (revolutionEndBoundaryVal_hasMFDerivAt H p.2).mdifferentiableAt, mfderiv_id]
  intro v w h
  apply Prod.ext
  · exact congrArg (fun u : ℝ × ℝ => u.1) h
  · apply revolutionEndBoundaryVal_mfderiv_injective H p.2
    exact congrArg (fun u : ℝ × ℝ => u.2) h

theorem revolutionEndCircle_boundary_mfderiv_injective {q : ℝ → ℝ}
    (hq : ContDiff ℝ ∞ q) {H : ℝ} (p : RevolutionClosedEnd H) (hp : q p.2 ≠ 0) :
    Function.Injective (mfderiv revolutionEndBoundaryModel 𝓘(ℝ, Ambient)
      (revolutionEndCircle q H) p) := by
  have heq : revolutionEndCircle q H = revolutionEndCircleFull q ∘ revolutionEndBoundaryInclusion H := by
    funext p
    exact revolutionEndCircle_eq_full q H p
  have hi := (revolutionEndBoundaryInclusion_contMDiff H p).mdifferentiableAt (by simp)
  have hx := (revolutionEndCircleFull_contMDiff hq (revolutionEndBoundaryInclusion H p)).mdifferentiableAt (by simp)
  rw [heq, mfderiv_comp p hx hi]
  intro v w h
  apply revolutionEndBoundaryInclusion_mfderiv_injective H p
  apply revolutionEndCircleFull_mfderiv_injective hq (revolutionEndBoundaryInclusion H p)
    hp
  exact h

end
end TightVer401
