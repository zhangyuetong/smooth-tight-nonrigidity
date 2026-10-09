import TightVer401.RevolutionEndBoundaryRiemannian
import Mathlib.Geometry.Manifold.Riemannian.PathELength

namespace TightVer401
noncomputable section
open Set Bundle Manifold OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff Topology Bundle
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

 theorem revolutionEndBoundaryRiemannianMetric_inner {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hpos : ∀ z ∈ Ici H, 0 < q z) (p : RevolutionClosedEnd H)
    (v w : TangentSpace revolutionEndBoundaryModel p) :
    letI : RiemannianBundle (fun p : RevolutionClosedEnd H => TangentSpace revolutionEndBoundaryModel p) :=
      ⟨revolutionEndBoundaryRiemannianMetric hq hpos⟩
    inner ℝ v w = inner ℝ
      (show Ambient from mfderiv revolutionEndBoundaryModel 𝓘(ℝ, Ambient) (revolutionEndCircle q H) p v)
      (show Ambient from mfderiv revolutionEndBoundaryModel 𝓘(ℝ, Ambient) (revolutionEndCircle q H) p w) := rfl

 theorem revolutionEndBoundaryRiemannianMetric_norm {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hpos : ∀ z ∈ Ici H, 0 < q z) (p : RevolutionClosedEnd H)
    (v : TangentSpace revolutionEndBoundaryModel p) :
    letI : RiemannianBundle (fun p : RevolutionClosedEnd H => TangentSpace revolutionEndBoundaryModel p) :=
      ⟨revolutionEndBoundaryRiemannianMetric hq hpos⟩
    ‖v‖ = ‖show Ambient from mfderiv revolutionEndBoundaryModel 𝓘(ℝ, Ambient) (revolutionEndCircle q H) p v‖ := by
  letI : RiemannianBundle (fun p : RevolutionClosedEnd H => TangentSpace revolutionEndBoundaryModel p) :=
    ⟨revolutionEndBoundaryRiemannianMetric hq hpos⟩
  have h := revolutionEndBoundaryRiemannianMetric_inner hq hpos p v v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg v,
    norm_nonneg (show Ambient from mfderiv revolutionEndBoundaryModel 𝓘(ℝ, Ambient) (revolutionEndCircle q H) p v)]

end
end TightVer401

