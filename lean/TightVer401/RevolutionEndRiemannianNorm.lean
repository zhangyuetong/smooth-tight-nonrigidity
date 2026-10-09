import TightVer401.RevolutionEndRiemannian
import Mathlib.Geometry.Manifold.Riemannian.PathELength

namespace TightVer401
noncomputable section
open Set Bundle Manifold OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff Topology Bundle
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

 theorem revolutionEndRiemannianMetric_inner {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hpos : ∀ z, 0 < q z) (p : RevolutionCylinder)
    (v w : TangentSpace revolutionCylinderModel p) :
    letI : RiemannianBundle (fun p : RevolutionCylinder => TangentSpace revolutionCylinderModel p) :=
      ⟨revolutionEndRiemannianMetric hq hpos⟩
    inner ℝ v w = inner ℝ
      (show Ambient from mfderiv revolutionCylinderModel 𝓘(ℝ, Ambient) (revolutionEndCircleFull q) p v)
      (show Ambient from mfderiv revolutionCylinderModel 𝓘(ℝ, Ambient) (revolutionEndCircleFull q) p w) := rfl

 theorem revolutionEndRiemannianMetric_norm {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hpos : ∀ z, 0 < q z) (p : RevolutionCylinder)
    (v : TangentSpace revolutionCylinderModel p) :
    letI : RiemannianBundle (fun p : RevolutionCylinder => TangentSpace revolutionCylinderModel p) :=
      ⟨revolutionEndRiemannianMetric hq hpos⟩
    ‖v‖ = ‖show Ambient from mfderiv revolutionCylinderModel 𝓘(ℝ, Ambient) (revolutionEndCircleFull q) p v‖ := by
  letI : RiemannianBundle (fun p : RevolutionCylinder => TangentSpace revolutionCylinderModel p) :=
    ⟨revolutionEndRiemannianMetric hq hpos⟩
  have h := revolutionEndRiemannianMetric_inner hq hpos p v v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg v,
    norm_nonneg (show Ambient from mfderiv revolutionCylinderModel 𝓘(ℝ, Ambient) (revolutionEndCircleFull q) p v)]

end
end TightVer401
