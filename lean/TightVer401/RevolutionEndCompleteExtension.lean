import TightVer401.RevolutionEndCompleteness
import TightVer401.RevolutionEndPositiveExtension

namespace TightVer401
noncomputable section
open Set Bundle OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem revolutionEndEMetricSpace_edist {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hpos : ∀ z, 0 < q z) (p s : RevolutionCylinder) :
    @edist RevolutionCylinder (revolutionEndEMetricSpace hq hpos).toEDist p s =
      (letI : RiemannianBundle
        (fun p : RevolutionCylinder => TangentSpace revolutionCylinderModel p) :=
          ⟨revolutionEndRiemannianMetric hq hpos⟩
       Manifold.riemannianEDist revolutionCylinderModel p s) := rfl

theorem exists_revolutionEnd_complete_positive_extension {q : ℝ → ℝ} {H : ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ z ∈ Ici H, 0 < q z) :
    ∃ (Q : ℝ → ℝ) (hQ : ContDiff ℝ ∞ Q) (hQpos : ∀ z, 0 < Q z),
      (∃ b < H, EqOn Q q (Ioi b)) ∧
      @CompleteSpace RevolutionCylinder (revolutionEndEMetricSpace hQ hQpos).toUniformSpace := by
  obtain ⟨Q, hQ, hQpos, hagree⟩ := exists_revolutionEnd_positive_extension hq hpos
  exact ⟨Q, hQ, hQpos, hagree, revolutionEnd_fullCylinder_complete hQ hQpos⟩

end
end TightVer401
