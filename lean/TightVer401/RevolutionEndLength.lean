import TightVer401.RevolutionEndCircleSmooth
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Manifold
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

 theorem revolution_ambientCurve_length_lower_height {F : ℝ → Ambient}
    (hF : ContDiff ℝ ∞ F) {A B : ℝ} (hAB : A ≤ B) :
    |F B 2 - F A 2| ≤ ∫ t in A..B, ‖deriv F t‖ := by
  have hd := (contDiff_infty_iff_deriv.mp hF).2
  have hi : (∫ t in A..B, deriv F t) = F B - F A :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => (hF.differentiable (by simp) t).hasDerivAt)
      (hd.continuous.intervalIntegrable A B)
  calc
    |F B 2 - F A 2| = ‖(F B - F A) 2‖ := by simp
    _ ≤ ‖F B - F A‖ := PiLp.norm_apply_le _ 2
    _ = ‖∫ t in A..B, deriv F t‖ := congrArg norm hi.symm
    _ ≤ ∫ t in A..B, ‖deriv F t‖ := intervalIntegral.norm_integral_le_integral_norm hAB

 theorem revolutionEnd_height (q : ℝ → ℝ) (p : Coord) : revolutionEnd q p 2 = p 1 := by
  simp [revolutionEnd, revolutionRadial, revolutionAxis]

 theorem revolutionEndCurve_length_lower_height {q : ℝ → ℝ} {c : ℝ → Coord}
    (hq : ContDiff ℝ ∞ q) (hc : ContDiff ℝ ∞ c) {A B : ℝ} (hAB : A ≤ B) :
    |c B 1 - c A 1| ≤ ∫ t in A..B, ‖deriv (revolutionEnd q ∘ c) t‖ := by
  simpa only [Function.comp_apply, revolutionEnd_height] using
    revolution_ambientCurve_length_lower_height ((revolutionEnd_contDiff hq).comp hc) hAB

 theorem revolutionEndCircleFull_height (q : ℝ → ℝ) (p : AddCircle (2 * Real.pi) × ℝ) :
    revolutionEndCircleFull q p 2 = p.2 := by
  simp [revolutionEndCircleFull, revolutionCircleRadial, revolutionAxis]

 theorem revolutionEndCircleCurve_length_lower_height {q : ℝ → ℝ}
    {c : ℝ → AddCircle (2 * Real.pi) × ℝ} (hq : ContDiff ℝ ∞ q)
    (hc : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ c) {A B : ℝ} (hAB : A ≤ B) :
    |(c B).2 - (c A).2| ≤ ∫ t in A..B, ‖deriv (revolutionEndCircleFull q ∘ c) t‖ := by
  have hF : ContDiff ℝ ∞ (revolutionEndCircleFull q ∘ c) :=
    ((revolutionEndCircleFull_contMDiff hq).comp hc).contDiff
  simpa only [Function.comp_apply, revolutionEndCircleFull_height] using
    revolution_ambientCurve_length_lower_height hF hAB

end
end TightVer401
