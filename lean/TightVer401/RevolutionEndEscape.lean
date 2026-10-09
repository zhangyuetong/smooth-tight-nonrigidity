import TightVer401.RevolutionEndLength

namespace TightVer401
noncomputable section
open Set Filter Bundle Manifold OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem revolutionEndCircleCurve_length_tendsto_atTop {q : ℝ → ℝ}
    (hq : ContDiff ℝ ∞ q) {c : ℝ → AddCircle (2 * Real.pi) × ℝ}
    (hc : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ c)
    (hescape : Tendsto (fun t => (c t).2) atTop atTop) (A : ℝ) :
    Tendsto (fun B => ∫ t in A..B, ‖deriv (revolutionEndCircleFull q ∘ c) t‖) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop A, hescape.eventually_ge_atTop (b + (c A).2)] with B hAB hB
  have hlength := revolutionEndCircleCurve_length_lower_height hq hc hAB
  calc
    b ≤ (c B).2 - (c A).2 := by linarith
    _ ≤ |(c B).2 - (c A).2| := le_abs_self _
    _ ≤ ∫ t in A..B, ‖deriv (revolutionEndCircleFull q ∘ c) t‖ := hlength

end
end TightVer401
