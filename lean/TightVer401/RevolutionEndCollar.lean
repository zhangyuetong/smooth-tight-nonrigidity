import TightVer401.RevolutionEndBoundaryImmersion

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped Topology
set_option backward.isDefEq.respectTransparency false

 theorem revolutionEndCircle_eqOn_collar_of_germ {q q₀ : ℝ → ℝ} {H : ℝ}
    (hgerm : q =ᶠ[𝓝 H] q₀) :
    ∃ ε > 0, ∀ p : RevolutionClosedEnd H, (p.2 : ℝ) ≤ H + ε →
      revolutionEndCircle q H p = revolutionEndCircle q₀ H p := by
  change {z : ℝ | q z = q₀ z} ∈ 𝓝 H at hgerm
  obtain ⟨d, hd, hb⟩ := Metric.mem_nhds_iff.mp hgerm
  refine ⟨d / 2, by positivity, ?_⟩
  intro p hp
  have hz : (p.2 : ℝ) ∈ Metric.ball H d := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr p.2.property)]
    linarith
  have heq := hb hz
  change q (p.2 : ℝ) = q₀ (p.2 : ℝ) at heq
  simp only [revolutionEndCircle, heq]

end
end TightVer401
