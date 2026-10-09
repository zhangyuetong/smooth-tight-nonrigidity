import TightVer401.ExitPositiveGraphTangent

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem exitGraphCurve_uniform_domain {v : ℝ → ℝ} {U : Set Coord} {P : ℝ}
    (hv : ContDiff ℝ ∞ v) (hU : IsOpen U)
    (hseam : ∀ r ∈ Icc (0 : ℝ) P, (![r, 0] : Coord) ∈ U) :
    ∃ ε > 0, ∀ r ∈ Icc (0 : ℝ) P, ∀ δ, |δ| ≤ ε → exitGraphCurve v δ r ∈ U := by
  let V := (exitGraphPoint v) ⁻¹' U
  have hV : IsOpen V := hU.preimage (exitGraphPoint_contDiff hv).continuous
  have hs : ∀ r ∈ Icc (0 : ℝ) P, (![r, 0] : Coord) ∈ V := by
    intro r hr
    simpa [V, exitGraphPoint] using hseam r hr
  have hd : ∀ r ∈ Icc (0 : ℝ) P, 0 < coordPartial 1 (fun p : Coord => p 1) ![r, 0] := by
    intro r hr
    rw [coordPartial_proj]
    simp
  obtain ⟨ε, hε, he⟩ := exitGraph_uniform_derivative_positive hV
    (contDiff_apply ℝ ℝ 1).contDiffOn hs hd
  refine ⟨ε, hε, ?_⟩
  intro r hr δ hδ
  exact (he r hr δ hδ).1

end
end TightVer401
