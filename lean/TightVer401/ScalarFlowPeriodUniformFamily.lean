import TightVer401.ScalarFlowPeriodLocalFamily

namespace TightVer401
noncomputable section
open Set Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- Actual scalar solution cells with a common positive time and initial-data width. -/
theorem scalarFlowPeriod_exists_uniform_scalar_cells {f : Coord → ℝ} {W : Set Coord}
    {P : ℝ} (hP : 0 ≤ P) (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W)
    (hseam : ∀ r : ℝ, (![r, 0] : Coord) ∈ W)
    (hfzero : ∀ r : ℝ, f ![r, 0] = 0) :
    ∃ ε > 0, ∃ u : Icc (0 : ℝ) P → Coord → ℝ,
      ∀ r : Icc (0 : ℝ) P,
        ContDiffOn ℝ ∞ (u r) (scalarCellSource r ε) ∧
        (∀ q ∈ scalarCellSource r ε, (![q 0, u r q] : Coord) ∈ W) ∧
        (∀ q ∈ scalarCellSource r ε, coordPartial 0 (u r) q = f ![q 0, u r q]) ∧
        (∀ a : ℝ, |a - r| < ε → u r ![a, 0] = 0) ∧
        ∀ x : ℝ, |x| < ε → u r ![r, x] = x := by
  classical
  obtain ⟨δ, hδ, s, D, Φ, hflow, hcover⟩ :=
    scalarFlowPeriod_exists_uniform_finite_cells hP hW hf (fun r _ => hseam r)
  choose c hc hbox using fun r : Icc (0 : ℝ) P => hcover r r.property
  refine ⟨δ / 2, half_pos hδ, fun r => scalarCellMap (Φ (c r)) r, ?_⟩
  intro r
  exact scalarFlowPeriod_extract_scalar_cell hδ hW hf (hflow _ (hc r)).2.1
    (hflow _ (hc r)).2.2.1 (hflow _ (hc r)).2.2.2 hseam hfzero (hbox r)

end
end TightVer401
