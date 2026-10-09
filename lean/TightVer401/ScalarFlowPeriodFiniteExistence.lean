import TightVer401.ScalarFlowPeriodUniformFamily
import TightVer401.ScalarFlowPeriodFiniteCells
import TightVer401.ScalarCellTimeGrid

namespace TightVer401
noncomputable section
open Set Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

theorem scalarFlowPeriod_exists_composable_cells {f : Coord → ℝ} {W : Set Coord}
    {P : ℝ} (hP : 0 < P) (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W)
    (hseam : ∀ r : ℝ, (![r, 0] : Coord) ∈ W)
    (hfzero : ∀ r : ℝ, f ![r, 0] = 0) :
    ∃ (N : ℕ) (ε e : ℝ), 0 < N ∧ 0 < ε ∧ 0 < e ∧
      0 < scalarCellStep P N ∧ scalarCellStep P N < ε / 4 ∧
      ∃ w : ℕ → Coord → ℝ,
      (∀ j ≤ N, ContDiffOn ℝ ∞ (w j)
        (scalarCellStrip (scalarCellTime P N j) ε (ball 0 e))) ∧
      (∀ j ≤ N, ∀ q ∈ scalarCellStrip (scalarCellTime P N j) ε (ball 0 e),
        (![q 0, w j q] : Coord) ∈ W ∧ coordPartial 0 (w j) q = f ![q 0, w j q]) ∧
      (∀ j ≤ N, ∀ a, |a - scalarCellTime P N j| < ε → w j ![a, 0] = 0) ∧
      (∀ j < N, ∀ x ∈ ball (0 : ℝ) e,
        w j ![scalarCellTime P N (j+1), x] = w (j+1) ![scalarCellTime P N (j+1), x]) ∧
      ∀ x ∈ ball (0 : ℝ) e, w 0 ![0, x] = x := by
  classical
  obtain ⟨ε, hε, u, hu⟩ := scalarFlowPeriod_exists_uniform_scalar_cells hP.le hW hf hseam hfzero
  obtain ⟨N, hN, hd, hsmall, hr0, hrN, hrmem, hsucc, hcover⟩ :=
    exists_scalarCellTimeGrid hP (by linarith : 0 < ε / 4)
  let c : ℕ → Icc (0 : ℝ) P := fun j =>
    ⟨scalarCellTime P N (min j N), hrmem _ (Nat.min_le_right j N)⟩
  have hc (j : ℕ) (hj : j ≤ N) : (c j : ℝ) = scalarCellTime P N j := by
    simp only [c, Nat.min_eq_left hj]
  have hs (j : ℕ) (hj : j ≤ N) :
      |scalarCellTime P N (j+1) - scalarCellTime P N j| < ε := by
    rw [hsucc j, add_sub_cancel_left, abs_of_pos hd]
    linarith
  obtain ⟨e, he, w, hw⟩ := scalarFlowPeriod_compose_finite_cells
    (u := fun j => u (c j)) (r := scalarCellTime P N) hε hr0 hs
    (fun j hj => by simpa only [hc j hj] using (hu (c j)).1)
    (fun j hj => by simpa only [hc j hj] using (hu (c j)).2.1)
    (fun j hj => by simpa only [hc j hj] using (hu (c j)).2.2.1)
    (fun j hj => by simpa only [hc j hj] using (hu (c j)).2.2.2.1)
    (fun j hj => by simpa only [hc j hj] using (hu (c j)).2.2.2.2)
  exact ⟨N, ε, e, hN, hε, he, hd, hsmall, w, hw⟩

end
end TightVer401
