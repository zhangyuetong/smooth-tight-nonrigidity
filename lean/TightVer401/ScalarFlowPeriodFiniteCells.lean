import TightVer401.ScalarFlowPeriodReparameter
import TightVer401.ScalarCellComposition

namespace TightVer401
noncomputable section
open Set Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- Finite actual local solutions can share one initial-data neighborhood. Endpoint maps
are formed from the solutions themselves, and matching traces are derived by composition. -/
theorem scalarFlowPeriod_compose_finite_cells {u : ℕ → Coord → ℝ} {r : ℕ → ℝ}
    {f : Coord → ℝ} {W : Set Coord} {ε : ℝ} {N : ℕ}
    (hε : 0 < ε) (hr0 : r 0 = 0)
    (hstep : ∀ j ≤ N, |r (j + 1) - r j| < ε)
    (hu : ∀ j ≤ N, ContDiffOn ℝ ∞ (u j) (scalarCellSource (r j) ε))
    (huW : ∀ j ≤ N, ∀ q ∈ scalarCellSource (r j) ε, (![q 0, u j q] : Coord) ∈ W)
    (hode : ∀ j ≤ N, ∀ q ∈ scalarCellSource (r j) ε,
      coordPartial 0 (u j) q = f ![q 0, u j q])
    (hcentral : ∀ j ≤ N, ∀ a, |a - r j| < ε → u j ![a, 0] = 0)
    (hinit : ∀ j ≤ N, ∀ x, |x| < ε → u j ![r j, x] = x) :
    ∃ e > 0, ∃ w : ℕ → Coord → ℝ,
      (∀ j ≤ N, ContDiffOn ℝ ∞ (w j) (scalarCellStrip (r j) ε (ball 0 e))) ∧
      (∀ j ≤ N, ∀ q ∈ scalarCellStrip (r j) ε (ball 0 e),
        (![q 0, w j q] : Coord) ∈ W ∧ coordPartial 0 (w j) q = f ![q 0, w j q]) ∧
      (∀ j ≤ N, ∀ a, |a - r j| < ε → w j ![a, 0] = 0) ∧
      (∀ j < N, ∀ x ∈ ball (0 : ℝ) e, w j ![r (j+1), x] = w (j+1) ![r (j+1), x]) ∧
      ∀ x ∈ ball (0 : ℝ) e, w 0 ![0, x] = x := by
  let φ : ℕ → ℝ → ℝ := fun j x => u j ![r (j+1), x]
  have hφ (j : ℕ) (hj : j < N+1) : ContDiffOn ℝ ∞ (φ j) (ball 0 ε) :=
    scalarFlowPeriod_endpoint_contDiffOn (hu j (Nat.lt_succ_iff.mp hj))
      (hstep j (Nat.lt_succ_iff.mp hj))
  have hz (j : ℕ) (hj : j < N+1) : φ j 0 = 0 :=
    hcentral j (Nat.lt_succ_iff.mp hj) _ (hstep j (Nat.lt_succ_iff.mp hj))
  obtain ⟨e, he, hsm, hmap⟩ := scalarCellComposition_exists_common_radius
    (N := N+1) (fun _ _ => isOpen_ball) (fun _ _ => mem_ball_self hε) hφ hz
  have hzero := scalarCellPrefix_zero hz
  have hpbound (j : ℕ) (hj : j ≤ N) (x : ℝ) (hx : x ∈ ball (0 : ℝ) e) :
      |scalarCellPrefix φ j x| < ε := by
    have hm := hmap j (Nat.lt_succ_iff.mpr hj) x (by
      simpa only [mem_ball, Real.dist_eq, sub_zero] using hx)
    simpa only [mem_ball, Real.dist_eq, sub_zero] using hm
  let w : ℕ → Coord → ℝ := fun j => scalarCellReparameter (u j) (scalarCellPrefix φ j)
  have hw (j : ℕ) (hj : j ≤ N) := scalarFlowPeriod_reparameter_cell isOpen_ball (hu j hj)
    (hsm j (hj.trans (Nat.le_succ N))) (hpbound j hj) (huW j hj) (hode j hj)
  refine ⟨e, he, w, fun j hj => (hw j hj).1,
    fun j hj q hq => ⟨(hw j hj).2.1 q hq, (hw j hj).2.2 q hq⟩, ?_, ?_, ?_⟩
  · intro j hj a ha
    change u j ![a, scalarCellPrefix φ j 0] = 0
    rw [hzero j (hj.trans (Nat.le_succ N))]
    exact hcentral j hj a ha
  · intro j hj x hx
    change u j ![r (j+1), scalarCellPrefix φ j x] =
      u (j+1) ![r (j+1), scalarCellPrefix φ (j+1) x]
    rw [hinit (j+1) (Nat.succ_le_iff.mpr hj) _
      (hpbound (j+1) (Nat.succ_le_iff.mpr hj) x hx)]
    rfl
  · intro x hx
    change u 0 ![0, scalarCellPrefix φ 0 x] = x
    change u 0 ![0, x] = x
    rw [← hr0]
    exact hinit 0 (Nat.zero_le N) x (hpbound 0 (Nat.zero_le N) x hx)

end
end TightVer401
