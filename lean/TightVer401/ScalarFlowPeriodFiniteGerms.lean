import TightVer401.ScalarFlowPeriodFiniteExistence
import TightVer401.ScalarFlowPeriodOverlapGerm

namespace TightVer401
noncomputable section
open Set Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

theorem scalarFlowPeriod_adjacent_germs {w : ℕ → Coord → ℝ} {r : ℕ → ℝ}
    {f : Coord → ℝ} {W : Set Coord} {ε e : ℝ} {N : ℕ}
    (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W)
    (hw : ∀ j ≤ N, ContDiffOn ℝ ∞ (w j) (scalarCellStrip (r j) ε (ball 0 e)))
    (hactual : ∀ j ≤ N, ∀ q ∈ scalarCellStrip (r j) ε (ball 0 e),
      (![q 0, w j q] : Coord) ∈ W ∧ coordPartial 0 (w j) q = f ![q 0, w j q])
    (htrace : ∀ j < N, ∀ x ∈ ball (0 : ℝ) e, w j ![r (j+1), x] = w (j+1) ![r (j+1), x]) :
    ∀ j < N, ∀ q ∈ scalarCellStrip (r j) ε (ball 0 e) ∩
        scalarCellStrip (r (j+1)) ε (ball 0 e),
      q 0 = r (j+1) → w j =ᶠ[𝓝 q] w (j+1) := by
  intro j hj q hq hqt
  have heq : (![r (j+1), q 1] : Coord) = q := by
    ext i
    fin_cases i
    · exact hqt.symm
    · rfl
  have htr : (fun x => w j ![r (j+1), x]) =ᶠ[𝓝 (q 1)]
      (fun x => w (j+1) ![r (j+1), x]) := by
    filter_upwards [isOpen_ball.mem_nhds hq.1.2] with x hx
    exact htrace j hj x hx
  have hg := scalarFlowPeriod_initial_germ_unique
    (scalarCellStrip_isOpen isOpen_ball) (scalarCellStrip_isOpen isOpen_ball) hW hf
    (hw j hj.le) (hw (j+1) (Nat.succ_le_iff.mpr hj))
    (by rw [heq]; exact hq.1) (by rw [heq]; exact hq.2)
    (fun q hq => (hactual j hj.le q hq).1)
    (fun q hq => (hactual (j+1) (Nat.succ_le_iff.mpr hj) q hq).1)
    (fun q hq => (hactual j hj.le q hq).2)
    (fun q hq => (hactual (j+1) (Nat.succ_le_iff.mpr hj) q hq).2) htr
  simpa only [heq] using hg

theorem scalarFlowPeriod_adjacent_seam_germs {w : ℕ → Coord → ℝ} {r : ℕ → ℝ}
    {f : Coord → ℝ} {W : Set Coord} {ε e : ℝ} {N : ℕ}
    (hε : 0 < ε) (hstep : ∀ j < N, |r (j+1) - r j| < ε)
    (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W)
    (hw : ∀ j ≤ N, ContDiffOn ℝ ∞ (w j) (scalarCellStrip (r j) ε (ball 0 e)))
    (hactual : ∀ j ≤ N, ∀ q ∈ scalarCellStrip (r j) ε (ball 0 e),
      (![q 0, w j q] : Coord) ∈ W ∧ coordPartial 0 (w j) q = f ![q 0, w j q])
    (htrace : ∀ j < N, ∀ x ∈ ball (0 : ℝ) e, w j ![r (j+1), x] = w (j+1) ![r (j+1), x]) :
    ∀ j < N, ∀ x ∈ ball (0 : ℝ) e,
      w j =ᶠ[𝓝 (![r (j+1), x] : Coord)] w (j+1) := by
  intro j hj x hx
  apply scalarFlowPeriod_adjacent_germs hW hf hw hactual htrace j hj
  · constructor
    · exact ⟨by simpa using hstep j hj, by simpa using hx⟩
    · exact ⟨by simpa using hε, by simpa using hx⟩
  · rfl

end
end TightVer401
