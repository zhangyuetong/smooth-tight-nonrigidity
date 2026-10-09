import TightVer401.SeamChartContinuity
import Mathlib.Topology.MetricSpace.Thickening

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

theorem seam_compact_axis_open_collar {K : Set ℝ} (hK : IsCompact K)
    {U : Set Coord} (hU : IsOpen U) (haxis : ∀ s ∈ K, (![s,0] : Coord) ∈ U) :
    ∃ r > 0, ∀ s ∈ K, ∀ t : ℝ, |t| ≤ r → (![s,t] : Coord) ∈ U := by
  let A : Set Coord := (fun s : ℝ => (![s,0] : Coord)) '' K
  have hA : IsCompact A := hK.image (by fun_prop)
  have hAU : A ⊆ U := by
    rintro _ ⟨s,hs,rfl⟩
    exact haxis s hs
  obtain ⟨r,hr,hthick⟩ := hA.exists_cthickening_subset_open hU hAU
  refine ⟨r/2,half_pos hr,fun s hs t ht => ?_⟩
  apply hthick
  apply Metric.thickening_subset_cthickening r A
  apply Metric.mem_thickening_iff.mpr
  refine ⟨(![s,0] : Coord),⟨s,hs,rfl⟩,?_⟩
  rw [dist_eq_norm]
  have hn : ‖(![s,t] : Coord)-![s,0]‖ ≤ r/2 := by
    apply (pi_norm_le_iff_of_nonneg (half_pos hr).le).mpr
    intro i
    fin_cases i
    · change ‖s-s‖ ≤ r/2
      rw [sub_self,norm_zero]
      exact (half_pos hr).le
    · change ‖t-0‖ ≤ r/2
      simpa only [sub_zero,Real.norm_eq_abs] using ht
  exact hn.trans_lt (half_lt_self hr)

/-- Actual regularity along a compact seam persists on an actual uniform collar. -/
theorem seamCoordinateJacobian_compact_regular_collar {Φ : Coord → Coord}
    (hΦ : ContDiff ℝ ∞ Φ) {K : Set ℝ} (hK : IsCompact K)
    (hJ : ∀ s ∈ K, (seamCoordinateJacobian Φ (![s,0])).det ≠ 0) :
    ∃ r > 0, ∀ s ∈ K, ∀ t : ℝ, |t| ≤ r →
      (seamCoordinateJacobian Φ (![s,t])).det ≠ 0 := by
  exact seam_compact_axis_open_collar (U := {p : Coord | (seamCoordinateJacobian Φ p).det ≠ 0}) hK
    (isOpen_ne.preimage (seamCoordinateJacobian_continuous hΦ |>.matrix_det)) hJ

end
end TightVer401
