import TightVer401.DualRadialCompletionProtected

/-! Derive a quantitative neck-attachment margin from the actual compact
filling boundary inside its gradient ball. -/
namespace TightVer401
noncomputable section
open Set Metric
open scoped Topology

/-- The compact returned filling disk admits a strictly separated neck
attachment radius. No quantitative gap is required from the producer. -/
theorem exists_dualRadialCompletion_filling_separation {R M : ℝ}
    (hR : 0 < R) (hM : 0 < M) (Gamma : ℂ ≃ₜ ℂ)
    (hDisk : Gamma '' closedBall (0 : ℂ) 1 ⊆ ball (0 : ℂ) (M * R)) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ R / 2 ∧
      ∀ z ∈ Gamma '' closedBall (0 : ℂ) 1, ‖z‖ < M * (R - rho) := by
  have hCompact : IsCompact (Gamma '' closedBall (0 : ℂ) 1) :=
    (isCompact_closedBall (0 : ℂ) 1).image Gamma.continuous
  have hNonempty : (Gamma '' closedBall (0 : ℂ) 1).Nonempty := by
    refine ⟨Gamma 0, 0, ?_, rfl⟩
    simp
  obtain ⟨zMax, hzMax, hMax⟩ := hCompact.exists_isMaxOn hNonempty
    continuous_norm.continuousOn
  have hBound : ‖zMax‖ < M * R := by
    simpa only [mem_ball, dist_zero_right] using hDisk hzMax
  let rho := min (R / 4) ((M * R - ‖zMax‖) / (2 * M))
  have hrho : 0 < rho := lt_min (by positivity) (div_pos (by linarith) (by positivity))
  have hrhoR : rho ≤ R / 2 := (min_le_left _ _).trans (by linarith)
  have hGap : rho * (2 * M) ≤ M * R - ‖zMax‖ := by
    exact (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  refine ⟨rho, hrho, hrhoR, ?_⟩
  intro z hz
  have hUpper := (isMaxOn_iff.mp hMax) z hz
  have hPositive : 0 < M * rho := mul_pos hM hrho
  nlinarith

end
end TightVer401
