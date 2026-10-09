import TightVer401.SmoothingPatchedStateBounds
import TightVer401.SmoothingBranchPullback

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff BigOperators

/-- Bounds for the actual curved-chart connection follow from geometric
regularity and compactness, and need not be supplied by a smoothing package. -/
theorem relativeSaddle_compact_connection_bound {Φ : Coord → Coord}
    (hΦ : ContDiff ℝ ∞ Φ) {S : Set Coord} (hS : IsCompact S)
    (hJ : ∀ p ∈ S, (seamCoordinateJacobian Φ p).det ≠ 0) :
    ∃ C > 0, ∀ p ∈ S, ∀ k i j : Fin 2, |seamChartConnection Φ k i j p| ≤ C := by
  let A : Coord → (Fin 2 → Fin 2 → Fin 2 → ℝ) :=
    fun p k i j => seamChartConnection Φ k i j p
  have hc : ContinuousOn A S := by
    intro p hp
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_pi.mpr
    intro k
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    exact seamChartConnection_continuousAt hΦ (hJ p hp) k i j
  obtain ⟨B,hB⟩ := hS.exists_bound_of_continuousOn hc
  refine ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro p hp k i j
  change ‖A p k i j‖ ≤ max 1 B
  exact (norm_le_pi_norm (A p k i) j).trans
    ((norm_le_pi_norm (A p k) i).trans
      ((norm_le_pi_norm (A p) k).trans ((hB p hp).trans (le_max_right _ _))))

/-- Uniform quantitative control of the constructed normal profile and its
cutoff correction, with actual cutoff bounds obtained from compactness. -/
theorem relativeSaddleProfile_error_bounds :
    ∃ B₁ > 0, ∃ B₂ > 0, ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 → ∀ t : ℝ,
      |smoothingPatchedProfile δ hδ (Real.sqrt δ) t - (max t 0)^2| ≤ 7*δ^2 ∧
      |deriv (smoothingPatchedProfile δ hδ (Real.sqrt δ)) t - 2*max t 0| ≤
        4*δ + 3*B₁*δ*Real.sqrt δ ∧
      (|t| ≤ 2*Real.sqrt δ →
        |smoothingPatchedProfile δ hδ (Real.sqrt δ) t| ≤ 11*δ ∧
        |deriv (smoothingPatchedProfile δ hδ (Real.sqrt δ)) t| ≤
          (8+3*B₁*δ)*Real.sqrt δ ∧
        |deriv (deriv (smoothingPatchedProfile δ hδ (Real.sqrt δ))) t/2 -
          smoothingNormalCDF δ hδ t| ≤ (3*B₂/2)*δ) := by
  obtain ⟨B₁,hB₁,B₂,hB₂,hB⟩ := smoothingNormalStep_uniform_derivative_bounds
  refine ⟨B₁,hB₁,B₂,hB₂,fun δ hδ hd t => ?_⟩
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hid : δ^2*(B₁/Real.sqrt δ)=B₁*δ*Real.sqrt δ := by
    have hr : δ/Real.sqrt δ=Real.sqrt δ :=
      (div_eq_iff (ne_of_gt hs)).mpr (by nlinarith [Real.sq_sqrt hδ.le])
    calc
      _ = B₁*δ*(δ/Real.sqrt δ) := by ring
      _ = _ := by rw [hr]
  refine ⟨smoothingPatchedProfile_uniform_value_error δ hδ _ t, ?_, ?_⟩
  · have he := smoothingPatchedProfile_first_error δ hδ hs hB₁.le
      (hB (Real.sqrt δ) hs t).1
    rw [show 3*δ^2*(B₁/Real.sqrt δ)=3*(δ^2*(B₁/Real.sqrt δ)) by ring, hid] at he
    simpa only [mul_assoc] using he
  · intro ht
    exact smoothingPatchedProfile_sqrt_state_bounds δ hδ hd hB₁.le hB₂.le ht
      (hB (Real.sqrt δ) hs t).1 (hB (Real.sqrt δ) hs t).2

/-- The precise curved-coordinate error: gradient error contributes through the
actual connection, in addition to the coordinate Hessian error. -/
theorem relativeSaddle_correctedHessian_error {Φ : Coord → Coord} {F G : Coord → ℝ}
    {p : Coord} {C ε ν : ℝ} (hC : 0 ≤ C)
    (hConnection : ∀ k i j : Fin 2, |seamChartConnection Φ k i j p| ≤ C)
    (hGradient : ∀ k : Fin 2, |coordPartial k F p - coordPartial k G p| ≤ ε)
    (hHessian : ∀ i j : Fin 2, |planarHessian F p i j - planarHessian G p i j| ≤ ν)
    (i j : Fin 2) :
    |seamCorrectedHessian Φ F p i j - seamCorrectedHessian Φ G p i j| ≤ ν + 2*C*ε := by
  have hb (k : Fin 2) :
      |seamChartConnection Φ k i j p * (coordPartial k F p - coordPartial k G p)| ≤ C*ε := by
    rw [abs_mul]
    exact mul_le_mul (hConnection k i j) (hGradient k) (abs_nonneg _) hC
  have he : seamCorrectedHessian Φ F p i j - seamCorrectedHessian Φ G p i j =
      (planarHessian F p i j - planarHessian G p i j) -
        (seamChartConnection Φ 0 i j p * (coordPartial 0 F p - coordPartial 0 G p) +
          seamChartConnection Φ 1 i j p * (coordPartial 1 F p - coordPartial 1 G p)) := by
    simp only [seamCorrectedHessian, Fin.sum_univ_two]
    ring
  rw [he]
  have hTriangle (a b : ℝ) : |a-b| ≤ |a|+|b| := by
    simpa only [sub_zero, zero_sub, abs_neg] using (abs_sub_le a 0 b)
  calc
    _ ≤ |planarHessian F p i j - planarHessian G p i j| +
        |seamChartConnection Φ 0 i j p * (coordPartial 0 F p - coordPartial 0 G p) +
          seamChartConnection Φ 1 i j p * (coordPartial 1 F p - coordPartial 1 G p)| := hTriangle _ _
    _ ≤ ν + (C*ε + C*ε) := add_le_add (hHessian i j)
      ((abs_add_le _ _).trans (add_le_add (hb 0) (hb 1)))
    _ = ν + 2*C*ε := by ring

end
end TightVer401
