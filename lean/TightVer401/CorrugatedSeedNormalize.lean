import TightVer401.CorrugatedSeedTangentBounds

namespace TightVer401
noncomputable section

theorem corrugated_normalize_distance {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {z w : E} (hz : z ≠ 0) (hw : w ≠ 0) :
    ‖‖z‖⁻¹ • z - ‖w‖⁻¹ • w‖ ≤ 2 * ‖z - w‖ / ‖w‖ := by
  have hzp : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hwp : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have he : ‖z‖⁻¹ • z - ‖w‖⁻¹ • w =
      (‖z‖⁻¹ - ‖w‖⁻¹) • z + ‖w‖⁻¹ • (z - w) := by module
  have hfirst : ‖(‖z‖⁻¹ - ‖w‖⁻¹) • z‖ ≤ ‖z - w‖ / ‖w‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    have ha : (‖z‖⁻¹ - ‖w‖⁻¹) * ‖z‖ = (‖w‖ - ‖z‖) / ‖w‖ := by
      field_simp
    calc
      _ = |(‖z‖⁻¹ - ‖w‖⁻¹) * ‖z‖| := by rw [abs_mul, abs_of_nonneg hzp.le]
      _ = |‖w‖ - ‖z‖| / ‖w‖ := by rw [ha, abs_div, abs_of_pos hwp]
      _ ≤ ‖z - w‖ / ‖w‖ := by
        apply div_le_div_of_nonneg_right _ hwp.le
        simpa only [norm_sub_rev] using abs_norm_sub_norm_le w z
  have hsecond : ‖‖w‖⁻¹ • (z - w)‖ = ‖z - w‖ / ‖w‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hwp)]
    ring
  rw [he]
  calc
    _ ≤ ‖(‖z‖⁻¹ - ‖w‖⁻¹) • z‖ + ‖‖w‖⁻¹ • (z - w)‖ := norm_add_le _ _
    _ ≤ ‖z - w‖ / ‖w‖ + ‖z - w‖ / ‖w‖ := add_le_add hfirst hsecond.le
    _ = 2 * ‖z - w‖ / ‖w‖ := by ring

def corrugatedSeedUnitTangent (N t : ℝ) : ℂ :=
  ‖corrugatedSeedBetaVelocity N t‖⁻¹ • corrugatedSeedBetaVelocity N t

def corrugatedSeedLimitingUnitTangent (N t : ℝ) : ℂ :=
  ‖corrugatedSeedLimitingVelocity N t‖⁻¹ • corrugatedSeedLimitingVelocity N t

theorem corrugatedSeedLimitingVelocity_norm (N t : ℝ) :
    ‖corrugatedSeedLimitingVelocity N t‖ = ‖corrugatedSeedLimitingFactor (N * t)‖ := by
  simp only [corrugatedSeedLimitingVelocity, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem corrugatedSeedUnitTangent_error {N : ℝ} (hN : 1 < N) (t : ℝ) :
    ‖corrugatedSeedUnitTangent N t - corrugatedSeedLimitingUnitTangent N t‖ < 50 / N := by
  have hNp : 0 < N := by linarith
  have hv : corrugatedSeedLimitingVelocity N t ≠ 0 :=
    mul_ne_zero (Complex.exp_ne_zero _) (corrugatedSeedLimitingFactor_ne_zero _)
  have hp : 0 < ‖corrugatedSeedLimitingVelocity N t‖ := norm_pos_iff.mpr hv
  have hnorm : (11 / 25 : ℝ) < ‖corrugatedSeedLimitingVelocity N t‖ := by
    have h := corrugatedSeedLimitingFactor_norm_lower (N * t)
    rw [← corrugatedSeedLimitingVelocity_norm N t] at h
    by_contra hn
    have hn' := le_of_not_gt hn
    have hs : ‖corrugatedSeedLimitingVelocity N t‖^2 ≤ (11 / 25 : ℝ)^2 :=
      pow_le_pow_left₀ hp.le hn' 2
    nlinarith
  have h := corrugated_normalize_distance (corrugatedSeedBetaVelocity_ne_zero hN t) hv
  calc
    _ ≤ 2 * ‖corrugatedSeedBetaVelocity N t - corrugatedSeedLimitingVelocity N t‖ /
        ‖corrugatedSeedLimitingVelocity N t‖ := h
    _ ≤ 2 * (11 / N) / ‖corrugatedSeedLimitingVelocity N t‖ := by
      apply div_le_div_of_nonneg_right _ hp.le
      exact mul_le_mul_of_nonneg_left (corrugatedSeedBetaVelocity_error hNp t) (by norm_num)
    _ < 50 / N := by
      apply (div_lt_iff₀ hp).mpr
      have h' := mul_lt_mul_of_pos_left hnorm (show 0 < 50 / N by positivity)
      have he : 50 / N * (11 / 25 : ℝ) = 2 * (11 / N) := by ring
      rw [he] at h'
      exact h'

end
end TightVer401
