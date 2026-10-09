import TightVer401.CorrugatedSeedVisibility

namespace TightVer401
noncomputable section

theorem corrugatedVisibilityCoefficient_distance {R r s : ℝ}
    (hR : 0 ≤ R) (hr : 0 < r) (hs : 0 < s)
    (hRr : R < r) (hRs : R < s)
    (hqr : 1 / 2 ≤ Real.sqrt (r^2 - R^2) / r)
    (hqs : 1 / 2 ≤ Real.sqrt (s^2 - R^2) / s) :
    ‖corrugatedVisibilityCoefficient R r - corrugatedVisibilityCoefficient R s‖ ≤
      3 * R * |r - s| / (r * s) := by
  have hrc := corrugatedVisibilityCoefficient_components hR hr hRr
  have hsc := corrugatedVisibilityCoefficient_components hR hs hRs
  have h := corrugated_upper_semicircle_distance hrc.1 hrc.2.1 hsc.1 hsc.2.1
    hqr hqs hrc.2.2.2 hsc.2.2.2
  change ‖corrugatedVisibilityCoefficient R r - corrugatedVisibilityCoefficient R s‖ ≤
    3 * |R / r - R / s| at h
  have he : R / r - R / s = R * (s - r) / (r * s) := by field_simp
  rw [he, abs_div, abs_mul, abs_of_nonneg hR, abs_of_pos (mul_pos hr hs), abs_sub_comm] at h
  exact h.trans_eq (by ring)

theorem corrugatedVisibilityDirection_distance {R : ℝ} {z w : ℂ}
    (hR : 0 ≤ R) (hz : R < ‖z‖) (hw : R < ‖w‖)
    (hqz : 1 / 2 ≤ Real.sqrt (‖z‖^2 - R^2) / ‖z‖)
    (hqw : 1 / 2 ≤ Real.sqrt (‖w‖^2 - R^2) / ‖w‖) :
    ‖corrugatedVisibilityDirection R z - corrugatedVisibilityDirection R w‖ ≤
      2 * ‖z - w‖ / ‖w‖ + 3 * R * ‖z - w‖ / (‖z‖ * ‖w‖) := by
  have hzp : 0 < ‖z‖ := hR.trans_lt hz
  have hwp : 0 < ‖w‖ := hR.trans_lt hw
  have hzne : z ≠ 0 := norm_pos_iff.mp hzp
  have hwne : w ≠ 0 := norm_pos_iff.mp hwp
  rw [corrugatedVisibilityDirection_eq hzne, corrugatedVisibilityDirection_eq hwne]
  have he : (‖z‖⁻¹ • z) * corrugatedVisibilityCoefficient R ‖z‖ -
      (‖w‖⁻¹ • w) * corrugatedVisibilityCoefficient R ‖w‖ =
      (‖z‖⁻¹ • z - ‖w‖⁻¹ • w) * corrugatedVisibilityCoefficient R ‖z‖ +
      (‖w‖⁻¹ • w) * (corrugatedVisibilityCoefficient R ‖z‖ - corrugatedVisibilityCoefficient R ‖w‖) := by ring
  rw [he]
  calc
    _ ≤ ‖(‖z‖⁻¹ • z - ‖w‖⁻¹ • w) * corrugatedVisibilityCoefficient R ‖z‖‖ +
        ‖(‖w‖⁻¹ • w) * (corrugatedVisibilityCoefficient R ‖z‖ - corrugatedVisibilityCoefficient R ‖w‖)‖ := norm_add_le _ _
    _ = ‖‖z‖⁻¹ • z - ‖w‖⁻¹ • w‖ +
        ‖corrugatedVisibilityCoefficient R ‖z‖ - corrugatedVisibilityCoefficient R ‖w‖‖ := by
      rw [norm_mul, norm_mul, corrugatedVisibilityCoefficient_norm hR hzp hz,
        norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hwp),
        inv_mul_cancel₀ (ne_of_gt hwp), mul_one, one_mul]
    _ ≤ 2 * ‖z - w‖ / ‖w‖ + 3 * R * |‖z‖ - ‖w‖| / (‖z‖ * ‖w‖) :=
      add_le_add (corrugated_normalize_distance hzne hwne)
        (corrugatedVisibilityCoefficient_distance hR hzp hwp hz hw hqz hqw)
    _ ≤ 2 * ‖z - w‖ / ‖w‖ + 3 * R * ‖z - w‖ / (‖z‖ * ‖w‖) := by
      apply add_le_add le_rfl
      apply div_le_div_of_nonneg_right _ (mul_pos hzp hwp).le
      exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le z w) (by positivity)

theorem corrugatedVisibilityDirection_outer_distance {z w : ℂ}
    (hz : (49 / 100 : ℝ) ≤ ‖z‖) (hw : ‖w‖ = (1 / 2 : ℝ)) :
    ‖corrugatedVisibilityDirection (1 / 4) z - corrugatedVisibilityDirection (1 / 4) w‖ ≤
      8 * ‖z - w‖ := by
  have hzp : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) hz
  have hzw : (1 / 4 : ℝ) < ‖z‖ := lt_of_lt_of_le (by norm_num) hz
  have hww : (1 / 4 : ℝ) < ‖w‖ := by rw [hw]; norm_num
  have hqz := corrugatedVisibilityCoefficient_im_lower (by norm_num : 0 ≤ (1 / 4 : ℝ))
    hzp (show (1 / 4 : ℝ) ≤ (17 / 20) * ‖z‖ by linarith)
  have hqw := corrugatedVisibilityCoefficient_im_lower (by norm_num : 0 ≤ (1 / 4 : ℝ))
    (show 0 < ‖w‖ by rw [hw]; norm_num) (show (1 / 4 : ℝ) ≤ (17 / 20) * ‖w‖ by rw [hw]; norm_num)
  have h := corrugatedVisibilityDirection_distance (by norm_num : 0 ≤ (1 / 4 : ℝ)) hzw hww hqz hqw
  rw [hw] at h
  apply h.trans
  have he : 2 * ‖z - w‖ / (1 / 2 : ℝ) = 4 * ‖z - w‖ := by ring
  rw [he]
  have hfrac : 3 * (1 / 4 : ℝ) * ‖z - w‖ / (‖z‖ * (1 / 2)) ≤ 4 * ‖z - w‖ := by
    apply (div_le_iff₀ (mul_pos hzp (by norm_num))).mpr
    nlinarith [norm_nonneg (z - w)]
  linarith

end
end TightVer401
