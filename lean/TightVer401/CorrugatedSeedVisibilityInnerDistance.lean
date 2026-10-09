import TightVer401.CorrugatedSeedVisibilityLipschitz

namespace TightVer401
noncomputable section
open scoped ComplexConjugate

def corrugatedReflectedVisibilityDirection (R : ℝ) (z : ℂ) : ℂ :=
  -conj (corrugatedVisibilityDirection R (conj z))

theorem corrugatedReflectedVisibilityDirection_norm {R : ℝ} (hR : 0 ≤ R) {z : ℂ} (hz : R < ‖z‖) :
    ‖corrugatedReflectedVisibilityDirection R z‖ = 1 := by
  unfold corrugatedReflectedVisibilityDirection
  rw [norm_neg, Complex.norm_conj]
  exact corrugatedVisibilityDirection_norm hR (by simpa only [Complex.norm_conj] using hz)

theorem corrugatedReflectedVisibilityDirection_eq (R : ℝ) (z : ℂ) :
    corrugatedReflectedVisibilityDirection R z =
      ((-R : ℝ) + (Real.sqrt (‖z‖^2 - R^2) : ℂ) * Complex.I) * z / ((‖z‖^2 : ℝ) : ℂ) := by
  simp only [corrugatedReflectedVisibilityDirection, corrugatedVisibilityDirection,
    Complex.norm_conj, map_div₀, map_mul, map_add, Complex.conj_ofReal, Complex.conj_I,
    Complex.conj_conj, Complex.ofReal_neg]
  ring

theorem corrugatedReflectedVisibilityDirection_inner_distance {z w : ℂ}
    (hz : (99 / 100 : ℝ) ≤ ‖z‖) (hw : ‖w‖ = 1) :
    ‖corrugatedReflectedVisibilityDirection (4 / 5) z -
      corrugatedReflectedVisibilityDirection (4 / 5) w‖ ≤ 5 * ‖z - w‖ := by
  have hzp : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) hz
  have hzw : (4 / 5 : ℝ) < ‖z‖ := lt_of_lt_of_le (by norm_num) hz
  have hww : (4 / 5 : ℝ) < ‖w‖ := by rw [hw]; norm_num
  have hqz := corrugatedVisibilityCoefficient_im_lower (by norm_num : 0 ≤ (4 / 5 : ℝ))
    hzp (show (4 / 5 : ℝ) ≤ (17 / 20) * ‖z‖ by linarith)
  have hqw := corrugatedVisibilityCoefficient_im_lower (by norm_num : 0 ≤ (4 / 5 : ℝ))
    (show 0 < ‖w‖ by rw [hw]; norm_num) (show (4 / 5 : ℝ) ≤ (17 / 20) * ‖w‖ by rw [hw]; norm_num)
  have h := corrugatedVisibilityDirection_distance (z := conj z) (w := conj w)
    (by norm_num : 0 ≤ (4 / 5 : ℝ))
    (by simpa only [Complex.norm_conj] using hzw)
    (by simpa only [Complex.norm_conj] using hww)
    (by simpa only [Complex.norm_conj] using hqz)
    (by simpa only [Complex.norm_conj] using hqw)
  have hleft : ‖corrugatedReflectedVisibilityDirection (4 / 5) z -
      corrugatedReflectedVisibilityDirection (4 / 5) w‖ =
      ‖corrugatedVisibilityDirection (4 / 5) (conj z) -
        corrugatedVisibilityDirection (4 / 5) (conj w)‖ := by
    unfold corrugatedReflectedVisibilityDirection
    rw [neg_sub_neg, ← map_sub, Complex.norm_conj, norm_sub_rev]
  have hdiff : ‖conj z - conj w‖ = ‖z - w‖ := by rw [← map_sub, Complex.norm_conj]
  rw [hleft]
  simp only [Complex.norm_conj, hdiff] at h
  apply h.trans
  simp only [hw, mul_one, div_one]
  have hfrac : 3 * (4 / 5 : ℝ) * ‖z - w‖ / ‖z‖ ≤ 3 * ‖z - w‖ := by
    apply (div_le_iff₀ hzp).mpr
    nlinarith [norm_nonneg (z - w)]
  linarith

end
end TightVer401
