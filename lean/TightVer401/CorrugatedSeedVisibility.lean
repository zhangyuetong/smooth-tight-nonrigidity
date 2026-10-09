import TightVer401.CorrugatedSeedNormalize

namespace TightVer401
noncomputable section

def corrugatedVisibilityCoefficient (R r : ℝ) : ℂ :=
  ((R / r : ℝ) : ℂ) + ((Real.sqrt (r^2 - R^2) / r : ℝ) : ℂ) * Complex.I

def corrugatedVisibilityDirection (R : ℝ) (z : ℂ) : ℂ :=
  ((R : ℂ) + (Real.sqrt (‖z‖^2 - R^2) : ℂ) * Complex.I) * z / ((‖z‖^2 : ℝ) : ℂ)

theorem corrugatedVisibilityCoefficient_components {R r : ℝ} (hR : 0 ≤ R) (hr : 0 < r)
    (hRr : R < r) :
    0 ≤ R / r ∧ R / r ≤ 1 ∧ 0 ≤ Real.sqrt (r^2 - R^2) / r ∧
      (R / r)^2 + (Real.sqrt (r^2 - R^2) / r)^2 = 1 := by
  have hsq : 0 ≤ r^2 - R^2 := by nlinarith
  refine ⟨div_nonneg hR hr.le, (div_le_one hr).mpr hRr.le,
    div_nonneg (Real.sqrt_nonneg _) hr.le, ?_⟩
  rw [div_pow, div_pow, Real.sq_sqrt hsq]
  field_simp
  ring

theorem corrugatedVisibilityCoefficient_norm {R r : ℝ} (hR : 0 ≤ R) (hr : 0 < r) (hRr : R < r) :
    ‖corrugatedVisibilityCoefficient R r‖ = 1 := by
  have h := (corrugatedVisibilityCoefficient_components hR hr hRr).2.2.2
  have he : ‖corrugatedVisibilityCoefficient R r‖^2 = 1 := by
    rw [Complex.sq_norm]
    simpa only [corrugatedVisibilityCoefficient, Complex.normSq_apply, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, zero_add, add_zero,
      one_mul, mul_one, pow_two] using h
  nlinarith [norm_nonneg (corrugatedVisibilityCoefficient R r)]

theorem corrugatedVisibilityDirection_eq {R : ℝ} {z : ℂ} (hz : z ≠ 0) :
    corrugatedVisibilityDirection R z = (‖z‖⁻¹ • z) * corrugatedVisibilityCoefficient R ‖z‖ := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  unfold corrugatedVisibilityDirection corrugatedVisibilityCoefficient
  simp only [Complex.real_smul,
    Complex.ofReal_div, Complex.ofReal_inv, Complex.ofReal_pow]
  field_simp

theorem corrugatedVisibilityDirection_norm {R : ℝ} (hR : 0 ≤ R) {z : ℂ} (hz : R < ‖z‖) :
    ‖corrugatedVisibilityDirection R z‖ = 1 := by
  have hzp : 0 < ‖z‖ := hR.trans_lt hz
  have hzne : z ≠ 0 := norm_pos_iff.mp hzp
  rw [corrugatedVisibilityDirection_eq hzne, norm_mul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hzp), inv_mul_cancel₀ (ne_of_gt hzp),
    corrugatedVisibilityCoefficient_norm hR hzp hz, one_mul]

theorem corrugatedVisibilityCoefficient_im_lower {R r : ℝ} (hR : 0 ≤ R) (hr : 0 < r)
    (hRr : R ≤ (17 / 20) * r) : (1 / 2 : ℝ) ≤ Real.sqrt (r^2 - R^2) / r := by
  have hsq : 0 ≤ r^2 - R^2 := by nlinarith
  have hs := Real.sq_sqrt hsq
  have hsn := Real.sqrt_nonneg (r^2 - R^2)
  apply (le_div_iff₀ hr).mpr
  nlinarith

theorem corrugated_upper_semicircle_distance {p q s u : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hq : 1 / 2 ≤ q) (hu : 1 / 2 ≤ u)
    (hpq : p^2 + q^2 = 1) (hsu : s^2 + u^2 = 1) :
    ‖((p : ℂ) + (q : ℂ) * Complex.I) - ((s : ℂ) + (u : ℂ) * Complex.I)‖ ≤ 3 * |p - s| := by
  have hqu : |q - u| ≤ 2 * |p - s| := by
    rcases le_total u q with h | h
    · have hps : p ≤ s := by nlinarith
      rw [abs_of_nonneg (by linarith : 0 ≤ q - u), abs_of_nonpos (by linarith : p - s ≤ 0)]
      nlinarith [mul_nonneg (sub_nonneg.mpr h) (by linarith : 0 ≤ q + u - 1),
        mul_nonneg (sub_nonneg.mpr hps) (by linarith : 0 ≤ 2 - p - s)]
    · have hsp : s ≤ p := by nlinarith
      rw [abs_of_nonpos (by linarith : q - u ≤ 0), abs_of_nonneg (by linarith : 0 ≤ p - s)]
      nlinarith [mul_nonneg (sub_nonneg.mpr h) (by linarith : 0 ≤ q + u - 1),
        mul_nonneg (sub_nonneg.mpr hsp) (by linarith : 0 ≤ 2 - p - s)]
  have hnorm := Complex.norm_le_abs_re_add_abs_im
    (((p : ℂ) + (q : ℂ) * Complex.I) - ((s : ℂ) + (u : ℂ) * Complex.I))
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_add, add_zero, sub_zero, mul_one] at hnorm
  linarith

end
end TightVer401
