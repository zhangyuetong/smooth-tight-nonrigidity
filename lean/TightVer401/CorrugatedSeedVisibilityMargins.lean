import TightVer401.CorrugatedSeedVisibility

namespace TightVer401
noncomputable section
open scoped RealInnerProductSpace

def corrugatedOuterLimitingDirection (t : ℝ) : ℂ :=
  Complex.exp ((t : ℂ) * Complex.I) * (((-Real.sqrt 3 / 2 : ℝ) : ℂ) + Complex.I / 2)

def corrugatedInnerLimitingDirection (t : ℝ) : ℂ :=
  Complex.exp ((t : ℂ) * Complex.I) * ((-4 / 5 : ℂ) + (3 / 5 : ℂ) * Complex.I)

theorem corrugated_complex_inner (z w : ℂ) : inner ℝ z w = z.re * w.re + z.im * w.im := by
  rw [Complex.inner]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem corrugated_complex_inner_rotate (θ : ℝ) (z w : ℂ) :
    inner ℝ (Complex.exp ((θ : ℂ) * Complex.I) * z)
      (Complex.exp ((θ : ℂ) * Complex.I) * w) = inner ℝ z w := by
  have he (u z w : ℂ) : inner ℝ (u * z) (u * w) =
      (u.re^2 + u.im^2) * inner ℝ z w := by
    simp only [corrugated_complex_inner, Complex.mul_re, Complex.mul_im]
    ring
  rw [he, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Real.cos_sq_add_sin_sq, one_mul]

theorem corrugatedSeedLimitingFactor_norm_upper (x : ℝ) :
    ‖corrugatedSeedLimitingFactor x‖ < 16 / 5 := by
  have hc : (Real.cos x)^2 ≤ 1 := by nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (Real.sin x)]
  have hy : |1 + 2 * Real.cos x| ≤ 3 := by
    have ha := abs_add_le (1 : ℝ) (2 * Real.cos x)
    simp only [abs_one, abs_mul] at ha
    norm_num at ha
    linarith [Real.abs_cos_le_one x]
  have hy2 : (1 + 2 * Real.cos x)^2 ≤ 9 := by nlinarith [abs_nonneg (1 + 2 * Real.cos x), sq_abs (1 + 2 * Real.cos x)]
  have hsq := corrugatedSeedLimitingFactor_norm_sq x
  nlinarith [norm_nonneg (corrugatedSeedLimitingFactor x)]

theorem corrugatedOuterLimitingDirection_inner (N t : ℝ) :
    inner ℝ (corrugatedSeedLimitingUnitTangent N t) (corrugatedOuterLimitingDirection t) =
      (1 + (2 - Real.sqrt 3) * Real.cos (N * t)) /
        (2 * ‖corrugatedSeedLimitingFactor (N * t)‖) := by
  unfold corrugatedSeedLimitingUnitTangent
  rw [corrugatedSeedLimitingVelocity_norm, real_inner_smul_left]
  unfold corrugatedSeedLimitingVelocity corrugatedOuterLimitingDirection
  rw [corrugated_complex_inner_rotate, corrugated_complex_inner]
  simp only [corrugatedSeedLimitingFactor, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_apply]
  ring

theorem corrugatedOuterLimitingDirection_margin (N t : ℝ) :
    (1 / 10 : ℝ) < inner ℝ (corrugatedSeedLimitingUnitTangent N t) (corrugatedOuterLimitingDirection t) := by
  rw [corrugatedOuterLimitingDirection_inner]
  have hp : 0 < ‖corrugatedSeedLimitingFactor (N * t)‖ :=
    norm_pos_iff.mpr (corrugatedSeedLimitingFactor_ne_zero _)
  apply (lt_div_iff₀ (mul_pos (by norm_num) hp)).mpr
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hsn := Real.sqrt_nonneg (3 : ℝ)
  have hslo : (17 / 10 : ℝ) < Real.sqrt 3 := by nlinarith
  have hshi : Real.sqrt 3 < 2 := by nlinarith
  have hc := Real.neg_one_le_cos (N * t)
  have hmul := mul_nonneg (sub_nonneg.mpr hshi.le) (by linarith : 0 ≤ Real.cos (N * t) + 1)
  have hu := corrugatedSeedLimitingFactor_norm_upper (N * t)
  nlinarith

theorem corrugatedInnerLimitingDirection_inner (N t : ℝ) :
    inner ℝ (corrugatedSeedLimitingUnitTangent N t) (corrugatedInnerLimitingDirection t) =
      (3 + 2 * Real.cos (N * t)) / (5 * ‖corrugatedSeedLimitingFactor (N * t)‖) := by
  unfold corrugatedSeedLimitingUnitTangent
  rw [corrugatedSeedLimitingVelocity_norm, real_inner_smul_left]
  unfold corrugatedSeedLimitingVelocity corrugatedInnerLimitingDirection
  rw [corrugated_complex_inner_rotate, corrugated_complex_inner]
  simp only [corrugatedSeedLimitingFactor, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.neg_re, Complex.neg_im, Complex.normSq_apply]
  ring

theorem corrugatedInnerLimitingDirection_margin (N t : ℝ) :
    (1 / 16 : ℝ) < inner ℝ (corrugatedSeedLimitingUnitTangent N t) (corrugatedInnerLimitingDirection t) := by
  rw [corrugatedInnerLimitingDirection_inner]
  have hp : 0 < ‖corrugatedSeedLimitingFactor (N * t)‖ :=
    norm_pos_iff.mpr (corrugatedSeedLimitingFactor_ne_zero _)
  apply (lt_div_iff₀ (mul_pos (by norm_num) hp)).mpr
  have hc := Real.neg_one_le_cos (N * t)
  have hu := corrugatedSeedLimitingFactor_norm_upper (N * t)
  nlinarith

end
end TightVer401
