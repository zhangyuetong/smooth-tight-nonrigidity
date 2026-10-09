import TightVer401.CorrugatedSeedBounds

namespace TightVer401
noncomputable section

def corrugatedSeedLimitingFactor (x : ℝ) : ℂ :=
  (Real.cos x : ℂ) + Complex.I * (1 + 2 * (Real.cos x : ℂ))

def corrugatedSeedLimitingVelocity (N t : ℝ) : ℂ :=
  Complex.exp ((t : ℂ) * Complex.I) * corrugatedSeedLimitingFactor (N * t)

theorem corrugatedSeedLimitingFactor_norm_le (x : ℝ) :
    ‖corrugatedSeedLimitingFactor x‖ ≤ 4 := by
  have hc := Real.abs_cos_le_one x
  have hy : |1 + 2 * Real.cos x| ≤ 3 := by
    calc
      _ ≤ |(1 : ℝ)| + |2 * Real.cos x| := abs_add_le _ _
      _ = 1 + 2 * |Real.cos x| := by simp [abs_mul]
      _ ≤ 3 := by linarith
  calc
    _ ≤ ‖(Real.cos x : ℂ)‖ + ‖Complex.I * ((1 + 2 * Real.cos x : ℝ) : ℂ)‖ := by
      simpa only [corrugatedSeedLimitingFactor, Complex.ofReal_add, Complex.ofReal_mul,
        Complex.ofReal_one, Complex.ofReal_ofNat] using norm_add_le
          (Real.cos x : ℂ) (Complex.I * ((1 + 2 * Real.cos x : ℝ) : ℂ))
    _ = |Real.cos x| + |1 + 2 * Real.cos x| := by
      simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 4 := by linarith

theorem corrugatedSeedLimitingFactor_norm_sq (x : ℝ) :
    ‖corrugatedSeedLimitingFactor x‖ ^ 2 =
      (Real.cos x)^2 + (1 + 2 * Real.cos x)^2 := by
  rw [Complex.sq_norm]
  simp only [corrugatedSeedLimitingFactor, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat]
  ring

theorem corrugatedSeedLimitingFactor_norm_lower (x : ℝ) :
    (1 : ℝ) ≤ 5 * ‖corrugatedSeedLimitingFactor x‖ ^ 2 := by
  rw [corrugatedSeedLimitingFactor_norm_sq]
  nlinarith [sq_nonneg (5 * Real.cos x + 2)]

theorem corrugatedSeedLimitingFactor_ne_zero (x : ℝ) :
    corrugatedSeedLimitingFactor x ≠ 0 := by
  intro h
  have hl := corrugatedSeedLimitingFactor_norm_lower x
  norm_num [h] at hl

theorem corrugatedSeedBetaVelocity_error {N : ℝ} (hN : 0 < N) (t : ℝ) :
    ‖corrugatedSeedBetaVelocity N t - corrugatedSeedLimitingVelocity N t‖ ≤ 11 / N := by
  let A := corrugatedSeedLimitingFactor (N * t)
  let d : ℂ := Complex.I * ((corrugatedSeedRadius N t - 1 : ℝ) : ℂ) *
    ((1 + 2 * Real.cos (N * t) : ℝ) : ℂ)
  have hd : ‖d‖ ≤ 3 / N := by
    have hy : |1 + 2 * Real.cos (N * t)| ≤ 3 := by
      have h := Real.abs_cos_le_one (N * t)
      have ha := abs_add_le (1 : ℝ) (2 * Real.cos (N * t))
      simp only [abs_one, abs_mul] at ha
      norm_num at ha
      linarith
    have he : 0 ≤ 1 / N := by positivity
    dsimp [d]
    simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ (1 / N) * 3 := mul_le_mul (corrugatedSeedRadius_error hN t) hy (abs_nonneg _) he
      _ = 3 / N := by ring
  have he : corrugatedSeedBetaVelocity N t - corrugatedSeedLimitingVelocity N t =
      Complex.exp ((corrugatedSeedPhase N t : ℂ) * Complex.I) * d +
      (Complex.exp ((corrugatedSeedPhase N t : ℂ) * Complex.I) -
        Complex.exp ((t : ℂ) * Complex.I)) * A := by
    simp only [corrugatedSeedBetaVelocity, corrugatedSeedLimitingVelocity, A, d,
      corrugatedSeedLimitingFactor, Complex.ofReal_sub, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  rw [he]
  calc
    _ ≤ ‖Complex.exp ((corrugatedSeedPhase N t : ℂ) * Complex.I) * d‖ +
      ‖(Complex.exp ((corrugatedSeedPhase N t : ℂ) * Complex.I) -
        Complex.exp ((t : ℂ) * Complex.I)) * A‖ := norm_add_le _ _
    _ = ‖d‖ + ‖Complex.exp ((corrugatedSeedPhase N t : ℂ) * Complex.I) -
        Complex.exp ((t : ℂ) * Complex.I)‖ * ‖A‖ := by
      simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    _ ≤ 3 / N + (2 / N) * 4 := by
      apply add_le_add hd
      apply mul_le_mul
        ((corrugated_unit_exponential_lipschitz t _).trans (corrugatedSeedPhase_error hN t))
        (corrugatedSeedLimitingFactor_norm_le _) (norm_nonneg _) (by positivity)
    _ = 11 / N := by ring

end
end TightVer401
