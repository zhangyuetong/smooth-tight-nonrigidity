import TightVer401.CorrugatedSeedCurve

namespace TightVer401
noncomputable section
open Set

theorem corrugated_unit_exponential_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I))
      (Complex.exp ((t : ℂ) * Complex.I) * Complex.I) t := by
  have h := (((hasDerivAt_id t).ofReal_comp).mul_const Complex.I).cexp
  have h' := h.congr_of_eventuallyEq
    (f₁ := fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I))
    (Filter.Eventually.of_forall (fun _ => rfl))
  have he : Complex.exp ((id t : ℂ) * Complex.I) * ((1 : ℂ) * Complex.I) =
      Complex.exp ((t : ℂ) * Complex.I) * Complex.I := by simp only [id_eq, one_mul]
  exact he ▸ h'

theorem corrugated_unit_exponential_lipschitz (s t : ℝ) :
    ‖Complex.exp ((t : ℂ) * Complex.I) - Complex.exp ((s : ℂ) * Complex.I)‖ ≤ |t - s| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (s := univ)
    (C := 1) (f := fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I))
    (fun x _ => (corrugated_unit_exponential_hasDerivAt x).differentiableAt)
    (fun x _ => by
      rw [(corrugated_unit_exponential_hasDerivAt x).deriv]
      simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_I, mul_one]
      rfl)
    convex_univ (mem_univ s) (mem_univ t)
  simpa only [one_mul, Real.norm_eq_abs] using h

theorem corrugatedSeedRadius_error {N : ℝ} (hN : 0 < N) (t : ℝ) :
    |corrugatedSeedRadius N t - 1| ≤ 1 / N := by
  have he : 0 < 1 / N := by positivity
  have hs := Real.abs_sin_le_one (N * t)
  simp only [corrugatedSeedRadius, add_sub_cancel_left, abs_mul, abs_of_pos he]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hs he.le

theorem corrugatedSeedPhase_error {N : ℝ} (hN : 0 < N) (t : ℝ) :
    |corrugatedSeedPhase N t - t| ≤ 2 / N := by
  have he : 0 < 2 * (1 / N) := by positivity
  have hs := Real.abs_sin_le_one (N * t)
  simp only [corrugatedSeedPhase, add_sub_cancel_left, abs_mul, abs_of_pos he]
  have h := mul_le_mul_of_nonneg_left hs he.le
  simpa only [mul_one, mul_one_div] using h

theorem corrugatedSeedBeta_error {N : ℝ} (hN : 0 < N) (t : ℝ) :
    ‖corrugatedSeedBeta N t - Complex.exp ((t : ℂ) * Complex.I)‖ ≤ 3 / N := by
  have he : corrugatedSeedBeta N t - Complex.exp ((t : ℂ) * Complex.I) =
      ((corrugatedSeedRadius N t - 1 : ℝ) : ℂ) *
        Complex.exp ((corrugatedSeedPhase N t : ℂ) * Complex.I) +
      (Complex.exp ((corrugatedSeedPhase N t : ℂ) * Complex.I) -
        Complex.exp ((t : ℂ) * Complex.I)) := by
    simp only [corrugatedSeedBeta, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  rw [he]
  calc
    _ ≤ ‖((corrugatedSeedRadius N t - 1 : ℝ) : ℂ) *
          Complex.exp ((corrugatedSeedPhase N t : ℂ) * Complex.I)‖ +
        ‖Complex.exp ((corrugatedSeedPhase N t : ℂ) * Complex.I) -
          Complex.exp ((t : ℂ) * Complex.I)‖ := norm_add_le _ _
    _ = |corrugatedSeedRadius N t - 1| +
        ‖Complex.exp ((corrugatedSeedPhase N t : ℂ) * Complex.I) -
          Complex.exp ((t : ℂ) * Complex.I)‖ := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 1 / N + |corrugatedSeedPhase N t - t| :=
      add_le_add (corrugatedSeedRadius_error hN t)
        (corrugated_unit_exponential_lipschitz t (corrugatedSeedPhase N t))
    _ ≤ 1 / N + 2 / N := add_le_add le_rfl (corrugatedSeedPhase_error hN t)
    _ = 3 / N := by ring

end
end TightVer401
