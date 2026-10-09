import TightVer401.CorrugatedSeedAction

namespace TightVer401
noncomputable section

def corrugatedSeedBetaAcceleration (N t : ℝ) : ℂ :=
  let c := Real.cos (N * t)
  let s := Real.sin (N * t)
  let r := corrugatedSeedRadius N t
  let y := 1 + 2 * c
  Complex.exp ((corrugatedSeedPhase N t : ℂ) * Complex.I) *
    (Complex.I * (y : ℂ) * ((c : ℂ) + Complex.I * (r : ℂ) * (y : ℂ)) +
      (-(N * s : ℝ) : ℂ) + Complex.I * (c * y - 2 * N * r * s : ℝ))

theorem corrugatedSeedRadius_hasDerivAt {N : ℝ} (hN : N ≠ 0) (t : ℝ) :
    HasDerivAt (corrugatedSeedRadius N) (Real.cos (N * t)) t := by
  have h := (((hasDerivAt_id t).const_mul N).sin.const_mul (1 / N)).const_add 1
  have h' := h.congr_of_eventuallyEq (f₁ := corrugatedSeedRadius N)
    (Filter.Eventually.of_forall (fun _ => rfl))
  have he : (1 / N) * (Real.cos (N * id t) * (N * 1)) = Real.cos (N * t) := by
    simp only [id_eq, mul_one]
    field_simp
  exact he ▸ h'

theorem corrugatedSeedPhase_hasDerivAt {N : ℝ} (hN : N ≠ 0) (t : ℝ) :
    HasDerivAt (corrugatedSeedPhase N) (1 + 2 * Real.cos (N * t)) t := by
  have h := (hasDerivAt_id t).add
    ((((hasDerivAt_id t).const_mul N).sin).const_mul (2 * (1 / N)))
  have h' := h.congr_of_eventuallyEq (f₁ := corrugatedSeedPhase N)
    (Filter.Eventually.of_forall (fun _ => rfl))
  have he : 1 + 2 * (1 / N) * (Real.cos (N * id t) * (N * 1)) =
      1 + 2 * Real.cos (N * t) := by simp only [id_eq, mul_one]; field_simp
  exact he ▸ h'

theorem corrugatedSeedBetaVelocity_hasDerivAt {N : ℝ} (hN : N ≠ 0) (t : ℝ) :
    HasDerivAt (corrugatedSeedBetaVelocity N) (corrugatedSeedBetaAcceleration N t) t := by
  have hc : HasDerivAt (fun u : ℝ => Real.cos (N * u))
      (-Real.sin (N * t) * N) t := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul N).cos
  have hr := corrugatedSeedRadius_hasDerivAt hN t
  have hy := (hc.const_mul 2).const_add 1
  have hp := ((corrugatedSeedPhase_hasDerivAt hN t).ofReal_comp.mul_const Complex.I).cexp
  have hw := hc.ofReal_comp.add
    (((hr.ofReal_comp.const_mul Complex.I).mul hy.ofReal_comp))
  have hd := hp.mul hw
  have hd' := hd.congr_of_eventuallyEq (f₁ := corrugatedSeedBetaVelocity N)
    (Filter.Eventually.of_forall (fun _ => by
      simp only [corrugatedSeedBetaVelocity, Complex.ofReal_add, Complex.ofReal_mul,
        Complex.ofReal_one, Complex.ofReal_ofNat, Pi.add_apply, Pi.mul_apply]))
  have he : Complex.exp ((corrugatedSeedPhase N t : ℂ) * Complex.I) *
      (((1 + 2 * Real.cos (N * t) : ℝ) : ℂ) * Complex.I) *
      ((Real.cos (N * t) : ℂ) + Complex.I * (corrugatedSeedRadius N t : ℂ) *
        ((1 + 2 * Real.cos (N * t) : ℝ) : ℂ)) +
      Complex.exp ((corrugatedSeedPhase N t : ℂ) * Complex.I) *
      (((-Real.sin (N * t) * N : ℝ) : ℂ) +
        (Complex.I * (Real.cos (N * t) : ℂ) * ((1 + 2 * Real.cos (N * t) : ℝ) : ℂ) +
          Complex.I * (corrugatedSeedRadius N t : ℂ) *
            ((2 * (-Real.sin (N * t) * N) : ℝ) : ℂ))) =
      corrugatedSeedBetaAcceleration N t := by
    simp only [corrugatedSeedBetaAcceleration, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_neg, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  exact he ▸ hd'

theorem corrugatedSeedBetaAcceleration_eq {N : ℝ} (hN : N ≠ 0) :
    deriv (deriv (corrugatedSeedBeta N)) = corrugatedSeedBetaAcceleration N := by
  have hv : deriv (corrugatedSeedBeta N) = corrugatedSeedBetaVelocity N :=
    funext (corrugatedSeedBeta_deriv hN)
  rw [hv]
  exact funext (fun t => (corrugatedSeedBetaVelocity_hasDerivAt hN t).deriv)

theorem corrugatedSeedBeta_curvature_numerator (N t : ℝ) :
    corrugatedSeedPlaneDet (corrugatedSeedBetaVelocity N t) (corrugatedSeedBetaAcceleration N t) =
      N * corrugatedSeedRadius N t * Real.sin (N * t) +
      2 * (Real.cos (N * t)) ^ 2 * (1 + 2 * Real.cos (N * t)) +
      (corrugatedSeedRadius N t) ^ 2 * (1 + 2 * Real.cos (N * t)) ^ 3 := by
  unfold corrugatedSeedBetaVelocity corrugatedSeedBetaAcceleration
  rw [corrugatedSeedPlaneDet_rotate]
  simp only [corrugatedSeedPlaneDet, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.neg_re, Complex.neg_im]
  ring

theorem corrugatedSeedBeta_curvature_at_zero {N : ℝ} (hN : N ≠ 0) :
    corrugatedSeedPlaneDet (deriv (corrugatedSeedBeta N) 0)
      (deriv (deriv (corrugatedSeedBeta N)) 0) = 33 := by
  rw [corrugatedSeedBeta_deriv hN, corrugatedSeedBetaAcceleration_eq hN,
    corrugatedSeedBeta_curvature_numerator]
  norm_num [corrugatedSeedRadius]

theorem corrugatedSeedBeta_curvature_at_half_cell {N : ℝ} (hN : N ≠ 0) :
    corrugatedSeedPlaneDet (deriv (corrugatedSeedBeta N) (Real.pi / N))
      (deriv (deriv (corrugatedSeedBeta N)) (Real.pi / N)) = -3 := by
  rw [corrugatedSeedBeta_deriv hN, corrugatedSeedBetaAcceleration_eq hN,
    corrugatedSeedBeta_curvature_numerator]
  have he : N * (Real.pi / N) = Real.pi := by field_simp
  norm_num [corrugatedSeedRadius, he]

end
end TightVer401
