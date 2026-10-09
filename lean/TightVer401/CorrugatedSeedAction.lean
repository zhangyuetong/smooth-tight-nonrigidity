import TightVer401.CorrugatedSeedClosure

namespace TightVer401
noncomputable section
open Set MeasureTheory

def corrugatedSeedPlaneDet (z w : ℂ) : ℝ := z.re * w.im - z.im * w.re

theorem corrugatedSeedPlaneDet_rotate (θ : ℝ) (z w : ℂ) :
    corrugatedSeedPlaneDet (Complex.exp ((θ : ℂ) * Complex.I) * z)
      (Complex.exp ((θ : ℂ) * Complex.I) * w) = corrugatedSeedPlaneDet z w := by
  have he (u z w : ℂ) : corrugatedSeedPlaneDet (u * z) (u * w) =
      (u.re ^ 2 + u.im ^ 2) * corrugatedSeedPlaneDet z w := by
    simp only [corrugatedSeedPlaneDet, Complex.mul_re, Complex.mul_im]
    ring
  rw [he, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  rw [Real.cos_sq_add_sin_sq, one_mul]

theorem corrugatedSeedPlaneDet_real_mul (a : ℝ) (z w : ℂ) :
    corrugatedSeedPlaneDet z ((a : ℂ) * w) = a * corrugatedSeedPlaneDet z w := by
  simp only [corrugatedSeedPlaneDet, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem corrugatedSeedBeta_tangent_det (N t : ℝ) :
    corrugatedSeedPlaneDet (corrugatedSeedBeta N t) (corrugatedSeedBetaVelocity N t) =
      (corrugatedSeedRadius N t) ^ 2 * (1 + 2 * Real.cos (N * t)) := by
  unfold corrugatedSeedBeta corrugatedSeedBetaVelocity
  rw [mul_comm (corrugatedSeedRadius N t : ℂ), corrugatedSeedPlaneDet_rotate]
  simp only [corrugatedSeedPlaneDet, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat]
  ring

theorem corrugatedSeedDelta_action_integrand (k N t : ℝ) :
    corrugatedSeedPlaneDet (corrugatedSeedBeta N t) (deriv (corrugatedSeedDelta k N) t) =
      (corrugatedSeedNormalization k)⁻¹ *
        (corrugatedWeight (1 / N) k (N * t) * (1 + 2 * Real.cos (N * t))) := by
  rw [corrugatedSeedDelta_deriv]
  unfold corrugatedSeedDeltaVelocity
  rw [corrugatedSeedPlaneDet_real_mul, corrugatedSeedBeta_tangent_det]
  simp only [corrugatedSeedMultiplier, corrugatedWeight, corrugatedSeedRadius]
  ring

theorem corrugatedSeedDelta_action_cell {N : ℝ} (hN : 1 < N) (k : ℝ)
    (hk : corrugatedRootIntegral (1 / N) k = 0) :
    (∫ t in 0..corrugatedSeedCell N,
      corrugatedSeedPlaneDet (corrugatedSeedBeta N t) (deriv (corrugatedSeedDelta k N) t)) = 0 := by
  have hz : N ≠ 0 := ne_of_gt (by linarith)
  have he : N * corrugatedSeedCell N = 2 * Real.pi := by
    unfold corrugatedSeedCell
    field_simp
  simp_rw [corrugatedSeedDelta_action_integrand]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_mul_left
    (fun x => corrugatedWeight (1 / N) k x * (1 + 2 * Real.cos x)) hz]
  simp only [mul_zero, he]
  change (corrugatedSeedNormalization k)⁻¹ * (N⁻¹ • corrugatedRootIntegral (1 / N) k) = 0
  rw [hk]
  simp

theorem corrugatedSeedPartner_action_cell {N : ℝ} (hN : 1 < N) :
    (∫ t in 0..corrugatedSeedCell N,
      corrugatedSeedPlaneDet (corrugatedSeedBeta N t) (deriv (corrugatedSeedPartner N) t)) = 0 :=
  corrugatedSeedDelta_action_cell hN _ (corrugatedSeedRoot_spec hN)

theorem corrugatedSeedPartner_action {N : ℕ} (hN : 2 ≤ N) :
    (∫ t in 0..(2 * Real.pi),
      corrugatedSeedPlaneDet (corrugatedSeedBeta (N : ℝ) t)
        (deriv (corrugatedSeedPartner (N : ℝ)) t)) = 0 := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hz : (N : ℝ) ≠ 0 := ne_of_gt (by linarith)
  let f : ℝ → ℝ := fun t => corrugatedSeedPlaneDet (corrugatedSeedBeta (N : ℝ) t)
    (deriv (corrugatedSeedPartner (N : ℝ)) t)
  have hf : Continuous f := by
    have he : f = fun t => (corrugatedSeedNormalization (corrugatedSeedRoot (N : ℝ)))⁻¹ *
      (corrugatedWeight (1 / (N : ℝ)) (corrugatedSeedRoot (N : ℝ)) ((N : ℝ) * t) *
        (1 + 2 * Real.cos ((N : ℝ) * t))) :=
      funext (corrugatedSeedDelta_action_integrand _ _)
    rw [he]
    unfold corrugatedWeight
    fun_prop
  have hp : Function.Periodic f (corrugatedSeedCell (N : ℝ)) := by
    intro t
    have he : (N : ℝ) * (t + corrugatedSeedCell (N : ℝ)) = (N : ℝ) * t + 2 * Real.pi := by
      unfold corrugatedSeedCell
      field_simp
    dsimp [f, corrugatedSeedPartner]
    simp only [corrugatedSeedDelta_action_integrand, corrugatedWeight, he,
      Real.sin_add_two_pi, Real.cos_add_two_pi]
  have hi := hp.intervalIntegral_add_zsmul_eq (N : ℤ) 0
    (fun a b => hf.intervalIntegrable a b)
  have he : ((N : ℤ) • corrugatedSeedCell (N : ℝ)) = 2 * Real.pi := by
    simp only [zsmul_eq_mul, Int.cast_natCast, corrugatedSeedCell]
    field_simp
  dsimp only [f] at hi
  simpa only [zero_add, he, corrugatedSeedPartner_action_cell hNr, smul_zero] using hi

end
end TightVer401
