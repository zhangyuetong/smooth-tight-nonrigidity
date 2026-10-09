import TightVer401.CorrugatedRootNormalization
import TightVer401.CorrugatedRootParameter
import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicPrimitive

namespace TightVer401
noncomputable section
open Set MeasureTheory
open scoped ContDiff

def corrugatedSeedRadius (N t : ℝ) : ℝ := 1 + (1 / N) * Real.sin (N * t)

def corrugatedSeedPhase (N t : ℝ) : ℝ := t + 2 * (1 / N) * Real.sin (N * t)

def corrugatedSeedBeta (N t : ℝ) : ℂ :=
  (corrugatedSeedRadius N t : ℂ) * Complex.exp ((corrugatedSeedPhase N t : ℂ) * Complex.I)

def corrugatedSeedBetaVelocity (N t : ℝ) : ℂ :=
  Complex.exp ((corrugatedSeedPhase N t : ℂ) * Complex.I) *
    ((Real.cos (N * t) : ℂ) + Complex.I * (corrugatedSeedRadius N t : ℂ) *
      (1 + 2 * (Real.cos (N * t) : ℂ)))

def corrugatedSeedCell (N : ℝ) : ℝ := 2 * Real.pi / N

def corrugatedSeedRotation (N : ℝ) : ℂ :=
  Complex.exp ((corrugatedSeedCell N : ℂ) * Complex.I)

theorem corrugatedSeedRadius_pos {N : ℝ} (hN : 1 < N) (t : ℝ) :
    0 < corrugatedSeedRadius N t := by
  have he : 0 < 1 / N := by positivity
  have he1 : 1 / N < 1 := (div_lt_one (by linarith)).mpr hN
  have hs := Real.neg_one_le_sin (N * t)
  have hm := mul_le_mul_of_nonneg_left hs he.le
  dsimp [corrugatedSeedRadius]
  linarith

theorem corrugatedSeedBeta_contDiff (N : ℝ) : ContDiff ℝ ∞ (corrugatedSeedBeta N) := by
  unfold corrugatedSeedBeta corrugatedSeedPhase corrugatedSeedRadius
  change ContDiff ℝ ∞ (fun t => Complex.ofRealCLM (1 + (1 / N) * Real.sin (N * t)) *
    Complex.exp (Complex.ofRealCLM (t + 2 * (1 / N) * Real.sin (N * t)) * Complex.I))
  fun_prop

theorem corrugatedSeedBetaVelocity_contDiff (N : ℝ) :
    ContDiff ℝ ∞ (corrugatedSeedBetaVelocity N) := by
  unfold corrugatedSeedBetaVelocity corrugatedSeedPhase corrugatedSeedRadius
  change ContDiff ℝ ∞ (fun t =>
    Complex.exp (Complex.ofRealCLM (t + 2 * (1 / N) * Real.sin (N * t)) * Complex.I) *
    (Complex.ofRealCLM (Real.cos (N * t)) + Complex.I *
      Complex.ofRealCLM (1 + (1 / N) * Real.sin (N * t)) *
      (1 + 2 * Complex.ofRealCLM (Real.cos (N * t)))))
  fun_prop

theorem corrugatedSeedBeta_hasDerivAt {N : ℝ} (hN : N ≠ 0) (t : ℝ) :
    HasDerivAt (corrugatedSeedBeta N) (corrugatedSeedBetaVelocity N t) t := by
  have hs := ((hasDerivAt_id t).const_mul N).sin
  have hr : HasDerivAt (corrugatedSeedRadius N) (Real.cos (N * t)) t := by
    have h := (hs.const_mul (1 / N)).const_add 1
    have he : (1 / N) * (Real.cos (N * t) * N) = Real.cos (N * t) := by
      field_simp
    have h' := h.congr_of_eventuallyEq (f₁ := corrugatedSeedRadius N)
      (Filter.Eventually.of_forall (fun _ => rfl))
    have hd : (1 / N) * (Real.cos (N * id t) * (N * 1)) = Real.cos (N * t) := by
      simpa only [id_eq, mul_one] using he
    exact hd ▸ h'
  have hp : HasDerivAt (corrugatedSeedPhase N) (1 + 2 * Real.cos (N * t)) t := by
    have h := (hasDerivAt_id t).add (hs.const_mul (2 * (1 / N)))
    have he : 1 + 2 * (1 / N) * (Real.cos (N * t) * N) =
        1 + 2 * Real.cos (N * t) := by field_simp
    have h' := h.congr_of_eventuallyEq (f₁ := corrugatedSeedPhase N)
      (Filter.Eventually.of_forall (fun _ => rfl))
    have hd : 1 + 2 * (1 / N) * (Real.cos (N * id t) * (N * 1)) =
        1 + 2 * Real.cos (N * t) := by simpa only [id_eq, mul_one] using he
    exact hd ▸ h'
  have h := hr.ofReal_comp.mul ((hp.ofReal_comp.mul_const Complex.I).cexp)
  have he : (Real.cos (N * t) : ℂ) *
      Complex.exp ((corrugatedSeedPhase N t : ℂ) * Complex.I) +
      (corrugatedSeedRadius N t : ℂ) *
      (Complex.exp ((corrugatedSeedPhase N t : ℂ) * Complex.I) *
        (((1 + 2 * Real.cos (N * t) : ℝ) : ℂ) * Complex.I)) =
      corrugatedSeedBetaVelocity N t := by
    simp only [corrugatedSeedBetaVelocity, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  have h' := h.congr_of_eventuallyEq (f₁ := corrugatedSeedBeta N)
    (Filter.Eventually.of_forall (fun _ => rfl))
  exact he ▸ h'

theorem corrugatedSeedBeta_deriv {N : ℝ} (hN : N ≠ 0) (t : ℝ) :
    deriv (corrugatedSeedBeta N) t = corrugatedSeedBetaVelocity N t :=
  (corrugatedSeedBeta_hasDerivAt hN t).deriv

theorem corrugatedSeedBeta_norm {N : ℝ} (hN : 1 < N) (t : ℝ) :
    ‖corrugatedSeedBeta N t‖ = corrugatedSeedRadius N t := by
  simp [corrugatedSeedBeta, Complex.norm_exp_ofReal_mul_I,
    abs_of_pos (corrugatedSeedRadius_pos hN t)]

theorem corrugatedSeedBetaVelocity_ne_zero {N : ℝ} (hN : 1 < N) (t : ℝ) :
    corrugatedSeedBetaVelocity N t ≠ 0 := by
  apply mul_ne_zero (Complex.exp_ne_zero _)
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
    Complex.re_ofNat, Complex.im_ofNat, zero_mul, mul_zero, zero_add, add_zero,
    one_mul, sub_zero, zero_sub] at hre him
  have hc : Real.cos (N * t) = 0 := by simpa using hre
  have hz : corrugatedSeedRadius N t = 0 := by simpa [hc] using him
  exact (ne_of_gt (corrugatedSeedRadius_pos hN t)) hz

theorem corrugatedSeedRadius_cell {N : ℝ} (hN : N ≠ 0) (t : ℝ) :
    corrugatedSeedRadius N (t + corrugatedSeedCell N) = corrugatedSeedRadius N t := by
  have he : N * (t + corrugatedSeedCell N) = N * t + 2 * Real.pi := by
    unfold corrugatedSeedCell
    field_simp
  simp [corrugatedSeedRadius, he]

theorem corrugatedSeedPhase_cell {N : ℝ} (hN : N ≠ 0) (t : ℝ) :
    corrugatedSeedPhase N (t + corrugatedSeedCell N) =
      corrugatedSeedPhase N t + corrugatedSeedCell N := by
  have he : N * (t + corrugatedSeedCell N) = N * t + 2 * Real.pi := by
    unfold corrugatedSeedCell
    field_simp
  simp only [corrugatedSeedPhase, he, Real.sin_add_two_pi]
  ring

theorem corrugatedSeedBeta_cell {N : ℝ} (hN : N ≠ 0) (t : ℝ) :
    corrugatedSeedBeta N (t + corrugatedSeedCell N) =
      corrugatedSeedRotation N * corrugatedSeedBeta N t := by
  simp only [corrugatedSeedBeta, corrugatedSeedRadius_cell hN,
    corrugatedSeedPhase_cell hN, Complex.ofReal_add, add_mul, Complex.exp_add,
    corrugatedSeedRotation]
  ring

theorem corrugatedSeedBetaVelocity_cell {N : ℝ} (hN : N ≠ 0) (t : ℝ) :
    corrugatedSeedBetaVelocity N (t + corrugatedSeedCell N) =
      corrugatedSeedRotation N * corrugatedSeedBetaVelocity N t := by
  have he : N * (t + corrugatedSeedCell N) = N * t + 2 * Real.pi := by
    unfold corrugatedSeedCell
    field_simp
  simp only [corrugatedSeedBetaVelocity, corrugatedSeedRadius_cell hN,
    corrugatedSeedPhase_cell hN, he, Real.cos_add_two_pi, Complex.ofReal_add,
    add_mul, Complex.exp_add, corrugatedSeedRotation]
  ring

end
end TightVer401
