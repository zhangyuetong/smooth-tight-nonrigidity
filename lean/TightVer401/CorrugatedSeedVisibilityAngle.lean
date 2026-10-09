import TightVer401.CorrugatedSeedVisiblePairs
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

namespace TightVer401
noncomputable section
open scoped ComplexConjugate RealInnerProductSpace ContDiff

def corrugatedSeedPartnerRatio (N t : ℝ) : ℂ :=
  corrugatedSeedPartner N t / (Complex.I / 2 * Complex.exp ((t : ℂ) * Complex.I))

def corrugatedSeedPartnerAngle (N t : ℝ) : ℝ :=
  t + Real.pi / 2 + (corrugatedSeedPartnerRatio N t).arg

def corrugatedSeedVisibleAngle (N t : ℝ) : ℝ :=
  corrugatedSeedPartnerAngle N t + Real.arccos ((1 / 4) / ‖corrugatedSeedPartner N t‖)

theorem corrugatedSeedPartnerRatio_close {N : ℝ} (hN : 10000 ≤ N) (t : ℝ) :
    ‖corrugatedSeedPartnerRatio N t - 1‖ ≤ 200 / N := by
  have hb : Complex.I / 2 * Complex.exp ((t : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (div_ne_zero Complex.I_ne_zero (by norm_num)) (Complex.exp_ne_zero _)
  have he : corrugatedSeedPartnerRatio N t - 1 =
      (corrugatedSeedPartner N t - Complex.I / 2 * Complex.exp ((t : ℂ) * Complex.I)) /
        (Complex.I / 2 * Complex.exp ((t : ℂ) * Complex.I)) := by
    unfold corrugatedSeedPartnerRatio
    field_simp
  rw [he, norm_div, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hn : ‖(Complex.I / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hn]
  have h := corrugatedSeedPartner_uniform_error hN t
  calc
    _ ≤ (100 / N) / (1 / 2) := div_le_div_of_nonneg_right h (by norm_num)
    _ = 200 / N := by ring

theorem corrugatedSeedPartnerRatio_re_pos {N : ℝ} (hN : 10000 ≤ N) (t : ℝ) :
    0 < (corrugatedSeedPartnerRatio N t).re := by
  have he : 200 / N ≤ (1 / 50 : ℝ) :=
    (div_le_div_iff₀ (by linarith : 0 < N) (by norm_num)).mpr (by nlinarith)
  have h := (corrugatedSeedPartnerRatio_close hN t).trans he
  have hr := Complex.abs_re_le_norm (corrugatedSeedPartnerRatio N t - 1)
  simp only [Complex.sub_re, Complex.one_re] at hr
  have ha := le_abs_self (-(corrugatedSeedPartnerRatio N t).re + 1)
  rw [show -(corrugatedSeedPartnerRatio N t).re + 1 =
    -((corrugatedSeedPartnerRatio N t).re - 1) by ring, abs_neg] at ha
  linarith

theorem corrugatedSeedPartnerRatio_slitPlane {N : ℝ} (hN : 10000 ≤ N) (t : ℝ) :
    corrugatedSeedPartnerRatio N t ∈ Complex.slitPlane :=
  Or.inl (corrugatedSeedPartnerRatio_re_pos hN t)

theorem corrugated_arg_hasDerivAt {f : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (hf : HasDerivAt f v t) (hs : f t ∈ Complex.slitPlane) :
    HasDerivAt (fun s => (f s).arg) (v / f t).im t := by
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hf.clog_real hs)
  exact h.congr_of_eventuallyEq (f₁ := fun s => (f s).arg)
    (Filter.Eventually.of_forall (fun s => (Complex.log_im (f s)).symm))

theorem corrugatedSeedPartnerRatio_contDiff (N : ℝ) :
    ContDiff ℝ ∞ (corrugatedSeedPartnerRatio N) := by
  unfold corrugatedSeedPartnerRatio
  have hf := corrugatedSeedPartner_contDiff N
  have hn : ∀ t : ℝ, Complex.I / 2 * Complex.exp ((t : ℂ) * Complex.I) ≠ 0 :=
    fun _ => mul_ne_zero (div_ne_zero Complex.I_ne_zero (by norm_num)) (Complex.exp_ne_zero _)
  have hg : ContDiff ℝ ∞ (fun t : ℝ => Complex.I / 2 * Complex.exp ((t : ℂ) * Complex.I)) := by
    change ContDiff ℝ ∞ (fun t : ℝ => Complex.I / 2 * Complex.exp (Complex.ofRealCLM t * Complex.I))
    fun_prop
  rw [show (fun t : ℝ => corrugatedSeedPartner N t /
      (Complex.I / 2 * Complex.exp ((t : ℂ) * Complex.I))) =
      (fun t : ℝ => corrugatedSeedPartner N t *
        (Complex.I / 2 * Complex.exp ((t : ℂ) * Complex.I))⁻¹) by ext; rw [div_eq_mul_inv]]
  exact hf.mul (hg.inv hn)

theorem corrugatedSeedPartnerAngle_differentiable {N : ℝ} (hN : 10000 ≤ N) :
    Differentiable ℝ (corrugatedSeedPartnerAngle N) := by
  intro t
  have hf := (corrugatedSeedPartnerRatio_contDiff N).differentiable (by simp) t
  have ha := (corrugated_arg_hasDerivAt hf.hasDerivAt
    (corrugatedSeedPartnerRatio_slitPlane hN t)).differentiableAt
  exact ((differentiableAt_id.add_const _).add ha)

theorem corrugatedSeedVisibleAngle_differentiable {N : ℝ} (hN : 10000 ≤ N) :
    Differentiable ℝ (corrugatedSeedVisibleAngle N) := by
  intro t
  have hr : (1 / 4 : ℝ) < ‖corrugatedSeedPartner N t‖ := by
    linarith [(corrugatedSeedPartner_radius_bounds hN t).1]
  have hne : corrugatedSeedPartner N t ≠ 0 := norm_pos_iff.mp (by linarith)
  have hd := ((corrugatedSeedPartner_contDiff N).differentiable (by simp) t).norm ℂ hne
  have hq := (differentiableAt_const (c := (1 / 4 : ℝ))).div hd (ne_of_gt (by linarith))
  have hl : (-1 : ℝ) < (1 / 4) / ‖corrugatedSeedPartner N t‖ := by
    have : 0 < (1 / 4 : ℝ) / ‖corrugatedSeedPartner N t‖ := by positivity
    linarith
  have hu : (1 / 4) / ‖corrugatedSeedPartner N t‖ < (1 : ℝ) :=
    (div_lt_one (by linarith)).mpr hr
  have ha := (Real.hasDerivAt_arccos (ne_of_gt hl) (ne_of_lt hu)).differentiableAt.comp t hq
  exact (corrugatedSeedPartnerAngle_differentiable hN t).add ha

theorem corrugatedSeedPartnerRatio_periodic {N : ℕ} (hN : 2 ≤ N) :
    Function.Periodic (corrugatedSeedPartnerRatio (N : ℝ)) (2 * Real.pi) := by
  intro t
  unfold corrugatedSeedPartnerRatio
  rw [corrugatedSeedPartner_periodic hN t]
  have he : Complex.exp ((((t + 2 * Real.pi : ℝ) : ℂ)) * Complex.I) =
      Complex.exp ((t : ℂ) * Complex.I) := by
    rw [Complex.ofReal_add, add_mul, Complex.exp_add]
    have hp : (((2 * Real.pi : ℝ) : ℂ)) * Complex.I = 2 * Real.pi * Complex.I := by push_cast; rfl
    rw [hp, Complex.exp_two_pi_mul_I, mul_one]
  rw [he]

theorem corrugatedSeedVisibleAngle_shift {N : ℕ} (hN : 2 ≤ N) (t : ℝ) :
    corrugatedSeedVisibleAngle (N : ℝ) (t + 2 * Real.pi) =
      corrugatedSeedVisibleAngle (N : ℝ) t + 2 * Real.pi := by
  unfold corrugatedSeedVisibleAngle corrugatedSeedPartnerAngle
  rw [corrugatedSeedPartnerRatio_periodic hN t, corrugatedSeedPartner_periodic hN t]
  ring

end
end TightVer401
