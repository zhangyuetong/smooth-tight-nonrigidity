import TightVer401.CorrugatedSeedVisibilityAngle
import TightVer401.CorrugatedSeedVisibilityAngleAlgebra

namespace TightVer401
noncomputable section
open scoped ContDiff

theorem corrugatedSeedPartnerAngle_exp {N : ℝ} (hN : 10000 ≤ N) (t : ℝ) :
    Complex.exp ((corrugatedSeedPartnerAngle N t : ℂ) * Complex.I) =
      ‖corrugatedSeedPartner N t‖⁻¹ • corrugatedSeedPartner N t := by
  have hz : 0 < ‖corrugatedSeedPartner N t‖ := by
    linarith [(corrugatedSeedPartner_radius_bounds hN t).1]
  have hq : corrugatedSeedPartnerRatio N t ≠ 0 :=
    Complex.slitPlane_ne_zero (corrugatedSeedPartnerRatio_slitPlane hN t)
  have hqn : ‖corrugatedSeedPartnerRatio N t‖ = 2 * ‖corrugatedSeedPartner N t‖ := by
    unfold corrugatedSeedPartnerRatio
    rw [norm_div, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    norm_num
    ring
  have ha : Complex.exp (((corrugatedSeedPartnerRatio N t).arg : ℂ) * Complex.I) =
      corrugatedSeedPartnerRatio N t / (‖corrugatedSeedPartnerRatio N t‖ : ℂ) := by
    apply (eq_div_iff (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hq))).mpr
    rw [mul_comm]
    exact Complex.norm_mul_exp_arg_mul_I _
  unfold corrugatedSeedPartnerAngle
  simp only [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.ofReal_div,
    Complex.ofReal_ofNat]
  rw [Complex.exp_pi_div_two_mul_I, ha, hqn, Complex.real_smul]
  unfold corrugatedSeedPartnerRatio
  have he := Complex.exp_ne_zero ((t : ℂ) * Complex.I)
  have hzn := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  push_cast
  field_simp

theorem corrugatedSeedVisibleAngle_exp {N : ℝ} (hN : 10000 ≤ N) (t : ℝ) :
    Complex.exp ((corrugatedSeedVisibleAngle N t : ℂ) * Complex.I) =
      corrugatedVisibilityDirection (1 / 4) (corrugatedSeedPartner N t) := by
  have hr := (corrugatedSeed_outer_visible hN t).1
  have hz : corrugatedSeedPartner N t ≠ 0 := norm_pos_iff.mp (by linarith)
  unfold corrugatedSeedVisibleAngle
  rw [Complex.ofReal_add, add_mul, Complex.exp_add, corrugatedSeedPartnerAngle_exp hN,
    ← corrugatedVisibilityCoefficient_exp_arccos (by norm_num : 0 ≤ (1 / 4 : ℝ)) hr,
    corrugatedVisibilityDirection_eq hz]

theorem corrugatedSeedPartnerAngle_contDiff {N : ℝ} (hN : 10000 ≤ N) :
    ContDiff ℝ ∞ (corrugatedSeedPartnerAngle N) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  have hs := corrugatedSeedPartnerRatio_slitPlane hN t
  have hl := ((Complex.contDiffAt_log hs).restrict_scalars ℝ).comp t
    (corrugatedSeedPartnerRatio_contDiff N).contDiffAt
  have hi := Complex.imCLM.contDiff.contDiffAt.comp t hl
  have ha : ContDiffAt ℝ ∞ (fun s => (corrugatedSeedPartnerRatio N s).arg) t := by
    change ContDiffAt ℝ ∞ (fun s => (Complex.log (corrugatedSeedPartnerRatio N s)).im) t at hi
    simpa only [Complex.log_im] using hi
  exact (contDiffAt_id.add contDiffAt_const).add ha

theorem corrugatedSeedVisibleAngle_contDiff {N : ℝ} (hN : 10000 ≤ N) :
    ContDiff ℝ ∞ (corrugatedSeedVisibleAngle N) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  have hr := (corrugatedSeed_outer_visible hN t).1
  have hn : 0 < ‖corrugatedSeedPartner N t‖ := by linarith
  have hne : corrugatedSeedPartner N t ≠ 0 := norm_pos_iff.mp hn
  have hd := (corrugatedSeedPartner_contDiff N).contDiffAt.norm ℂ hne
  have hq := (contDiffAt_const (c := (1 / 4 : ℝ))).div hd (ne_of_gt hn)
  have hl : (-1 : ℝ) < (1 / 4) / ‖corrugatedSeedPartner N t‖ := by
    have : 0 < (1 / 4 : ℝ) / ‖corrugatedSeedPartner N t‖ := by positivity
    linarith
  have hu : (1 / 4) / ‖corrugatedSeedPartner N t‖ < (1 : ℝ) := (div_lt_one hn).mpr hr
  have ha := (Real.contDiffAt_arccos (ne_of_gt hl) (ne_of_lt hu)).comp t hq
  exact (corrugatedSeedPartnerAngle_contDiff hN).contDiffAt.add ha

end
end TightVer401
