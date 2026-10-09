import TightVer401.CorrugatedSeedVisibilityAngle
import TightVer401.CorrugatedSeedVisibilityAngleAlgebra

namespace TightVer401
noncomputable section
open scoped ContDiff RealInnerProductSpace

theorem corrugatedSeedPartnerAngle_hasDerivAt {N : ℝ} (hN : 10000 ≤ N) (t : ℝ) :
    HasDerivAt (corrugatedSeedPartnerAngle N)
      (deriv (corrugatedSeedPartner N) t / corrugatedSeedPartner N t).im t := by
  let z := corrugatedSeedPartner N t
  let v := deriv (corrugatedSeedPartner N) t
  let b := Complex.I / 2 * Complex.exp ((t : ℂ) * Complex.I)
  have hbne : b ≠ 0 := mul_ne_zero (div_ne_zero Complex.I_ne_zero (by norm_num))
    (Complex.exp_ne_zero _)
  have hzne : z ≠ 0 := norm_pos_iff.mp (by
    change 0 < ‖corrugatedSeedPartner N t‖
    linarith [(corrugatedSeedPartner_radius_bounds hN t).1])
  have hf : HasDerivAt (corrugatedSeedPartner N) v t :=
    ((corrugatedSeedPartner_contDiff N).differentiable (by simp) t).hasDerivAt
  have hb₀ := (corrugated_unit_exponential_hasDerivAt t).const_mul (Complex.I / 2)
  have hb : HasDerivAt (fun s : ℝ => Complex.I / 2 * Complex.exp ((s : ℂ) * Complex.I))
      (b * Complex.I) t := by
    have he : Complex.I / 2 * (Complex.exp ((t : ℂ) * Complex.I) * Complex.I) = b * Complex.I := by
      dsimp [b]; ring
    exact he ▸ hb₀
  have hbi := (hasFDerivAt_inv' (𝕜 := ℝ) hbne).comp_hasDerivAt t hb
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply] at hbi
  have hq₀ := hf.mul hbi
  have hq := hq₀.congr_of_eventuallyEq (f₁ := corrugatedSeedPartnerRatio N)
    (Filter.Eventually.of_forall (fun s => by
      change corrugatedSeedPartner N s /
          (Complex.I / 2 * Complex.exp ((s : ℂ) * Complex.I)) = _
      rw [div_eq_mul_inv]
      rfl))
  have ha := corrugated_arg_hasDerivAt hq (corrugatedSeedPartnerRatio_slitPlane hN t)
  have hθ := ((hasDerivAt_id t).add_const (Real.pi / 2)).add ha
  have he : (v * b⁻¹ + z * -(b⁻¹ * (b * Complex.I) * b⁻¹)) /
      corrugatedSeedPartnerRatio N t = v / z - Complex.I := by
    change _ / (z / b) = _
    field_simp
    ring
  change HasDerivAt (corrugatedSeedPartnerAngle N)
    (1 + ((v * b⁻¹ + z * -(b⁻¹ * (b * Complex.I) * b⁻¹)) /
      corrugatedSeedPartnerRatio N t).im) t at hθ
  rw [he, Complex.sub_im, Complex.I_im] at hθ
  have hcoeff : 1 + ((v / z).im - 1) = (v / z).im := by ring
  rw [hcoeff] at hθ
  exact hθ

theorem corrugatedSeedVisibleAngle_hasDerivAt {N : ℝ} (hN : 10000 ≤ N) (t : ℝ) :
    HasDerivAt (corrugatedSeedVisibleAngle N)
      (inner ℝ (deriv (corrugatedSeedPartner N) t)
        (corrugatedVisibilityDirection (1 / 4) (corrugatedSeedPartner N t)) /
          Real.sqrt (‖corrugatedSeedPartner N t‖^2 - (1 / 4)^2)) t := by
  have hf := ((corrugatedSeedPartner_contDiff N).differentiable (by simp) t).hasDerivAt
  have hr : (1 / 4 : ℝ) < ‖corrugatedSeedPartner N t‖ :=
    (corrugatedSeed_outer_visible hN t).1
  have h := (corrugatedSeedPartnerAngle_hasDerivAt hN t).add
    (corrugated_visibility_arccos_hasDerivAt hf (by norm_num : 0 ≤ (1 / 4 : ℝ)) hr)
  rw [corrugated_visibility_inner_formula (by norm_num : 0 ≤ (1 / 4 : ℝ)) hr]
  exact h

theorem corrugatedSeedVisibleAngle_deriv_pos {N : ℝ} (hN : 10000 ≤ N) (t : ℝ) :
    0 < deriv (corrugatedSeedVisibleAngle N) t := by
  rw [(corrugatedSeedVisibleAngle_hasDerivAt hN t).deriv]
  apply div_pos (corrugatedSeed_outer_visible hN t).2.2
  apply Real.sqrt_pos.mpr
  have hr := (corrugatedSeed_outer_visible hN t).1
  nlinarith

end
end TightVer401
