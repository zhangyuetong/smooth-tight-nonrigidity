import TightVer401.CorrugatedSeedVisibilityMargins
import TightVer401.CorrugatedSeedVisibilityInnerDistance

namespace TightVer401
noncomputable section

theorem corrugatedVisibilityDirection_rotate (R : ℝ) {u : ℂ} (hu : ‖u‖ = 1) (z : ℂ) :
    corrugatedVisibilityDirection R (u * z) = u * corrugatedVisibilityDirection R z := by
  simp only [corrugatedVisibilityDirection, norm_mul, hu, one_mul]
  ring

theorem corrugatedReflectedVisibilityDirection_rotate (R : ℝ) {u : ℂ} (hu : ‖u‖ = 1) (z : ℂ) :
    corrugatedReflectedVisibilityDirection R (u * z) = u * corrugatedReflectedVisibilityDirection R z := by
  simp only [corrugatedReflectedVisibilityDirection_eq, norm_mul, hu, one_mul]
  ring

theorem corrugatedVisibilityDirection_outer_reference (t : ℝ) :
    corrugatedVisibilityDirection (1 / 4)
      (Complex.I / 2 * Complex.exp ((t : ℂ) * Complex.I)) = corrugatedOuterLimitingDirection t := by
  have hhalf : ‖Complex.I / 2‖ = (1 / 2 : ℝ) := by norm_num
  have hs : Real.sqrt ((1 / 2 : ℝ)^2 - (1 / 4)^2) = Real.sqrt 3 / 4 := by
    rw [show ((1 / 2 : ℝ)^2 - (1 / 4)^2) = 3 / 16 by norm_num,
      Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  rw [mul_comm (Complex.I / 2), corrugatedVisibilityDirection_rotate (1 / 4)
    (Complex.norm_exp_ofReal_mul_I t)]
  unfold corrugatedOuterLimitingDirection
  congr 1
  simp only [corrugatedVisibilityDirection, hhalf, hs]
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
      Complex.normSq_ofNat, Complex.re_ofNat, Complex.im_ofNat] <;> ring

theorem corrugatedReflectedVisibilityDirection_inner_reference (t : ℝ) :
    corrugatedReflectedVisibilityDirection (4 / 5) (Complex.exp ((t : ℂ) * Complex.I)) =
      corrugatedInnerLimitingDirection t := by
  have hs : Real.sqrt ((1 : ℝ)^2 - (4 / 5)^2) = (3 / 5 : ℝ) := by
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ (1 : ℝ)^2 - (4 / 5)^2)
    have hp := Real.sqrt_nonneg ((1 : ℝ)^2 - (4 / 5)^2)
    nlinarith
  have h := corrugatedReflectedVisibilityDirection_rotate (4 / 5)
    (Complex.norm_exp_ofReal_mul_I t) (1 : ℂ)
  rw [mul_one] at h
  rw [h]
  unfold corrugatedInnerLimitingDirection
  congr 1
  simp only [corrugatedReflectedVisibilityDirection_eq, norm_one, hs]
  norm_num

end
end TightVer401
