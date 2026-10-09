import TightVer401.CorrugatedSeedAverageBounds
import TightVer401.CorrugatedSeedTangentBounds

namespace TightVer401
noncomputable section
open MeasureTheory

theorem corrugatedSeedAverage_map {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (k : ℝ) (L : E →L[ℝ] F) {f : ℝ → E} (hf : Continuous f) :
    corrugatedSeedAverage k (fun x => L (f x)) = L (corrugatedSeedAverage k f) := by
  unfold corrugatedSeedAverage
  have he (x : ℝ) : corrugatedSeedDensity k x • L (f x) = L (corrugatedSeedDensity k x • f x) :=
    (L.map_smul _ _).symm
  simp_rw [he]
  exact L.intervalIntegral_comp_comm
    (((corrugatedSeedDensity_continuous k).smul hf).intervalIntegrable _ _)

theorem corrugatedSeedLimitingFactor_continuous : Continuous corrugatedSeedLimitingFactor := by
  unfold corrugatedSeedLimitingFactor
  fun_prop

theorem corrugatedSeedAverage_limiting_re (k : ℝ) :
    (corrugatedSeedAverage k corrugatedSeedLimitingFactor).re = corrugatedSeedAverage k Real.cos := by
  have he : (fun x => Complex.reCLM (corrugatedSeedLimitingFactor x)) = Real.cos := by
    funext x
    simp only [corrugatedSeedLimitingFactor, Complex.reCLM_apply, Complex.add_re,
      Complex.mul_re, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, Complex.re_ofNat,
      Complex.im_ofNat, mul_zero, zero_mul, sub_zero, add_zero]
  have h := corrugatedSeedAverage_map k Complex.reCLM corrugatedSeedLimitingFactor_continuous
  rw [he] at h
  exact h.symm

theorem corrugatedSeedAverage_limiting_im (k : ℝ) :
    (corrugatedSeedAverage k corrugatedSeedLimitingFactor).im =
      corrugatedSeedAverage k (fun x => 1 + 2 * Real.cos x) := by
  have he : (fun x => Complex.imCLM (corrugatedSeedLimitingFactor x)) =
      (fun x => 1 + 2 * Real.cos x) := by
    funext x
    simp only [corrugatedSeedLimitingFactor, Complex.imCLM_apply, Complex.add_re,
      Complex.mul_re, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, Complex.re_ofNat,
      Complex.im_ofNat, mul_zero, zero_mul, sub_zero, add_zero, zero_add, one_mul]
  have h := corrugatedSeedAverage_map k Complex.imCLM corrugatedSeedLimitingFactor_continuous
  rw [he] at h
  exact h.symm

theorem corrugatedSeedAverage_limiting_bound (ε k : ℝ) (hk : corrugatedRootIntegral ε k = 0) :
    ‖corrugatedSeedAverage k corrugatedSeedLimitingFactor + (1 / 2 : ℂ)‖ ≤ (9 / 2) * ε^2 := by
  calc
    _ ≤ |(corrugatedSeedAverage k corrugatedSeedLimitingFactor + (1 / 2 : ℂ)).re| +
      |(corrugatedSeedAverage k corrugatedSeedLimitingFactor + (1 / 2 : ℂ)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |corrugatedSeedAverage k Real.cos + 1 / 2| +
      |corrugatedSeedAverage k (fun x => 1 + 2 * Real.cos x)| := by
        simp only [Complex.add_re, Complex.add_im, corrugatedSeedAverage_limiting_re,
          corrugatedSeedAverage_limiting_im]
        norm_num
    _ ≤ (3 / 2) * ε^2 + 3 * ε^2 := add_le_add
      (corrugatedSeedAverage_cos_bound ε k hk) (corrugatedSeedAverage_y_bound ε k hk)
    _ = (9 / 2) * ε^2 := by ring

end
end TightVer401
