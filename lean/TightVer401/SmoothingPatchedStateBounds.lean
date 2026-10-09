import TightVer401.SmoothingPatchedDerivatives

namespace TightVer401
noncomputable section

theorem smoothingPatchedProfile_sqrt_state_bounds (δ : ℝ) (hδ : 0 < δ) (hd₁ : δ ≤ 1)
    {B₁ B₂ t : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (ht : |t| ≤ 2*Real.sqrt δ)
    (hζ₁ : |deriv (smoothingNormalStep (Real.sqrt δ)) t| ≤ B₁/Real.sqrt δ)
    (hζ₂ : |deriv (deriv (smoothingNormalStep (Real.sqrt δ))) t| ≤ B₂/(Real.sqrt δ)^2) :
    |smoothingPatchedProfile δ hδ (Real.sqrt δ) t| ≤ 11*δ ∧
    |deriv (smoothingPatchedProfile δ hδ (Real.sqrt δ)) t| ≤
      (8+3*B₁*δ)*Real.sqrt δ ∧
    |deriv (deriv (smoothingPatchedProfile δ hδ (Real.sqrt δ))) t/2 -
      smoothingNormalCDF δ hδ t| ≤ (3*B₂/2)*δ := by
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hs₂ := Real.sq_sqrt hδ.le
  have hdhs : δ ≤ Real.sqrt δ := by nlinarith [sq_nonneg (Real.sqrt δ-δ)]
  have hm : max t 0 ≤ 2*Real.sqrt δ := max_le (abs_le.mp ht).2 (by positivity)
  have hm₀ : 0 ≤ max t 0 := le_max_right _ _
  have hm₂ : (max t 0)^2 ≤ 4*δ := by nlinarith
  have hq := abs_le.mp (smoothingPatchedProfile_uniform_value_error δ hδ (Real.sqrt δ) t)
  have hid : δ^2*(B₁/Real.sqrt δ)=B₁*δ*Real.sqrt δ := by
    have hr : δ/Real.sqrt δ=Real.sqrt δ :=
      (div_eq_iff (ne_of_gt hs)).mpr (by nlinarith [hs₂])
    calc
      _ = B₁*δ*(δ/Real.sqrt δ) := by ring
      _ = _ := by rw [hr]
  have hfirst := abs_le.mp (smoothingPatchedProfile_first_error δ hδ hs hB₁ hζ₁)
  rw [show 3*δ^2*(B₁/Real.sqrt δ)=3*(δ^2*(B₁/Real.sqrt δ)) by ring,hid] at hfirst
  refine ⟨abs_le.mpr ⟨by nlinarith [sq_nonneg δ],by nlinarith [sq_nonneg δ]⟩,
    abs_le.mpr ⟨by nlinarith,by nlinarith⟩,?_⟩
  rw [smoothingPatchedProfile_second]
  have he : (2*smoothingNormalCDF δ hδ t -
      (smoothingNormalProfile δ hδ δ-δ^2)*deriv (deriv (smoothingNormalStep (Real.sqrt δ))) t)/2 -
      smoothingNormalCDF δ hδ t =
      -((smoothingNormalProfile δ hδ δ-δ^2)*deriv (deriv (smoothingNormalStep (Real.sqrt δ))) t)/2 := by ring
  rw [he,abs_div,abs_neg,abs_mul]
  rw [abs_of_pos (by norm_num : (0 : ℝ)<2)]
  have hb := mul_le_mul (smoothingNormalProfile_offset_bound δ hδ) hζ₂ (abs_nonneg _) (by positivity)
  apply (div_le_div_of_nonneg_right hb (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
  rw [hs₂]
  field_simp

end
end TightVer401
