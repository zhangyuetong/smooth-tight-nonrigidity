import TightVer401.SmoothingNormalProfileGerms

namespace TightVer401
noncomputable section
open Set MeasureTheory
open scoped ContDiff

theorem smoothingNormalFirst_bounds (δ : ℝ) (hδ : 0 < δ) {t : ℝ} (ht : -δ ≤ t) :
    0 ≤ smoothingNormalFirst δ hδ t ∧ smoothingNormalFirst δ hδ t ≤ 2 * (t + δ) := by
  rw [smoothingNormalFirst_integral]
  have hn := intervalIntegral.integral_nonneg_of_forall (μ := volume) ht
    (fun u => (smoothingNormalCDF_bounds δ hδ u).1)
  have hu := intervalIntegral.integral_mono_on ht
    ((smoothingNormalCDF_contDiff δ hδ).continuous.intervalIntegrable (μ := volume) (-δ) t)
    ((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).intervalIntegrable (μ := volume) (-δ) t)
    (fun u _ => (smoothingNormalCDF_bounds δ hδ u).2)
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hu
  constructor <;> linarith

theorem smoothingNormalProfile_bounds (δ : ℝ) (hδ : 0 < δ) {t : ℝ} (ht : -δ ≤ t) :
    0 ≤ smoothingNormalProfile δ hδ t ∧ smoothingNormalProfile δ hδ t ≤ (t + δ)^2 := by
  rw [smoothingNormalProfile_integral]
  have hn := intervalIntegral.integral_nonneg (μ := volume) ht
    (fun u hu => (smoothingNormalFirst_bounds δ hδ hu.1).1)
  have hu := intervalIntegral.integral_mono_on ht
    ((smoothingNormalFirst_contDiff δ hδ).continuous.intervalIntegrable (μ := volume) (-δ) t)
    (((continuous_const.mul (continuous_id.add continuous_const)) :
      Continuous (fun u : ℝ => 2 * (u + δ))).intervalIntegrable (μ := volume) (-δ) t)
    (fun u hu => (smoothingNormalFirst_bounds δ hδ hu.1).2)
  have hi : (∫ u in -δ..t, 2 * (u + δ)) = (t + δ)^2 := by
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => by simpa using ((hasDerivAt_id u).add_const δ).pow 2)
      (((continuous_const.mul (continuous_id.add continuous_const)) :
        Continuous (fun u : ℝ => 2 * (u + δ))).intervalIntegrable (-δ) t)
    simpa using he
  exact ⟨hn, hu.trans_eq hi⟩

theorem smoothingNormalProfile_offset_bound (δ : ℝ) (hδ : 0 < δ) :
    |smoothingNormalProfile δ hδ δ - δ^2| ≤ 3 * δ^2 := by
  have h := smoothingNormalProfile_bounds δ hδ (show -δ ≤ δ by linarith)
  apply abs_le.mpr
  constructor <;> nlinarith [h.1, h.2, sq_nonneg δ]

theorem smoothingNormalProfile_uniform_value_error (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    |smoothingNormalProfile δ hδ t - (max t 0)^2| ≤ 4 * δ^2 := by
  by_cases hl : t ≤ -δ
  · rw [smoothingNormalProfile_zero δ hδ hl, max_eq_right (by linarith : t ≤ 0)]
    simp
    positivity
  by_cases hr : δ ≤ t
  · rw [smoothingNormalProfile_right δ hδ hr, max_eq_left (by linarith : 0 ≤ t)]
    have he : t^2 + (smoothingNormalProfile δ hδ δ - δ^2) - t^2 =
      smoothingNormalProfile δ hδ δ - δ^2 := by ring
    rw [he]
    exact (smoothingNormalProfile_offset_bound δ hδ).trans (by nlinarith [sq_nonneg δ])
  have ht : -δ ≤ t := le_of_lt (lt_of_not_ge hl)
  have ht' : t ≤ δ := le_of_lt (lt_of_not_ge hr)
  have hb := smoothingNormalProfile_bounds δ hδ ht
  have hm0 : 0 ≤ max t 0 := le_max_right _ _
  have hm : max t 0 ≤ δ := max_le ht' hδ.le
  have hs : (max t 0)^2 ≤ δ^2 := by nlinarith
  have hq : smoothingNormalProfile δ hδ t ≤ 4 * δ^2 := by nlinarith [hb.2]
  apply abs_le.mpr
  constructor <;> nlinarith [hb.1, sq_nonneg (max t 0), sq_nonneg δ]

theorem smoothingNormalProfile_uniform_first_error (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    |deriv (smoothingNormalProfile δ hδ) t - 2 * max t 0| ≤ 4 * δ := by
  rw [(smoothingNormalProfile_hasDerivAt δ hδ t).deriv]
  by_cases hl : t ≤ -δ
  · rw [smoothingNormalFirst_zero δ hδ hl, max_eq_right (by linarith : t ≤ 0)]
    simp
    linarith
  by_cases hr : δ ≤ t
  · rw [smoothingNormalFirst_right δ hδ hr, max_eq_left (by linarith : 0 ≤ t)]
    simp
    linarith
  have hb := smoothingNormalFirst_bounds δ hδ (le_of_lt (lt_of_not_ge hl))
  have hm0 : 0 ≤ max t 0 := le_max_right _ _
  have hm : max t 0 ≤ δ := max_le (le_of_lt (lt_of_not_ge hr)) hδ.le
  apply abs_le.mpr
  constructor <;> linarith [hb.1, hb.2, le_of_lt (lt_of_not_ge hr)]

end
end TightVer401
