import TightVer401.SmoothingNormalProfile

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff

theorem smoothingNormalCDF_reflection (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    smoothingNormalCDF δ hδ (-t) = 1 - smoothingNormalCDF δ hδ t := by
  have he : (∫ u in -δ..(-t), smoothingNormalKernel δ hδ u) =
      ∫ u in t..δ, smoothingNormalKernel δ hδ u := by
    calc
      _ = ∫ u in -δ..(-t), smoothingNormalKernel δ hδ (-u) := by
        apply intervalIntegral.integral_congr
        intro u _
        exact (smoothingNormalKernel_even δ hδ u).symm
      _ = _ := by rw [intervalIntegral.integral_comp_neg]; simp
  have hi := intervalIntegral.integral_add_adjacent_intervals
    ((smoothingNormalKernel_contDiff δ hδ).continuous.intervalIntegrable (μ := volume) (-δ) t)
    ((smoothingNormalKernel_contDiff δ hδ).continuous.intervalIntegrable (μ := volume) t δ)
  rw [smoothingNormalKernel_mass] at hi
  rw [smoothingNormalCDF_integral, he, smoothingNormalCDF_integral]
  linarith

theorem smoothingNormalFirst_integral (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    smoothingNormalFirst δ hδ t = 2 * ∫ u in -δ..t, smoothingNormalCDF δ hδ u := by
  unfold smoothingNormalFirst
  rw [show rawPrimitive (smoothingNormalCDF δ hδ) t - rawPrimitive (smoothingNormalCDF δ hδ) (-δ) =
      ∫ u in -δ..t, smoothingNormalCDF δ hδ u from intervalIntegral.integral_interval_sub_left
        ((smoothingNormalCDF_contDiff δ hδ).continuous.intervalIntegrable 0 t)
        ((smoothingNormalCDF_contDiff δ hδ).continuous.intervalIntegrable 0 (-δ))]

theorem smoothingNormalProfile_integral (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    smoothingNormalProfile δ hδ t = ∫ u in -δ..t, smoothingNormalFirst δ hδ u :=
  intervalIntegral.integral_interval_sub_left
    ((smoothingNormalFirst_contDiff δ hδ).continuous.intervalIntegrable 0 t)
    ((smoothingNormalFirst_contDiff δ hδ).continuous.intervalIntegrable 0 (-δ))

theorem smoothingNormalFirst_right_endpoint (δ : ℝ) (hδ : 0 < δ) :
    smoothingNormalFirst δ hδ δ = 2 * δ := by
  have hi : (∫ u in -δ..δ, smoothingNormalCDF δ hδ (-u)) =
      ∫ u in -δ..δ, smoothingNormalCDF δ hδ u := by
    rw [intervalIntegral.integral_comp_neg]
    simp
  have he : (∫ u in -δ..δ, smoothingNormalCDF δ hδ (-u)) =
      2 * δ - ∫ u in -δ..δ, smoothingNormalCDF δ hδ u := by
    calc
      _ = ∫ u in -δ..δ, (1 - smoothingNormalCDF δ hδ u) := by
        apply intervalIntegral.integral_congr
        intro u _
        exact smoothingNormalCDF_reflection δ hδ u
      _ = _ := by
        rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable (-δ) δ)
          ((smoothingNormalCDF_contDiff δ hδ).continuous.intervalIntegrable (-δ) δ)]
        simp
        ring
  rw [smoothingNormalFirst_integral]
  linarith

theorem smoothingNormalFirst_zero (δ : ℝ) (hδ : 0 < δ) {t : ℝ} (ht : t ≤ -δ) :
    smoothingNormalFirst δ hδ t = 0 := by
  rw [smoothingNormalFirst_integral]
  have he : (∫ u in -δ..t, smoothingNormalCDF δ hδ u) = 0 := by
    calc
      _ = ∫ u in -δ..t, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_ge ht] at hu
        exact smoothingNormalCDF_zero δ hδ hu.2
      _ = 0 := by simp
  rw [he, mul_zero]

theorem smoothingNormalFirst_right (δ : ℝ) (hδ : 0 < δ) {t : ℝ} (ht : δ ≤ t) :
    smoothingNormalFirst δ hδ t = 2 * t := by
  have he : (∫ u in δ..t, smoothingNormalCDF δ hδ u) = t - δ := by
    calc
      _ = ∫ u in δ..t, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le ht] at hu
        exact smoothingNormalCDF_one δ hδ hu.1
      _ = _ := by simp
  have hi := intervalIntegral.integral_add_adjacent_intervals
    ((smoothingNormalCDF_contDiff δ hδ).continuous.intervalIntegrable (μ := volume) (-δ) δ)
    ((smoothingNormalCDF_contDiff δ hδ).continuous.intervalIntegrable (μ := volume) δ t)
  have hend := smoothingNormalFirst_right_endpoint δ hδ
  rw [smoothingNormalFirst_integral] at hend ⊢
  rw [← hi, he]
  linarith

theorem smoothingNormalProfile_zero (δ : ℝ) (hδ : 0 < δ) {t : ℝ} (ht : t ≤ -δ) :
    smoothingNormalProfile δ hδ t = 0 := by
  rw [smoothingNormalProfile_integral]
  calc
    _ = ∫ u in -δ..t, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_ge ht] at hu
      exact smoothingNormalFirst_zero δ hδ hu.2
    _ = 0 := by simp

theorem smoothingNormalProfile_right (δ : ℝ) (hδ : 0 < δ) {t : ℝ} (ht : δ ≤ t) :
    smoothingNormalProfile δ hδ t = t^2 + (smoothingNormalProfile δ hδ δ - δ^2) := by
  have he : (∫ u in δ..t, smoothingNormalFirst δ hδ u) = t^2 - δ^2 := by
    calc
      _ = ∫ u in δ..t, (2 * u) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le ht] at hu
        exact smoothingNormalFirst_right δ hδ hu.1
      _ = _ := by
        exact intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun u _ => by simpa using ((hasDerivAt_id u).pow 2))
          ((continuous_const.mul continuous_id).intervalIntegrable δ t)
  have hi := intervalIntegral.integral_add_adjacent_intervals
    ((smoothingNormalFirst_contDiff δ hδ).continuous.intervalIntegrable (μ := volume) (-δ) δ)
    ((smoothingNormalFirst_contDiff δ hδ).continuous.intervalIntegrable (μ := volume) δ t)
  rw [smoothingNormalProfile_integral, ← hi, he, ← smoothingNormalProfile_integral]
  ring

end
end TightVer401
