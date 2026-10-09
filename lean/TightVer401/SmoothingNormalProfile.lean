import TightVer401.MomentControlBump
import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicPrimitive

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff

def smoothingNormalKernel (δ : ℝ) (hδ : 0 < δ) : ℝ → ℝ := normalizedMomentControl 0 δ hδ

def smoothingNormalCDF (δ : ℝ) (hδ : 0 < δ) (t : ℝ) : ℝ :=
  rawPrimitive (smoothingNormalKernel δ hδ) t - rawPrimitive (smoothingNormalKernel δ hδ) (-δ)

def smoothingNormalFirst (δ : ℝ) (hδ : 0 < δ) (t : ℝ) : ℝ :=
  2 * (rawPrimitive (smoothingNormalCDF δ hδ) t - rawPrimitive (smoothingNormalCDF δ hδ) (-δ))

def smoothingNormalProfile (δ : ℝ) (hδ : 0 < δ) (t : ℝ) : ℝ :=
  rawPrimitive (smoothingNormalFirst δ hδ) t - rawPrimitive (smoothingNormalFirst δ hδ) (-δ)

theorem smoothingNormalKernel_contDiff (δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (smoothingNormalKernel δ hδ) := normalizedMomentControl_contDiff 0 δ hδ

theorem smoothingNormalKernel_nonneg (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    0 ≤ smoothingNormalKernel δ hδ t := normalizedMomentControl_nonneg 0 δ hδ t

theorem smoothingNormalKernel_even (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    smoothingNormalKernel δ hδ (-t) = smoothingNormalKernel δ hδ t :=
  (momentControlBump 0 δ hδ).normed_neg t

theorem smoothingNormalKernel_zero (δ : ℝ) (hδ : 0 < δ) {t : ℝ}
    (ht : t ≤ -δ ∨ δ ≤ t) : smoothingNormalKernel δ hδ t = 0 := by
  apply Function.notMem_support.mp
  rw [smoothingNormalKernel, normalizedMomentControl_support]
  simp only [zero_sub, zero_add, mem_Ioo]
  rcases ht with ht | ht <;> intro h <;> linarith [h.1, h.2]

theorem smoothingNormalKernel_mass (δ : ℝ) (hδ : 0 < δ) :
    (∫ t in -δ..δ, smoothingNormalKernel δ hδ t) = 1 := by
  rw [intervalIntegral.integral_eq_integral_of_support_subset]
  · exact normalizedMomentControl_integral 0 δ hδ
  · intro t ht
    change t ∈ Function.support (normalizedMomentControl 0 δ hδ) at ht
    rw [normalizedMomentControl_support] at ht
    simp only [zero_sub, zero_add] at ht
    exact ⟨ht.1, ht.2.le⟩

theorem smoothingNormalCDF_contDiff (δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (smoothingNormalCDF δ hδ) :=
  (rawPrimitive_contDiff (smoothingNormalKernel_contDiff δ hδ)).sub contDiff_const

theorem smoothingNormalCDF_integral (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    smoothingNormalCDF δ hδ t = ∫ u in -δ..t, smoothingNormalKernel δ hδ u :=
  intervalIntegral.integral_interval_sub_left
    ((smoothingNormalKernel_contDiff δ hδ).continuous.intervalIntegrable 0 t)
    ((smoothingNormalKernel_contDiff δ hδ).continuous.intervalIntegrable 0 (-δ))

theorem smoothingNormalCDF_zero (δ : ℝ) (hδ : 0 < δ) {t : ℝ} (ht : t ≤ -δ) :
    smoothingNormalCDF δ hδ t = 0 := by
  rw [smoothingNormalCDF_integral]
  have he : (∫ u in -δ..t, smoothingNormalKernel δ hδ u) = ∫ u in -δ..t, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_ge ht] at hu
    exact smoothingNormalKernel_zero δ hδ (Or.inl hu.2)
  rw [he]
  simp

theorem smoothingNormalCDF_one (δ : ℝ) (hδ : 0 < δ) {t : ℝ} (ht : δ ≤ t) :
    smoothingNormalCDF δ hδ t = 1 := by
  rw [smoothingNormalCDF_integral]
  have he : (∫ u in δ..t, smoothingNormalKernel δ hδ u) = 0 := by
    calc
      _ = ∫ u in δ..t, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le ht] at hu
        exact smoothingNormalKernel_zero δ hδ (Or.inr hu.1)
      _ = 0 := by simp
  have hi := intervalIntegral.integral_add_adjacent_intervals
    ((smoothingNormalKernel_contDiff δ hδ).continuous.intervalIntegrable (μ := volume) (-δ) δ)
    ((smoothingNormalKernel_contDiff δ hδ).continuous.intervalIntegrable (μ := volume) δ t)
  rw [← hi, smoothingNormalKernel_mass, he, add_zero]

theorem smoothingNormalCDF_bounds (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    0 ≤ smoothingNormalCDF δ hδ t ∧ smoothingNormalCDF δ hδ t ≤ 1 := by
  by_cases hl : t ≤ -δ
  · rw [smoothingNormalCDF_zero δ hδ hl]
    constructor <;> norm_num
  by_cases hr : δ ≤ t
  · rw [smoothingNormalCDF_one δ hδ hr]
    constructor <;> norm_num
  have hl' : -δ ≤ t := le_of_lt (lt_of_not_ge hl)
  have hr' : t ≤ δ := le_of_lt (lt_of_not_ge hr)
  rw [smoothingNormalCDF_integral]
  refine ⟨intervalIntegral.integral_nonneg_of_forall hl' (smoothingNormalKernel_nonneg δ hδ), ?_⟩
  have hm := intervalIntegral.integral_mono_interval (a := -δ) (b := t) (c := -δ) (d := δ)
    le_rfl hl' hr' (Eventually.of_forall (smoothingNormalKernel_nonneg δ hδ))
    ((smoothingNormalKernel_contDiff δ hδ).continuous.intervalIntegrable (μ := volume) (-δ) δ)
  exact hm.trans_eq (smoothingNormalKernel_mass δ hδ)

theorem smoothingNormalFirst_contDiff (δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (smoothingNormalFirst δ hδ) :=
  contDiff_const.mul ((rawPrimitive_contDiff (smoothingNormalCDF_contDiff δ hδ)).sub contDiff_const)

theorem smoothingNormalProfile_contDiff (δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (smoothingNormalProfile δ hδ) :=
  (rawPrimitive_contDiff (smoothingNormalFirst_contDiff δ hδ)).sub contDiff_const

theorem smoothingNormalFirst_hasDerivAt (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    HasDerivAt (smoothingNormalFirst δ hδ) (2 * smoothingNormalCDF δ hδ t) t :=
  ((rawPrimitive_hasDerivAt (smoothingNormalCDF_contDiff δ hδ).continuous t).sub_const _).const_mul 2

theorem smoothingNormalProfile_hasDerivAt (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    HasDerivAt (smoothingNormalProfile δ hδ) (smoothingNormalFirst δ hδ t) t :=
  (rawPrimitive_hasDerivAt (smoothingNormalFirst_contDiff δ hδ).continuous t).sub_const _

theorem smoothingNormalProfile_second_deriv (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    deriv (deriv (smoothingNormalProfile δ hδ)) t = 2 * smoothingNormalCDF δ hδ t := by
  have he : deriv (smoothingNormalProfile δ hδ) = smoothingNormalFirst δ hδ := by
    funext u
    exact (smoothingNormalProfile_hasDerivAt δ hδ u).deriv
  rw [he]
  exact (smoothingNormalFirst_hasDerivAt δ hδ t).deriv

theorem smoothingNormalProfile_second_deriv_bounds (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    0 ≤ deriv (deriv (smoothingNormalProfile δ hδ)) t ∧
      deriv (deriv (smoothingNormalProfile δ hδ)) t ≤ 2 := by
  rw [smoothingNormalProfile_second_deriv]
  constructor <;> linarith [(smoothingNormalCDF_bounds δ hδ t).1,
    (smoothingNormalCDF_bounds δ hδ t).2]

end
end TightVer401
