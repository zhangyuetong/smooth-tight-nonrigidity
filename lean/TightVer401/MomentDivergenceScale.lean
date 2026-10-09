import TightVer401.MomentPeriod
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false

theorem momentDivergence_inv_sqrt_limit :
    Tendsto (fun t : ℝ => (Real.sqrt (1 - t))⁻¹) (𝓝[<] 1) atTop := by
  have hlinear : Tendsto (fun t : ℝ => 1 - t) (𝓝[<] 1) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => 1 - t) := continuous_const.sub continuous_id
    have hd : Tendsto (fun t : ℝ => 1 - t) (𝓝 1) (𝓝 0) := by
      simpa using (hc.continuousAt (x := (1 : ℝ))).tendsto
    exact hd.mono_left inf_le_left
  have hroot : Tendsto (fun t : ℝ => Real.sqrt (1 - t)) (𝓝[<] 1) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa only [Real.sqrt_zero, Function.comp_def] using
        (Real.continuous_sqrt.continuousAt (x := (0 : ℝ))).tendsto.comp hlinear
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact Real.sqrt_pos.mpr (by simpa only [mem_Iio] using sub_pos.mpr ht)
  exact tendsto_inv_nhdsGT_zero.comp hroot

theorem momentDivergence_scale_unbounded {C B : ℝ} (hC : 0 < C) (M : ℝ) :
    ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ M < (Real.sqrt (1 - t))⁻¹ * C - B := by
  let D := |M + B| + C + 1
  have hD : 0 < D := by dsimp [D]; linarith [abs_nonneg (M + B)]
  have hCD : C < D := by dsimp [D]; linarith [abs_nonneg (M + B)]
  let q := C / D
  have hq : 0 < q := div_pos hC hD
  have hq1 : q < 1 := (div_lt_one hD).mpr hCD
  refine ⟨1 - q^2, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith [sq_pos_of_pos hq]
  · have hroot : Real.sqrt (1 - (1 - q^2)) = q := by
      rw [show 1 - (1 - q^2) = q^2 by ring, Real.sqrt_sq hq.le]
    rw [hroot]
    have hscale : q⁻¹ * C = D := by dsimp [q]; field_simp
    rw [hscale]
    dsimp [D]
    linarith [le_abs_self (M + B)]

theorem momentDivergence_plateau_scale {a b g : ℝ → ℝ} {t u v : ℝ}
    (ht : t < 1)
    (hplateau : ∀ r ∈ uIcc u v, a r = (1 - t) * b r) :
    (∫ r in u..v, g r / Real.sqrt (a r)) =
      (Real.sqrt (1 - t))⁻¹ * (∫ r in u..v, g r / Real.sqrt (b r)) := by
  calc
    (∫ r in u..v, g r / Real.sqrt (a r)) =
        ∫ r in u..v, g r / Real.sqrt ((1 - t) * b r) := by
      apply intervalIntegral.integral_congr
      intro r hr
      change g r / Real.sqrt (a r) = g r / Real.sqrt ((1 - t) * b r)
      rw [hplateau r hr]
    _ = _ := by
      rw [show (fun r => g r / Real.sqrt ((1 - t) * b r)) =
          fun r => (Real.sqrt (1 - t))⁻¹ * (g r / Real.sqrt (b r)) by
        funext r
        rw [Real.sqrt_mul (by linarith : 0 ≤ 1 - t)]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring, intervalIntegral.integral_const_mul]

end
end TightVer401
