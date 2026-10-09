import TightVer401.CorrugatedSeedClosure

namespace TightVer401
noncomputable section
open Set MeasureTheory

def corrugatedSeedDensity (k x : ℝ) : ℝ :=
  (corrugatedCosMoment 0 0 k)⁻¹ * Real.exp (-k * Real.cos x)

def corrugatedSeedAverage {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℝ) (f : ℝ → E) : E := ∫ x in 0..(2 * Real.pi), corrugatedSeedDensity k x • f x

theorem corrugatedSeedDensity_continuous (k : ℝ) : Continuous (corrugatedSeedDensity k) := by
  unfold corrugatedSeedDensity
  fun_prop

theorem corrugatedSeedDensity_pos (k x : ℝ) : 0 < corrugatedSeedDensity k x :=
  mul_pos (inv_pos.mpr (corrugatedCosMoment_zero_pos (ε := 0) (by norm_num) k))
    (Real.exp_pos _)

theorem corrugatedSeedDensity_integral (k : ℝ) :
    (∫ x in 0..(2 * Real.pi), corrugatedSeedDensity k x) = 1 := by
  unfold corrugatedSeedDensity
  rw [intervalIntegral.integral_const_mul]
  have he : (∫ x in 0..(2 * Real.pi), Real.exp (-k * Real.cos x)) =
      corrugatedCosMoment 0 0 k := by simp [corrugatedCosMoment, corrugatedWeight]
  rw [he, inv_mul_cancel₀ (ne_of_gt (corrugatedCosMoment_zero_pos (ε := 0) (by norm_num) k))]

theorem corrugatedSeedAverage_norm_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (k : ℝ) {f : ℝ → E} (hf : Continuous f)
    {C : ℝ} (hbound : ∀ x ∈ Icc 0 (2 * Real.pi), ‖f x‖ ≤ C) :
    ‖corrugatedSeedAverage k f‖ ≤ C := by
  have hab : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hd := corrugatedSeedDensity_continuous k
  have hb : IntervalIntegrable (fun x => corrugatedSeedDensity k x * C) volume 0 (2 * Real.pi) :=
    (hd.mul continuous_const).intervalIntegrable 0 (2 * Real.pi)
  calc
    _ ≤ ∫ x in 0..(2 * Real.pi), ‖corrugatedSeedDensity k x • f x‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ x in 0..(2 * Real.pi), corrugatedSeedDensity k x * C := by
      apply intervalIntegral.integral_mono_on hab
        ((hd.smul hf).norm.intervalIntegrable 0 (2 * Real.pi)) hb
      intro x hx
      change ‖corrugatedSeedDensity k x • f x‖ ≤ _
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (corrugatedSeedDensity_pos k x)]
      exact mul_le_mul_of_nonneg_left (hbound x hx) (corrugatedSeedDensity_pos k x).le
    _ = C := by
      rw [intervalIntegral.integral_mul_const, corrugatedSeedDensity_integral, one_mul]

theorem corrugated_odd_interval_integral {f : ℝ → ℝ}
    (hodd : ∀ x, f (2 * Real.pi - x) = -f x) :
    (∫ x in 0..(2 * Real.pi), f x) = 0 := by
  have he := intervalIntegral.integral_comp_sub_left (a := 0) (b := 2 * Real.pi) f (2 * Real.pi)
  simp only [sub_self, sub_zero] at he
  simp_rw [hodd] at he
  rw [intervalIntegral.integral_neg] at he
  linarith

theorem corrugatedSeedAverage_sin_cos (k : ℝ) (g : ℝ → ℝ) :
    corrugatedSeedAverage k (fun x => Real.sin x * g (Real.cos x)) = 0 := by
  apply corrugated_odd_interval_integral
  intro x
  simp only [corrugatedSeedDensity, Real.cos_two_pi_sub, Real.sin_two_pi_sub, smul_eq_mul]
  ring

theorem corrugatedSeedAverage_root (ε k : ℝ) (hk : corrugatedRootIntegral ε k = 0) :
    corrugatedSeedAverage k (fun x => (1 + ε * Real.sin x)^2 * (1 + 2 * Real.cos x)) = 0 := by
  unfold corrugatedSeedAverage corrugatedSeedDensity
  simp only [smul_eq_mul]
  have he (x : ℝ) : (corrugatedCosMoment 0 0 k)⁻¹ * Real.exp (-k * Real.cos x) *
      ((1 + ε * Real.sin x)^2 * (1 + 2 * Real.cos x)) =
      (corrugatedCosMoment 0 0 k)⁻¹ *
        (corrugatedWeight ε k x * (1 + 2 * Real.cos x)) := by
    unfold corrugatedWeight
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  change (corrugatedCosMoment 0 0 k)⁻¹ * corrugatedRootIntegral ε k = 0
  rw [hk, mul_zero]

end
end TightVer401
