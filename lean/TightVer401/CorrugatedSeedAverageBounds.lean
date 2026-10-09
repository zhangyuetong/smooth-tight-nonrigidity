import TightVer401.CorrugatedSeedAverage

namespace TightVer401
noncomputable section
open Set MeasureTheory

theorem corrugatedSeedAverage_add (k : ℝ) {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    corrugatedSeedAverage k (fun x => f x + g x) =
      corrugatedSeedAverage k f + corrugatedSeedAverage k g := by
  unfold corrugatedSeedAverage
  simp only [smul_eq_mul, mul_add]
  exact intervalIntegral.integral_add
    ((corrugatedSeedDensity_continuous k).mul hf |>.intervalIntegrable _ _)
    ((corrugatedSeedDensity_continuous k).mul hg |>.intervalIntegrable _ _)

theorem corrugatedSeedAverage_const_mul (k a : ℝ) (f : ℝ → ℝ) :
    corrugatedSeedAverage k (fun x => a * f x) = a * corrugatedSeedAverage k f := by
  unfold corrugatedSeedAverage
  simp only [smul_eq_mul]
  have he (x : ℝ) : corrugatedSeedDensity k x * (a * f x) = a * (corrugatedSeedDensity k x * f x) := by ring
  simp_rw [he]
  exact intervalIntegral.integral_const_mul a _

theorem corrugatedSeedAverage_const (k a : ℝ) :
    corrugatedSeedAverage k (fun _ => a) = a := by
  unfold corrugatedSeedAverage
  simp only [smul_eq_mul]
  rw [intervalIntegral.integral_mul_const, corrugatedSeedDensity_integral, one_mul]

theorem corrugatedSeedAverage_root_relation (ε k : ℝ) (hk : corrugatedRootIntegral ε k = 0) :
    corrugatedSeedAverage k (fun x => 1 + 2 * Real.cos x) =
      -ε^2 * corrugatedSeedAverage k (fun x => (Real.sin x)^2 * (1 + 2 * Real.cos x)) := by
  have he : (fun x => (1 + ε * Real.sin x)^2 * (1 + 2 * Real.cos x)) =
      (fun x => (1 + 2 * Real.cos x) +
        ((2 * ε) * (Real.sin x * (1 + 2 * Real.cos x)) +
          ε^2 * ((Real.sin x)^2 * (1 + 2 * Real.cos x)))) := by funext x; ring
  have h := corrugatedSeedAverage_root ε k hk
  rw [he, corrugatedSeedAverage_add k (f := fun x => 1 + 2 * Real.cos x)
      (g := fun x => (2 * ε) * (Real.sin x * (1 + 2 * Real.cos x)) +
        ε^2 * ((Real.sin x)^2 * (1 + 2 * Real.cos x))) (by fun_prop) (by fun_prop),
    corrugatedSeedAverage_add k
      (f := fun x => (2 * ε) * (Real.sin x * (1 + 2 * Real.cos x)))
      (g := fun x => ε^2 * ((Real.sin x)^2 * (1 + 2 * Real.cos x))) (by fun_prop) (by fun_prop),
    corrugatedSeedAverage_const_mul, corrugatedSeedAverage_const_mul,
    corrugatedSeedAverage_sin_cos k (fun c => 1 + 2 * c)] at h
  linarith

theorem corrugatedSeedAverage_sin_sq_y_bound (k : ℝ) :
    |corrugatedSeedAverage k (fun x => (Real.sin x)^2 * (1 + 2 * Real.cos x))| ≤ 3 := by
  rw [← Real.norm_eq_abs]
  apply corrugatedSeedAverage_norm_le k (by fun_prop)
  intro x _
  have hs : |Real.sin x| ≤ 1 := Real.abs_sin_le_one x
  have hc : |Real.cos x| ≤ 1 := Real.abs_cos_le_one x
  have hy : |1 + 2 * Real.cos x| ≤ 3 := by
    have h := abs_add_le (1 : ℝ) (2 * Real.cos x)
    simp only [abs_one, abs_mul] at h
    norm_num at h
    linarith
  have hs2 : |Real.sin x| ^ 2 ≤ 1 := by nlinarith [abs_nonneg (Real.sin x)]
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact (mul_le_mul hs2 hy (abs_nonneg _) zero_le_one).trans_eq (by ring)

theorem corrugatedSeedAverage_y_bound (ε k : ℝ) (hk : corrugatedRootIntegral ε k = 0) :
    |corrugatedSeedAverage k (fun x => 1 + 2 * Real.cos x)| ≤ 3 * ε^2 := by
  rw [corrugatedSeedAverage_root_relation ε k hk, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg ε)]
  exact (mul_le_mul_of_nonneg_left (corrugatedSeedAverage_sin_sq_y_bound k) (sq_nonneg ε)).trans_eq (by ring)

theorem corrugatedSeedAverage_cos_bound (ε k : ℝ) (hk : corrugatedRootIntegral ε k = 0) :
    |corrugatedSeedAverage k Real.cos + 1 / 2| ≤ (3 / 2) * ε^2 := by
  have h := corrugatedSeedAverage_y_bound ε k hk
  rw [corrugatedSeedAverage_add k (f := fun _ => 1) (g := fun x => 2 * Real.cos x)
      continuous_const (by fun_prop),
    corrugatedSeedAverage_const, corrugatedSeedAverage_const_mul] at h
  have he : 1 + 2 * corrugatedSeedAverage k Real.cos =
      2 * (corrugatedSeedAverage k Real.cos + 1 / 2) := by ring
  rw [he, abs_mul] at h
  norm_num at h
  linarith

end
end TightVer401
