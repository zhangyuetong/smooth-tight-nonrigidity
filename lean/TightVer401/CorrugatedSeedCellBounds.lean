import TightVer401.CorrugatedSeedCellAverage
import TightVer401.CorrugatedSeedComplexAverage

namespace TightVer401
noncomputable section
open Set MeasureTheory

theorem corrugatedSeedAverage_sub_complex (k : ℝ) {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) :
    corrugatedSeedAverage k (fun x => f x - g x) =
      corrugatedSeedAverage k f - corrugatedSeedAverage k g := by
  unfold corrugatedSeedAverage
  simp only [smul_sub]
  exact intervalIntegral.integral_sub
    (((corrugatedSeedDensity_continuous k).smul hf).intervalIntegrable _ _)
    (((corrugatedSeedDensity_continuous k).smul hg).intervalIntegrable _ _)

theorem corrugatedSeedCellFactor_error {N : ℝ} (hN : 0 < N) {x : ℝ}
    (hx : x ∈ Icc 0 (2 * Real.pi)) :
    ‖corrugatedSeedCellFactor N x - corrugatedSeedLimitingFactor x‖ ≤ 43 / N := by
  let e := 1 / N
  let φ := e * (x + 2 * Real.sin x)
  let d : ℂ := Complex.I * ((e * Real.sin x : ℝ) : ℂ) * ((1 + 2 * Real.cos x : ℝ) : ℂ)
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hφ : |φ| ≤ 10 / N := by
    have hb : |x + 2 * Real.sin x| ≤ 10 := by
      calc
        _ ≤ |x| + |2 * Real.sin x| := abs_add_le _ _
        _ = x + 2 * |Real.sin x| := by rw [abs_of_nonneg hx.1, abs_mul]; norm_num
        _ ≤ 10 := by have h := Real.abs_sin_le_one x; linarith [Real.pi_lt_four, hx.2]
    dsimp [φ]
    rw [abs_mul, abs_of_nonneg he]
    exact (mul_le_mul_of_nonneg_left hb he).trans_eq (by dsimp [e]; ring)
  have hd : ‖d‖ ≤ 3 / N := by
    have hy : |1 + 2 * Real.cos x| ≤ 3 := by
      have h := Real.abs_cos_le_one x
      have ha := abs_add_le (1 : ℝ) (2 * Real.cos x)
      simp only [abs_one, abs_mul] at ha
      norm_num at ha
      linarith
    have hs : |e * Real.sin x| ≤ e := by
      rw [abs_mul, abs_of_nonneg he]
      exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one x) he).trans_eq (mul_one _)
    dsimp [d]
    simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg he]
    have hs' : e * |Real.sin x| ≤ e := by
      exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one x) he).trans_eq (mul_one _)
    exact (mul_le_mul hs' hy (abs_nonneg _) he).trans_eq (by change (1 / N) * 3 = 3 / N; ring)
  have hφexp : ‖Complex.exp ((φ : ℂ) * Complex.I) - 1‖ ≤ 10 / N := by
    have h := corrugated_unit_exponential_lipschitz 0 φ
    simp only [sub_zero] at h
    simpa only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, sub_zero] using h.trans hφ
  have hid : corrugatedSeedCellFactor N x - corrugatedSeedLimitingFactor x =
      Complex.exp ((φ : ℂ) * Complex.I) * d +
      (Complex.exp ((φ : ℂ) * Complex.I) - 1) * corrugatedSeedLimitingFactor x := by
    simp only [corrugatedSeedCellFactor, corrugatedSeedLimitingFactor, φ, e, d,
      Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  rw [hid]
  calc
    _ ≤ ‖Complex.exp ((φ : ℂ) * Complex.I) * d‖ +
      ‖(Complex.exp ((φ : ℂ) * Complex.I) - 1) * corrugatedSeedLimitingFactor x‖ := norm_add_le _ _
    _ = ‖d‖ + ‖Complex.exp ((φ : ℂ) * Complex.I) - 1‖ * ‖corrugatedSeedLimitingFactor x‖ := by
      simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    _ ≤ 3 / N + (10 / N) * 4 := add_le_add hd
      (mul_le_mul hφexp (corrugatedSeedLimitingFactor_norm_le x) (norm_nonneg _) (by positivity))
    _ = 43 / N := by ring

theorem corrugatedSeedCellAverage_error {N : ℝ} (hN : 10 ≤ N) (k : ℝ)
    (hk : corrugatedRootIntegral (1 / N) k = 0) :
    ‖corrugatedSeedAverage k (corrugatedSeedCellFactor N) + (1 / 2 : ℂ)‖ ≤ 44 / N := by
  have hNp : 0 < N := by linarith
  have hdiff : ‖corrugatedSeedAverage k (corrugatedSeedCellFactor N) -
      corrugatedSeedAverage k corrugatedSeedLimitingFactor‖ ≤ 43 / N := by
    rw [← corrugatedSeedAverage_sub_complex k (corrugatedSeedCellFactor_continuous N)
      corrugatedSeedLimitingFactor_continuous]
    exact corrugatedSeedAverage_norm_le k
      ((corrugatedSeedCellFactor_continuous N).sub corrugatedSeedLimitingFactor_continuous)
      (fun x hx => corrugatedSeedCellFactor_error hNp hx)
  have hbase := corrugatedSeedAverage_limiting_bound (1 / N) k hk
  have he : 1 / N ≤ 1 / 10 := (div_le_div_iff₀ hNp (by norm_num)).mpr (by nlinarith)
  have he0 : 0 ≤ 1 / N := by positivity
  have hsmall : (9 / 2 : ℝ) * (1 / N)^2 ≤ 1 / N := by nlinarith
  have hsum := norm_add_le
    (corrugatedSeedAverage k (corrugatedSeedCellFactor N) - corrugatedSeedAverage k corrugatedSeedLimitingFactor)
    (corrugatedSeedAverage k corrugatedSeedLimitingFactor + (1 / 2 : ℂ))
  have hnorm : ‖corrugatedSeedAverage k (corrugatedSeedCellFactor N) + (1 / 2 : ℂ)‖ ≤
      43 / N + (9 / 2 : ℝ) * (1 / N)^2 := by
    have he : corrugatedSeedAverage k (corrugatedSeedCellFactor N) -
        corrugatedSeedAverage k corrugatedSeedLimitingFactor +
        (corrugatedSeedAverage k corrugatedSeedLimitingFactor + (1 / 2 : ℂ)) =
        corrugatedSeedAverage k (corrugatedSeedCellFactor N) + (1 / 2 : ℂ) := by ring
    rw [he] at hsum
    exact hsum.trans (add_le_add hdiff hbase)
  calc
    _ ≤ 43 / N + (9 / 2 : ℝ) * (1 / N)^2 := hnorm
    _ ≤ 43 / N + 1 / N := add_le_add le_rfl hsmall
    _ = 44 / N := by ring

end
end TightVer401
