import TightVer401.CorrugatedSeedCellBounds
import TightVer401.CorrugatedSeedQuotientBounds

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.ClosedSurfaceR4.PeriodicPrimitive

theorem corrugatedSeedDelta_initial_bound {N : ℝ} (hN : 10000 ≤ N) (k : ℝ)
    (hk : corrugatedRootIntegral (1 / N) k = 0) :
    ‖corrugatedSeedDelta k N 0 - Complex.I / 2‖ ≤ 53 / N := by
  have hNp : 0 < N := by linarith
  rw [corrugatedSeedDelta_initial_average (ne_of_gt hNp)]
  let Q := corrugatedSeedCellQuotient N
  let A := corrugatedSeedAverage k (corrugatedSeedCellFactor N)
  have hQ := corrugatedSeedCellQuotient_bounds hN
  have hA := corrugatedSeedCellAverage_error (show 10 ≤ N by linarith) k hk
  have he : Q * A - Complex.I / 2 = Q * (A + (1 / 2 : ℂ)) - (Q + Complex.I) * (1 / 2 : ℂ) := by ring
  change ‖Q * A - Complex.I / 2‖ ≤ _
  rw [he]
  calc
    _ ≤ ‖Q * (A + (1 / 2 : ℂ))‖ + ‖(Q + Complex.I) * (1 / 2 : ℂ)‖ := norm_sub_le _ _
    _ = ‖Q‖ * ‖A + (1 / 2 : ℂ)‖ + ‖Q + Complex.I‖ * (1 / 2 : ℝ) := by
      simp only [norm_mul]
      norm_num
    _ ≤ (11 / 10) * (44 / N) + (9 / N) * (1 / 2) := add_le_add
      (mul_le_mul hQ.1 hA (norm_nonneg _) (by norm_num))
      (mul_le_mul_of_nonneg_right hQ.2 (by norm_num))
    _ ≤ 53 / N := by
      apply (le_div_iff₀ hNp).mpr
      field_simp
      norm_num

theorem corrugatedSeedBetaVelocity_norm_le {N : ℝ} (hN : 11 ≤ N) (t : ℝ) :
    ‖corrugatedSeedBetaVelocity N t‖ ≤ 5 := by
  have hNp : 0 < N := by linarith
  have h := norm_add_le (corrugatedSeedBetaVelocity N t - corrugatedSeedLimitingVelocity N t)
    (corrugatedSeedLimitingVelocity N t)
  rw [sub_add_cancel] at h
  have hl : ‖corrugatedSeedLimitingVelocity N t‖ ≤ 4 := by
    simpa only [corrugatedSeedLimitingVelocity, norm_mul,
      Complex.norm_exp_ofReal_mul_I, one_mul] using corrugatedSeedLimitingFactor_norm_le (N * t)
  have he : 11 / N ≤ 1 := (div_le_one hNp).mpr hN
  exact (h.trans (add_le_add (corrugatedSeedBetaVelocity_error hNp t) hl)).trans (by linarith)

theorem corrugatedSeedDelta_cell_motion {N : ℝ} (hN : 10000 ≤ N) (k : ℝ) {t : ℝ}
    (ht : t ∈ Icc 0 (corrugatedSeedCell N)) :
    ‖corrugatedSeedDelta k N t - corrugatedSeedDelta k N 0‖ ≤ 5 * corrugatedSeedCell N := by
  have hNp : 0 < N := by linarith
  have hm := (corrugatedSeedMultiplier_contDiff k N).continuous
  have hv := (corrugatedSeedDeltaVelocity_contDiff k N).continuous
  have he : corrugatedSeedDelta k N t - corrugatedSeedDelta k N 0 =
      ∫ s in 0..t, corrugatedSeedDeltaVelocity k N s := by
    simp only [corrugatedSeedDelta, rawPrimitive, intervalIntegral.integral_same, add_zero,
      add_sub_cancel_left]
  rw [he]
  calc
    _ ≤ ∫ s in 0..t, ‖corrugatedSeedDeltaVelocity k N s‖ :=
      intervalIntegral.norm_integral_le_integral_norm ht.1
    _ ≤ ∫ s in 0..t, corrugatedSeedMultiplier k N s * 5 := by
      apply intervalIntegral.integral_mono_on ht.1 (hv.norm.intervalIntegrable _ _)
        ((hm.mul continuous_const).intervalIntegrable _ _)
      intro s _
      change ‖(corrugatedSeedMultiplier k N s : ℂ) * corrugatedSeedBetaVelocity N s‖ ≤ _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (corrugatedSeedMultiplier_pos k N s)]
      exact mul_le_mul_of_nonneg_left
        (corrugatedSeedBetaVelocity_norm_le (by linarith) s)
        (corrugatedSeedMultiplier_pos k N s).le
    _ = 5 * ∫ s in 0..t, corrugatedSeedMultiplier k N s := by
      rw [intervalIntegral.integral_mul_const]
      ring
    _ ≤ 5 * ∫ s in 0..corrugatedSeedCell N, corrugatedSeedMultiplier k N s := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (Filter.Eventually.of_forall (fun s => (corrugatedSeedMultiplier_pos k N s).le))
        (hm.intervalIntegrable _ _)
    _ = 5 * corrugatedSeedCell N := by rw [corrugatedSeedMultiplier_cell_integral (ne_of_gt hNp)]

theorem corrugatedSeedDelta_cell_error {N : ℝ} (hN : 10000 ≤ N) (k : ℝ)
    (hk : corrugatedRootIntegral (1 / N) k = 0) {t : ℝ}
    (ht : t ∈ Icc 0 (corrugatedSeedCell N)) :
    ‖corrugatedSeedDelta k N t - Complex.I / 2 * Complex.exp ((t : ℂ) * Complex.I)‖ ≤ 100 / N := by
  have hNp : 0 < N := by linarith
  have hlim : ‖Complex.I / 2 - Complex.I / 2 * Complex.exp ((t : ℂ) * Complex.I)‖ ≤
      corrugatedSeedCell N / 2 := by
    have he : Complex.I / 2 - Complex.I / 2 * Complex.exp ((t : ℂ) * Complex.I) =
        -(Complex.I / 2) * (Complex.exp ((t : ℂ) * Complex.I) - 1) := by ring
    rw [he, norm_mul, norm_neg]
    have hx := corrugated_unit_exponential_lipschitz 0 t
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, sub_zero, abs_of_nonneg ht.1] at hx
    have hhalf : ‖Complex.I / 2‖ = (1 / 2 : ℝ) := by norm_num
    rw [hhalf]
    exact (mul_le_mul_of_nonneg_left (hx.trans ht.2) (by norm_num)).trans_eq (by ring)
  have he : corrugatedSeedDelta k N t - Complex.I / 2 * Complex.exp ((t : ℂ) * Complex.I) =
      (corrugatedSeedDelta k N t - corrugatedSeedDelta k N 0) +
      (corrugatedSeedDelta k N 0 - Complex.I / 2) +
      (Complex.I / 2 - Complex.I / 2 * Complex.exp ((t : ℂ) * Complex.I)) := by ring
  rw [he]
  calc
    _ ≤ ‖corrugatedSeedDelta k N t - corrugatedSeedDelta k N 0‖ +
      ‖corrugatedSeedDelta k N 0 - Complex.I / 2‖ +
      ‖Complex.I / 2 - Complex.I / 2 * Complex.exp ((t : ℂ) * Complex.I)‖ := norm_add₃_le
    _ ≤ 5 * corrugatedSeedCell N + 53 / N + corrugatedSeedCell N / 2 :=
      add_le_add (add_le_add (corrugatedSeedDelta_cell_motion hN k ht)
        (corrugatedSeedDelta_initial_bound hN k hk)) hlim
    _ ≤ 100 / N := by
      unfold corrugatedSeedCell
      apply (le_div_iff₀ hNp).mpr
      have he : (5 * (2 * Real.pi / N) + 53 / N + (2 * Real.pi / N) / 2) * N =
          11 * Real.pi + 53 := by field_simp; ring
      rw [he]
      linarith [Real.pi_lt_four]

end
end TightVer401
