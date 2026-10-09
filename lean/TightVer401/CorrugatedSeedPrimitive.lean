import TightVer401.CorrugatedSeedCurve

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff

def corrugatedSeedDeltaVelocity (k N t : ℝ) : ℂ :=
  (corrugatedSeedMultiplier k N t : ℂ) * corrugatedSeedBetaVelocity N t

def corrugatedSeedCellMoment (k N : ℝ) : ℂ :=
  ∫ t in 0..corrugatedSeedCell N, corrugatedSeedDeltaVelocity k N t

def corrugatedSeedDelta (k N t : ℝ) : ℂ :=
  corrugatedSeedCellMoment k N / (corrugatedSeedRotation N - 1) +
    rawPrimitive (corrugatedSeedDeltaVelocity k N) t

theorem corrugatedSeedDeltaVelocity_contDiff (k N : ℝ) :
    ContDiff ℝ ∞ (corrugatedSeedDeltaVelocity k N) := by
  exact (Complex.ofRealCLM.contDiff.comp (corrugatedSeedMultiplier_contDiff k N)).mul
    (corrugatedSeedBetaVelocity_contDiff N)

theorem corrugatedSeedDelta_contDiff (k N : ℝ) :
    ContDiff ℝ ∞ (corrugatedSeedDelta k N) :=
  contDiff_const.add (rawPrimitive_contDiff (corrugatedSeedDeltaVelocity_contDiff k N))

theorem corrugatedSeedDelta_hasDerivAt (k N t : ℝ) :
    HasDerivAt (corrugatedSeedDelta k N) (corrugatedSeedDeltaVelocity k N t) t :=
  (rawPrimitive_hasDerivAt (corrugatedSeedDeltaVelocity_contDiff k N).continuous t).const_add _

theorem corrugatedSeedDelta_deriv (k N t : ℝ) :
    deriv (corrugatedSeedDelta k N) t = corrugatedSeedDeltaVelocity k N t :=
  (corrugatedSeedDelta_hasDerivAt k N t).deriv

theorem corrugatedSeedDelta_deriv_eq {N : ℝ} (hN : N ≠ 0) (k t : ℝ) :
    deriv (corrugatedSeedDelta k N) t =
      corrugatedSeedMultiplier k N t • deriv (corrugatedSeedBeta N) t := by
  rw [corrugatedSeedDelta_deriv, corrugatedSeedBeta_deriv hN]
  rfl

theorem corrugatedSeedDeltaVelocity_ne_zero {N : ℝ} (hN : 1 < N) (k t : ℝ) :
    corrugatedSeedDeltaVelocity k N t ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (corrugatedSeedMultiplier_pos k N t)))
    (corrugatedSeedBetaVelocity_ne_zero hN t)

theorem corrugatedSeedDeltaVelocity_cell {N : ℝ} (hN : N ≠ 0) (k t : ℝ) :
    corrugatedSeedDeltaVelocity k N (t + corrugatedSeedCell N) =
      corrugatedSeedRotation N * corrugatedSeedDeltaVelocity k N t := by
  rw [corrugatedSeedDeltaVelocity, corrugatedSeedBetaVelocity_cell hN,
    show corrugatedSeedMultiplier k N (t + corrugatedSeedCell N) =
      corrugatedSeedMultiplier k N t from corrugatedSeedMultiplier_periodic k hN t]
  unfold corrugatedSeedDeltaVelocity
  ring

theorem corrugated_covariant_rawPrimitive {f : ℝ → ℂ} {T : ℝ} {ξ : ℂ}
    (hf : Continuous f) (hcov : ∀ t, f (t + T) = ξ * f t) (t : ℝ) :
    rawPrimitive f (t + T) = rawPrimitive f T + ξ * rawPrimitive f t := by
  unfold rawPrimitive
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable 0 T) (hf.intervalIntegrable T (t + T))]
  have he : (∫ s in T..t + T, f s) = ξ * ∫ s in 0..t, f s := by
    rw [← show (∫ s in 0..t, f (s + T)) = ∫ s in T..t + T, f s by
      simpa only [zero_add] using intervalIntegral.integral_comp_add_right (a := 0) (b := t) f T]
    simp_rw [hcov]
    exact intervalIntegral.integral_const_mul ξ f
  rw [he]

theorem corrugatedSeedRotation_ne_one {N : ℝ} (hN : 1 < N) :
    corrugatedSeedRotation N ≠ 1 := by
  have hT : 0 < corrugatedSeedCell N := by unfold corrugatedSeedCell; positivity
  have hTlt : corrugatedSeedCell N < 2 * Real.pi := by
    unfold corrugatedSeedCell
    exact (div_lt_iff₀ (by linarith)).mpr (by nlinarith [Real.pi_pos])
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff_of_im_nonneg
    (x := (corrugatedSeedCell N : ℂ) * Complex.I)
    (by simpa using hT.le) |>.mp h
  have he : corrugatedSeedCell N = (n : ℝ) * (2 * Real.pi) := by
    simpa using congrArg Complex.im hn
  have hn0 : n ≠ 0 := by intro hz; simp [hz] at he; linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn0)
  nlinarith [Real.pi_pos]

theorem corrugatedSeedDelta_cell {N : ℝ} (hN : 1 < N) (k t : ℝ) :
    corrugatedSeedDelta k N (t + corrugatedSeedCell N) =
      corrugatedSeedRotation N * corrugatedSeedDelta k N t := by
  have hNz : N ≠ 0 := ne_of_gt (by linarith)
  have hξ : corrugatedSeedRotation N - 1 ≠ 0 := sub_ne_zero.mpr
    (corrugatedSeedRotation_ne_one hN)
  have he := corrugated_covariant_rawPrimitive
    (corrugatedSeedDeltaVelocity_contDiff k N).continuous
    (corrugatedSeedDeltaVelocity_cell hNz k) t
  unfold corrugatedSeedDelta
  rw [he]
  change corrugatedSeedCellMoment k N / (corrugatedSeedRotation N - 1) +
    (corrugatedSeedCellMoment k N + corrugatedSeedRotation N *
      rawPrimitive (corrugatedSeedDeltaVelocity k N) t) = _
  field_simp
  ring

end
end TightVer401
