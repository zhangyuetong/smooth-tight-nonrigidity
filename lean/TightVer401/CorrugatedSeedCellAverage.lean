import TightVer401.CorrugatedSeedAverage

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.ClosedSurfaceR4.PeriodicPrimitive

def corrugatedSeedCellFactor (N x : ℝ) : ℂ :=
  Complex.exp ((((1 / N) * (x + 2 * Real.sin x) : ℝ) : ℂ) * Complex.I) *
    ((Real.cos x : ℂ) + Complex.I * ((1 + (1 / N) * Real.sin x : ℝ) : ℂ) *
      ((1 + 2 * Real.cos x : ℝ) : ℂ))

def corrugatedSeedCellQuotient (N : ℝ) : ℂ :=
  (corrugatedSeedCell N : ℂ) / (corrugatedSeedRotation N - 1)

theorem corrugatedSeedMultiplier_density (k N t : ℝ) :
    corrugatedSeedMultiplier k N t = (2 * Real.pi) * corrugatedSeedDensity k (N * t) := by
  rw [corrugatedSeedMultiplier, corrugatedSeedNormalization_eq]
  unfold corrugatedSeedDensity
  field_simp

theorem corrugatedSeedBetaVelocity_cellFactor {N : ℝ} (hN : N ≠ 0) (t : ℝ) :
    corrugatedSeedBetaVelocity N t = corrugatedSeedCellFactor N (N * t) := by
  have he : corrugatedSeedPhase N t = (1 / N) * (N * t + 2 * Real.sin (N * t)) := by
    unfold corrugatedSeedPhase
    field_simp
  simp only [corrugatedSeedBetaVelocity, corrugatedSeedCellFactor, corrugatedSeedRadius, he,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_ofNat]

theorem corrugatedSeedCellFactor_continuous (N : ℝ) : Continuous (corrugatedSeedCellFactor N) := by
  unfold corrugatedSeedCellFactor
  fun_prop

theorem corrugatedSeedCellMoment_average {N : ℝ} (hN : N ≠ 0) (k : ℝ) :
    corrugatedSeedCellMoment k N = (corrugatedSeedCell N : ℂ) *
      corrugatedSeedAverage k (corrugatedSeedCellFactor N) := by
  have he (t : ℝ) : corrugatedSeedDeltaVelocity k N t =
      (2 * Real.pi : ℂ) * (corrugatedSeedDensity k (N * t) • corrugatedSeedCellFactor N (N * t)) := by
    rw [corrugatedSeedDeltaVelocity, corrugatedSeedMultiplier_density,
      corrugatedSeedBetaVelocity_cellFactor hN]
    simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.real_smul]
    ring
  unfold corrugatedSeedCellMoment
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_mul_left
    (fun x => corrugatedSeedDensity k x • corrugatedSeedCellFactor N x) hN]
  have hT : N * corrugatedSeedCell N = 2 * Real.pi := by
    unfold corrugatedSeedCell
    field_simp
  simp only [mul_zero, hT]
  change (2 * Real.pi : ℂ) * (N⁻¹ • corrugatedSeedAverage k (corrugatedSeedCellFactor N)) = _
  simp only [Complex.real_smul, corrugatedSeedCell, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_inv]
  ring

theorem corrugatedSeedDelta_initial_average {N : ℝ} (hN : N ≠ 0) (k : ℝ) :
    corrugatedSeedDelta k N 0 = corrugatedSeedCellQuotient N *
      corrugatedSeedAverage k (corrugatedSeedCellFactor N) := by
  simp only [corrugatedSeedDelta, rawPrimitive, intervalIntegral.integral_same, add_zero]
  rw [corrugatedSeedCellMoment_average hN]
  unfold corrugatedSeedCellQuotient
  ring

theorem corrugatedSeedMultiplier_cell_integral {N : ℝ} (hN : N ≠ 0) (k : ℝ) :
    (∫ t in 0..corrugatedSeedCell N, corrugatedSeedMultiplier k N t) = corrugatedSeedCell N := by
  simp_rw [corrugatedSeedMultiplier_density]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (corrugatedSeedDensity k) hN]
  have hT : N * corrugatedSeedCell N = 2 * Real.pi := by
    unfold corrugatedSeedCell
    field_simp
  change (2 * Real.pi) * (N⁻¹ • ∫ x in N * 0..N * corrugatedSeedCell N,
    corrugatedSeedDensity k x) = corrugatedSeedCell N
  rw [mul_zero, hT, corrugatedSeedDensity_integral]
  simp only [smul_eq_mul, mul_one, corrugatedSeedCell]
  ring

end
end TightVer401
