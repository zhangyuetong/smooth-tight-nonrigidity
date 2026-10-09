import TightVer401.CorrugatedRootSmooth

namespace TightVer401
noncomputable section
open Set MeasureTheory
open scoped ContDiff

def corrugatedSeedNormalization (k : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ x in 0..(2 * Real.pi), Real.exp (-k * Real.cos x)

def corrugatedSeedMultiplier (k N t : ℝ) : ℝ :=
  (corrugatedSeedNormalization k)⁻¹ * Real.exp (-k * Real.cos (N * t))

theorem corrugatedSeedNormalization_eq (k : ℝ) :
    corrugatedSeedNormalization k = (2 * Real.pi)⁻¹ * corrugatedCosMoment 0 0 k := by
  simp [corrugatedSeedNormalization, corrugatedCosMoment, corrugatedWeight]

theorem corrugatedSeedNormalization_pos (k : ℝ) : 0 < corrugatedSeedNormalization k := by
  rw [corrugatedSeedNormalization_eq]
  exact mul_pos (inv_pos.mpr (by positivity))
    (corrugatedCosMoment_zero_pos (ε := 0) (by norm_num) k)

theorem corrugatedSeedNormalization_contDiff : ContDiff ℝ ∞ corrugatedSeedNormalization := by
  have he : corrugatedSeedNormalization =
      (fun k => (2 * Real.pi)⁻¹ * corrugatedCosMoment 0 0 k) := funext corrugatedSeedNormalization_eq
  rw [he]
  exact contDiff_const.mul (corrugatedCosMoment_contDiff 0 0)

theorem corrugatedSeedMultiplier_pos (k N t : ℝ) : 0 < corrugatedSeedMultiplier k N t :=
  mul_pos (inv_pos.mpr (corrugatedSeedNormalization_pos k)) (Real.exp_pos _)

theorem corrugatedSeedMultiplier_contDiff (k N : ℝ) :
    ContDiff ℝ ∞ (corrugatedSeedMultiplier k N) := by
  unfold corrugatedSeedMultiplier
  fun_prop

theorem corrugatedSeedMultiplier_periodic (k : ℝ) {N : ℝ} (hN : N ≠ 0) :
    Function.Periodic (corrugatedSeedMultiplier k N) (2 * Real.pi / N) := by
  intro t
  have he : N * (t + 2 * Real.pi / N) = N * t + 2 * Real.pi := by
    field_simp
  simp only [corrugatedSeedMultiplier, he, Real.cos_add_two_pi]

end
end TightVer401
